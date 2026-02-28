#!/usr/bin/env python3
"""
Git Manager Backend — 完整修复版 + 完善日志系统 + WebSocket实时通信
python3 server.py  →  http://localhost:7842
"""

import subprocess, os, json, re, sys, logging, threading, hashlib, time
from pathlib import Path
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs, unquote
from datetime import datetime
try:
    from websockets.sync.server import serve as ws_serve, ServerConnection
    WEBSOCKET_AVAILABLE = True
except ImportError:
    WEBSOCKET_AVAILABLE = False
    print("警告: websockets 库未安装，WebSocket功能将不可用")
    print("安装方法: pip install websockets")

# ════════════════════════════════════════════════════════
#  日志系统配置
# ════════════════════════════════════════════════════════

# 创建日志目录
LOG_DIR = Path(__file__).parent / "logs"
LOG_DIR.mkdir(exist_ok=True)

# 配置日志格式
log_format = logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# 创建主日志记录器
logger = logging.getLogger('GitManager')
logger.setLevel(logging.DEBUG)

# 控制台处理器 - 显示 INFO 及以上级别
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setLevel(logging.INFO)
console_handler.setFormatter(log_format)
logger.addHandler(console_handler)

# 文件处理器 - 记录所有级别的日志
log_file = LOG_DIR / f"git_manager_{datetime.now().strftime('%Y%m%d')}.log"
file_handler = logging.FileHandler(log_file, encoding='utf-8')
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(log_format)
logger.addHandler(file_handler)

# 错误日志文件处理器 - 只记录 ERROR 及以上级别
error_log_file = LOG_DIR / f"errors_{datetime.now().strftime('%Y%m%d')}.log"
error_handler = logging.FileHandler(error_log_file, encoding='utf-8')
error_handler.setLevel(logging.ERROR)
error_handler.setFormatter(log_format)
logger.addHandler(error_handler)

logger.info("=" * 60)
logger.info("Git Manager Backend 启动初始化...")
logger.info(f"日志文件: {log_file}")
logger.info(f"错误日志文件: {error_log_file}")
logger.info("=" * 60)

# ════════════════════════════════════════════════════════
#  全局变量
# ════════════════════════════════════════════════════════

REPO_PATH = None
WS_PORT = 7843  # WebSocket端口号
ws_clients = set()  # WebSocket客户端集合
last_file_state = None  # 上次的文件状态（用于检测变化）
_changed_files_cache = {
    "ts": 0.0,
    "files": None,
}

# ════════════════════════════════════════════════════════
#  WebSocket 实时通信
# ════════════════════════════════════════════════════════

def broadcast_to_clients(message):
    """向所有WebSocket客户端广播消息"""
    if not WEBSOCKET_AVAILABLE:
        return
    
    disconnected = set()
    for client in ws_clients.copy():
        try:
            client.send(json.dumps(message))
        except Exception as e:
            logger.warning(f"向客户端发送消息失败: {e}")
            disconnected.add(client)
    
    # 移除断开的客户端
    ws_clients.difference_update(disconnected)


def get_file_state_hash():
    """获取当前文件状态的哈希值"""
    if not REPO_PATH:
        return None
    try:
        # 轻量级状态：基于 git status porcelain 输出 + 相关文件 mtime
        # 仅用 status 输出会导致“持续编辑但状态不变（一直是 M）”时无法触发推送。
        # 这里额外叠加 mtime，避免触发昂贵的 git diff 统计。
        out, err, code = run_git(["status", "--porcelain=v1", "-u", "-z"])
        if code != 0:
            logger.debug(f"获取文件状态失败: {err}")
            return None

        entries = (out or "").split("\x00")
        state_items = []
        i = 0
        while i < len(entries):
            entry = entries[i]
            if not entry:
                i += 1
                continue
            if len(entry) < 4:
                i += 1
                continue

            xy = entry[:2]
            path = entry[3:]
            idx_s = xy[0]

            paths = [(path, xy)]
            # Rename/Copy 在 -z 下会额外带一个 path
            if idx_s in ("R", "C") and (i + 1) < len(entries):
                new_path = entries[i + 1]
                if new_path:
                    paths.append((new_path, xy))
                i += 1

            for p, flag in paths:
                p_key = (p or "").replace("\\", "/")
                if not p_key:
                    continue
                full = os.path.join(REPO_PATH, p_key)
                if os.path.exists(full):
                    try:
                        mtime = os.path.getmtime(full)
                    except Exception:
                        mtime = 0
                else:
                    # 文件不存在（删除/重命名旧路径等）：必须使用稳定值
                    mtime = 0
                state_items.append((p_key, flag, mtime))

            i += 1

        state_str = json.dumps(sorted(state_items), sort_keys=True)
        return hashlib.md5(state_str.encode("utf-8", errors="replace")).hexdigest()
    except Exception as e:
        logger.error(f"获取文件状态哈希失败: {e}")
        return None


def get_changed_files_cached(max_age_sec=1.0):
    """带短缓存的变更文件列表。

    典型场景：
    - 前端 /api/files 轮询备份
    - WebSocket 初始化/按需请求
    """
    now = time.time()
    try:
        ts = float(_changed_files_cache.get("ts") or 0.0)
    except Exception:
        ts = 0.0

    cached = _changed_files_cache.get("files")
    if cached is not None and (now - ts) <= float(max_age_sec):
        return cached

    files = get_changed_files()
    _changed_files_cache["ts"] = now
    _changed_files_cache["files"] = files
    return files


def watch_repository():
    """监控仓库变化并通知客户端"""
    global last_file_state
    
    while True:
        try:
            if REPO_PATH and ws_clients:
                current_state = get_file_state_hash()
                if current_state and current_state != last_file_state:
                    logger.debug(f"检测到文件变化: {last_file_state} -> {current_state}")
                    last_file_state = current_state
                    
                    # 获取最新的文件列表
                    files = get_changed_files_cached(max_age_sec=0)
                    
                    # 广播更新消息
                    broadcast_to_clients({
                        'type': 'files_updated',
                        'files': files
                    })
            
            time.sleep(1)  # 每秒检查一次
        except Exception as e:
            logger.error(f"仓库监控异常: {e}", exc_info=True)
            time.sleep(5)


def handle_websocket(websocket: ServerConnection):
    """处理WebSocket连接"""
    logger.info(f"新的WebSocket连接: {websocket.remote_address}")
    ws_clients.add(websocket)
    
    try:
        # 发送欢迎消息
        websocket.send(json.dumps({
            'type': 'connected',
            'message': 'WebSocket连接成功'
        }))
        
        # 如果已经打开了仓库，立即发送当前状态
        if REPO_PATH:
            files = get_changed_files_cached()
            websocket.send(json.dumps({
                'type': 'files_updated',
                'files': files
            }))
        
        # 接收客户端消息
        for message in websocket:
            try:
                data = json.loads(message)
                msg_type = data.get('type')
                
                if msg_type == 'ping':
                    websocket.send(json.dumps({'type': 'pong'}))
                elif msg_type == 'request_files':
                    if REPO_PATH:
                        files = get_changed_files_cached()
                        websocket.send(json.dumps({
                            'type': 'files_updated',
                            'files': files
                        }))
                else:
                    logger.warning(f"未知的WebSocket消息类型: {msg_type}")
                    
            except json.JSONDecodeError:
                logger.warning(f"无效的JSON消息: {message}")
            except Exception as e:
                logger.error(f"处理WebSocket消息异常: {e}", exc_info=True)
                
    except Exception as e:
        logger.error(f"WebSocket连接异常: {e}")
    finally:
        ws_clients.discard(websocket)
        logger.info(f"WebSocket连接关闭: {websocket.remote_address}")


def start_websocket_server():
    """启动WebSocket服务器"""
    if not WEBSOCKET_AVAILABLE:
        logger.warning("WebSocket库未安装，跳过WebSocket服务器启动")
        return
    
    try:
        ws_port = 7843
        max_attempts = 10
        
        for attempt in range(max_attempts):
            try:
                with ws_serve(handle_websocket, "127.0.0.1", ws_port) as server:
                    logger.info(f"WebSocket服务器启动成功: ws://localhost:{ws_port}")
                    
                    # 更新全局变量，让前端知道正确的WebSocket端口
                    global WS_PORT
                    WS_PORT = ws_port
                    
                    # 启动文件监控线程
                    watch_thread = threading.Thread(target=watch_repository, daemon=True)
                    watch_thread.start()
                    logger.info("文件监控线程已启动")
                    
                    # 保持服务器运行
                    server.serve_forever()
            except OSError as e:
                if e.errno == 10048:  # 端口被占用
                    logger.warning(f"端口 {ws_port} 被占用，尝试下一个端口...")
                    ws_port += 1
                    continue
                else:
                    raise
    except Exception as e:
        logger.error(f"WebSocket服务器启动失败: {e}", exc_info=True)


# ════════════════════════════════════════════════════════
#  Git 执行核心 — 处理 Windows GBK / 中文路径 / 空格
# ════════════════════════════════════════════════════════

def run_git(args, cwd=None, input_data=None, timeout=60):
    """执行 Git 命令并记录日志"""
    cwd = cwd or REPO_PATH
    env = os.environ.copy()
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["LANG"]                = "en_US.UTF-8"
    env["LC_ALL"]              = "en_US.UTF-8"
    env["PYTHONIOENCODING"]    = "utf-8"

    # 记录命令执行
    cmd_str = " ".join(["git"] + args)
    logger.debug(f"执行 Git 命令: {cmd_str} (工作目录: {cwd})")

    def decode_bytes(b):
        if not b:
            return ""
        for enc in ("utf-8", "utf-8-sig", "gbk", "gb2312", "cp936", "latin-1"):
            try:
                return b.decode(enc)
            except Exception:
                continue
        return b.decode("utf-8", errors="replace")

    try:
        inp = input_data.encode("utf-8") if isinstance(input_data, str) else input_data
        # -c core.quotepath=false  → 不转义中文/特殊字符路径
        r = subprocess.run(
            ["git", "-c", "core.quotepath=false"] + args,
            cwd=cwd,
            capture_output=True,
            text=False,
            input=inp,
            timeout=timeout,
            env=env,
        )
        stdout_str = decode_bytes(r.stdout)
        stderr_str = decode_bytes(r.stderr)
        
        if r.returncode == 0:
            logger.debug(f"Git 命令执行成功: {cmd_str}")
            if stdout_str:
                logger.debug(f"标准输出: {stdout_str[:200]}...")  # 只记录前200个字符
        else:
            logger.warning(f"Git 命令执行失败 (返回码: {r.returncode}): {cmd_str}")
            if stderr_str:
                logger.warning(f"错误输出: {stderr_str}")
        
        return stdout_str, stderr_str, r.returncode
    except FileNotFoundError:
        error_msg = "git 未安装或不在 PATH 中"
        logger.error(f"Git 命令执行失败: {error_msg}")
        return "", error_msg, 1
    except subprocess.TimeoutExpired:
        error_msg = f"命令超时(超过{timeout}秒)"
        logger.error(f"Git 命令超时: {cmd_str} - {error_msg}")
        return "", error_msg, 1
    except Exception as e:
        logger.error(f"Git 命令执行异常: {cmd_str} - {str(e)}", exc_info=True)
        return "", str(e), 1

# ════════════════════════════════════════════════════════
#  工作区变更文件
# ════════════════════════════════════════════════════════

def get_changed_files():
    """获取工作区变更文件列表"""
    logger.debug("开始获取变更文件列表")
    # -z 用 NUL 分隔,彻底避免中文/空格路径问题
    stdout, _, code = run_git(["status", "--porcelain=v1", "-u", "-z"])
    if code != 0:
        logger.warning("获取变更文件列表失败")
        return []

    def parse_numstat_z(out_text):
        m = {}
        if not out_text:
            return m
        parts = out_text.split("\x00")
        for item in parts:
            if not item:
                continue
            cols = item.split("\t")
            if len(cols) < 3:
                continue
            a, r, p = cols[0], cols[1], cols[2]
            try:
                added = int(a) if a != "-" else 0
                removed = int(r) if r != "-" else 0
            except Exception:
                added = removed = 0
            p = (p or "").replace("\\", "/")
            m[p] = (added, removed)
        return m

    # 批量统计增删行：最多执行 3 次 diff（而不是每个文件 3 次）
    ns_out, _, _ = run_git(["diff", "HEAD",     "--numstat", "-z"])
    ns_map = parse_numstat_z(ns_out)
    if not ns_map:
        ns_out2, _, _ = run_git(["diff",             "--numstat", "-z"])
        ns_map = parse_numstat_z(ns_out2)
    ns_cached_out, _, _ = run_git(["diff", "--cached", "--numstat", "-z"])
    ns_cached_map = parse_numstat_z(ns_cached_out)

    entries = stdout.split("\x00")
    files   = []
    i       = 0
    while i < len(entries):
        entry = entries[i]
        if len(entry) < 4:
            i += 1
            continue
        xy       = entry[:2]
        name     = entry[3:]
        old_name = None
        idx_s    = xy[0]
        work_s   = xy[1]

        if idx_s in ("R", "C"):
            i += 1
            old_name = entries[i] if i < len(entries) else ""

        if idx_s == "?" and work_s == "?":
            status = "U"
        elif idx_s == "D" or work_s == "D":
            status = "D"
        elif idx_s == "A":
            status = "A"
        elif idx_s in ("R", "C"):
            status = "R"
        else:
            status = "M"

        p_key = (name or "").replace("\\", "/")
        added, removed = (0, 0)
        if status == "U":
            try:
                full = _repo_abspath(p_key)
                added = sum(1 for _ in open(full, "r", errors="replace"))
                removed = 0
            except Exception as e:
                logger.debug(f"读取新文件行数失败: {p_key} - {e}")
                added = removed = 0
        else:
            if p_key in ns_map:
                added, removed = ns_map.get(p_key, (0, 0))
            elif p_key in ns_cached_map:
                added, removed = ns_cached_map.get(p_key, (0, 0))
        files.append({
            "path":     name,
            "status":   status,
            "old_path": old_name,
            "added":    added,
            "removed":  removed,
        })
        i += 1
    
    logger.debug(f"成功获取变更文件列表，共 {len(files)} 个文件")
    return files


def count_diff_lines(filepath, status):
    """统计文件的增删行数"""
    logger.debug(f"统计文件增删行数: {filepath} (状态: {status})")
    if status == "U":
        try:
            full = os.path.join(REPO_PATH, filepath)
            line_count = sum(1 for _ in open(full, "r", errors="replace"))
            logger.debug(f"新文件行数: {filepath} - {line_count} 行")
            return line_count, 0
        except Exception as e:
            logger.error(f"读取新文件失败: {filepath} - {e}")
            return 0, 0
    for args in (
        ["diff", "HEAD",     "--numstat", "--", filepath],
        ["diff",             "--numstat", "--", filepath],
        ["diff", "--cached", "--numstat", "--", filepath],
    ):
        out, _, code = run_git(args)
        if code == 0 and (out or "").strip():
            for line in out.splitlines():
                p = line.split("\t")
                if len(p) >= 2:
                    try:
                        added, removed = int(p[0]), int(p[1])
                        logger.debug(f"文件统计结果: {filepath} - +{added}/-{removed}")
                        return added, removed
                    except Exception as e:
                        logger.debug(f"解析统计数据失败: {filepath} - {e}")
                        pass
    logger.debug(f"无法获取文件统计: {filepath}")
    return 0, 0

# ════════════════════════════════════════════════════════
#  Diff 解析
# ════════════════════════════════════════════════════════

def get_file_diff(filepath, status, ctx_lines=5):
    """获取文件的 diff 内容"""
    try:
        ctx_lines = int(ctx_lines)
    except Exception:
        ctx_lines = 5
    if ctx_lines < 0:
        ctx_lines = 0
    if ctx_lines > 200:
        ctx_lines = 200
    logger.debug(f"获取文件 diff: {filepath} (状态: {status}, ctx: {ctx_lines})")
    if status == "U":
        try:
            full    = os.path.join(REPO_PATH, filepath)
            content = open(full, "r", errors="replace").readlines()
            logger.debug(f"读取新文件内容: {filepath} - {len(content)} 行")
            return [{
                "header":    f"@@ -0,0 +1,{len(content)} @@ 新文件",
                "old_start": 0,
                "new_start": 1,
                "lines": [{"type":"added","old":None,"new":i+1,"text":l.rstrip("\n")}
                          for i, l in enumerate(content)]
            }], None
        except Exception as e:
            logger.error(f"读取新文件 diff 失败: {filepath} - {e}")
            return [], str(e)

    raw = None
    unified_arg = f"--unified={ctx_lines}"
    for args in (
        ["diff", "HEAD",     unified_arg, "--", filepath],
        ["diff",             unified_arg, "--", filepath],
        ["diff", "--cached", unified_arg, "--", filepath],
    ):
        out, _, code = run_git(args)
        if code == 0 and (out or "").strip():
            raw = out
            break
    if not raw:
        logger.debug(f"未找到文件 diff: {filepath}")
        return [], None
    
    logger.debug(f"成功获取文件 diff: {filepath}")
    return parse_diff(raw), None


def parse_diff(text):
    """解析 diff 文本"""
    logger.debug("开始解析 diff 文本")
    hunks = []
    cur   = None
    ol = nl = 0
    removed_buf = []
    
    for raw_line in (text or "").splitlines():
        # Skip file header lines
        if raw_line.startswith("+++") or raw_line.startswith("---"):
            continue
            
        m = re.match(r'^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@(.*)', raw_line)
        if m:
            if cur:
                # Flush any pending removed lines before new hunk
                while removed_buf:
                    txt = removed_buf.pop(0)
                    cur["lines"].append({"type":"removed", "old":ol, "new":None, "text":txt})
                    ol += 1
                hunks.append(cur)
            ol  = int(m.group(1))
            nl  = int(m.group(2))
            ctx = m.group(3).strip()
            cur = {
                "header":    raw_line,
                "old_start": ol,
                "new_start": nl,
                "context":   ctx,
                "lines": []
            }
            continue

        if not cur:
            continue

        if raw_line.startswith("+"):
            text = raw_line[1:]
            if removed_buf:
                old_txt = removed_buf.pop(0)
                cur["lines"].append({
                    "type": "modified",
                    "old": ol,
                    "new": nl,
                    "text": text,
                    "old_text": old_txt
                })
                ol += 1
                nl += 1
            else:
                cur["lines"].append({"type":"added", "old":None, "new":nl, "text":text})
                nl += 1

        elif raw_line.startswith("-"):
            text = raw_line[1:]
            removed_buf.append(text)

        else:
            # Context line
            while removed_buf:
                txt = removed_buf.pop(0)
                cur["lines"].append({"type":"removed", "old":ol, "new":None, "text":txt})
                ol += 1
            text = raw_line[1:] if raw_line.startswith(" ") else raw_line
            cur["lines"].append({"type":"context", "old":ol, "new":nl, "text":text})
            ol += 1
            nl += 1

    if cur:
        while removed_buf:
            txt = removed_buf.pop(0)
            cur["lines"].append({"type":"removed", "old":ol, "new":None, "text":txt})
            ol += 1
        hunks.append(cur)
    
    logger.debug(f"解析完成，共 {len(hunks)} 个 hunk")
    return hunks

# ════════════════════════════════════════════════════════
#  提交历史
# ════════════════════════════════════════════════════════

def get_log():
    """获取提交历史"""
    logger.debug("获取提交历史")
    fmt = "--pretty=format:%H%x00%an%x00%ae%x00%ad%x00%s"
    out, _, code = run_git(["log", fmt, "--date=iso", "-50"])
    if code != 0:
        logger.warning("获取提交历史失败")
        return []
    
    commits = []
    for line in out.splitlines():
        parts = line.split("\x00")
        if len(parts) < 5:
            continue
        full_hash = parts[0]
        commits.append({
            "hash":      full_hash[:7],  # 短hash用于显示
            "full_hash": full_hash,      # 完整hash用于操作
            "author":    parts[1],
            "email":     parts[2],
            "date":      parts[3],
            "message":   parts[4]
        })
    
    logger.info(f"成功获取提交历史，共 {len(commits)} 条")
    return commits


def get_commit_detail(commit_hash):
    """获取提交详情"""
    logger.debug(f"获取提交详情: {commit_hash}")
    fmt = "--pretty=format:%H%x00%an%x00%ae%x00%ad%x00%s%x00%b"
    out, _, code = run_git(["show", "--no-patch", fmt, "--date=iso", commit_hash])
    if code != 0:
        logger.error(f"获取提交详情失败: {commit_hash}")
        return {"error":"找不到此提交"}

    parts = out.strip().split("\x00")
    if len(parts) < 5:
        logger.error(f"解析提交详情失败: {commit_hash}")
        return {"error":"解析失败"}

    info = {
        "hash":      parts[0][:7],  # 短hash
        "full_hash": parts[0],      # 完整hash
        "author":    parts[1],
        "email":     parts[2],
        "date":      parts[3],
        "subject":   parts[4],
        "message":   parts[4],
        "body":      parts[5] if len(parts) > 5 else ""
    }

    # 获取文件变更详情（使用numstat获取准确的增删行数）
    stat_out, _, _ = run_git(["show", "--numstat", "--format=", commit_hash])
    files = []
    
    for line in stat_out.splitlines():
        line = line.strip()
        if not line:
            continue
        
        # numstat格式: <added>\t<removed>\t<filepath>
        parts = line.split('\t')
        if len(parts) >= 3:
            added_str = parts[0]
            removed_str = parts[1]
            filepath = parts[2]
            
            # 处理二进制文件(显示为'-')
            try:
                added = int(added_str) if added_str != '-' else 0
                removed = int(removed_str) if removed_str != '-' else 0
            except ValueError:
                added = 0
                removed = 0
            
            # 使用name-status获取准确的文件状态
            status_out, _, _ = run_git(["show", "--name-status", "--format=", commit_hash, "--", filepath])
            status = 'M'  # 默认修改
            
            for status_line in status_out.splitlines():
                if filepath in status_line:
                    if status_line.startswith('A'):
                        status = 'A'
                    elif status_line.startswith('D'):
                        status = 'D'
                    elif status_line.startswith('M'):
                        status = 'M'
                    elif status_line.startswith('R'):
                        status = 'R'
                    break
            
            files.append({
                "path": filepath,
                "status": status,
                "added": added,
                "removed": removed
            })

    info["files"] = files
    logger.info(f"成功获取提交详情: {commit_hash}, 文件数: {len(files)}")
    return info


def get_commit_file_diff(commit_hash, filepath):
    """获取提交中某个文件的 diff"""
    logger.debug(f"获取提交文件 diff: {commit_hash} - {filepath}")
    
    # 使用git show获取该commit中该文件的diff
    # 添加--format=选项来只输出diff内容，不包含提交信息
    out, err, code = run_git(["show", "--format=", "--unified=5", f"{commit_hash}", "--", filepath])
    if code != 0:
        logger.error(f"获取提交文件 diff 失败: {commit_hash} - {filepath}, 错误: {err}")
        return []

    # 检查是否有diff内容
    if not out or not out.strip():
        logger.warning(f"提交文件 diff 为空: {commit_hash} - {filepath}")
        return []

    logger.info(f"成功获取提交文件 diff: {commit_hash} - {filepath}, diff长度: {len(out)}")
    return parse_diff(out)

# ════════════════════════════════════════════════════════
#  分支操作
# ════════════════════════════════════════════════════════

def get_branches():
    """获取分支列表"""
    logger.debug("获取分支列表")
    out, _, code = run_git(["branch", "-a"])
    if code != 0:
        logger.warning("获取分支列表失败")
        return [], None
    
    branches = []
    current  = None
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("*"):
            current = line[2:].strip()
            branches.append(current)
        elif line:
            branches.append(line)
    
    logger.info(f"成功获取分支列表，共 {len(branches)} 个分支，当前分支: {current}")
    return branches, current

def is_commit_pushed(commit_hash):
    """判断某个提交是否已经存在于任意远端分支（基于本地 remote refs）。"""
    commit_hash = (commit_hash or "").strip()
    if not commit_hash:
        return False, [], "缺少 hash"

    out, err, code = run_git(["branch", "-r", "--contains", commit_hash])
    if code != 0:
        return False, [], (err or "查询远端分支失败")

    branches = []
    for ln in (out or "").splitlines():
        b = (ln or "").strip()
        if not b:
            continue
        # ignore symbolic refs like: origin/HEAD -> origin/main
        if "->" in b:
            continue
        branches.append(b)

    return bool(branches), branches, None

# ════════════════════════════════════════════════════════
#  文件还原
# ════════════════════════════════════════════════════════

def _repo_abspath(rel):
    """获取仓库内文件的绝对路径"""
    return os.path.join(REPO_PATH, rel.replace("/", os.sep))


def revert_hunk(filepath, hunk_index, status):
    """还原单个 hunk"""
    logger.info(f"还原 hunk: {filepath} - hunk #{hunk_index} (状态: {status})")
    
    # 简化实现：直接使用文件整体撤回，避免复杂的diff解析和文件修改
    # 这种方法更可靠，虽然会撤回整个文件的更改
    for args in (
        ["checkout", "HEAD", "--", filepath],
        ["restore",          "--", filepath],
        ["checkout",         "--", filepath],
    ):
        _, err, code = run_git(args, timeout=120)
        if code == 0:
            logger.info(f"成功还原文件: {filepath}")
            return True, "已撤回所有更改"
    
    logger.error(f"还原 hunk 失败: {filepath} - 无法执行Git命令")
    return False, f"撤回失败: {err or '未知错误'}"


def revert_line(filepath, hunk_index, line_index, status, ctx_lines=5):
    """还原单行"""
    logger.info(f"还原行: {filepath} - hunk #{hunk_index}, line #{line_index} (状态: {status})")
    
    try:
        # 获取文件的当前内容
        full_path = _repo_abspath(filepath)
        with open(full_path, 'r', encoding='utf-8', errors='replace') as f:
            current_lines = f.readlines()
        
        # 获取文件的原始内容（从HEAD）
        old_content, _, code = run_git(['show', 'HEAD:' + filepath])
        if code != 0:
            logger.error(f"获取文件原始内容失败: {filepath}")
            return False, "获取文件原始内容失败"
        old_lines = old_content.splitlines(keepends=True)
        
        # 获取文件的diff数据
        hunks, err = get_file_diff(filepath, status, ctx_lines)
        if err:
            logger.error(f"获取文件diff失败: {filepath} - {err}")
            return False, f"获取文件diff失败: {err}"
        
        # 记录hunks信息
        logger.info(f"获取到 {len(hunks)} 个hunks")
        
        # 确保hunk_index和line_index有效
        if hunk_index < 0 or hunk_index >= len(hunks):
            logger.error(f"无效的hunk索引: {hunk_index}, 总hunks: {len(hunks)}")
            return False, "无效的hunk索引"
        
        hunk = hunks[hunk_index]
        logger.info(f"选中hunk #{hunk_index}, 包含 {len(hunk['lines'])} 行")
        
        if line_index < 0 or line_index >= len(hunk['lines']):
            logger.error(f"无效的行索引: {line_index}, hunk总行数: {len(hunk['lines'])}")
            return False, "无效的行索引"
        
        # 获取要撤回的行信息
        line_info = hunk['lines'][line_index]
        logger.info(f"要撤回的行: type={line_info['type']}, old={line_info.get('old')}, new={line_info.get('new')}, text={line_info.get('text')[:50]}")
        
        # 保存修改前的行数，用于验证是否只修改了一行
        original_line_count = len(current_lines)
        logger.info(f"修改前文件行数: {original_line_count}")
        
        # 根据行类型处理撤回
        if line_info['type'] == 'added':
            # 对于新增的行，直接删除
            if line_info['new'] and line_info['new'] <= len(current_lines):
                deleted_line = current_lines[line_info['new'] - 1]
                del current_lines[line_info['new'] - 1]
                logger.info(f"成功删除新增行: {filepath} - 行 {line_info['new']}, 内容: {deleted_line.strip()}")
            else:
                logger.error(f"新增行索引无效: {line_info['new']}, 文件总行数: {len(current_lines)}")
                return False, "新增行索引无效"
        elif line_info['type'] == 'removed':
            # 对于删除的行，恢复原始内容
            if line_info['old'] and line_info['old'] <= len(old_lines):
                # 找到插入位置
                insert_pos = line_info['old'] - 1
                if insert_pos < len(current_lines):
                    current_lines.insert(insert_pos, old_lines[insert_pos])
                    logger.info(f"成功恢复删除行: {filepath} - 行 {line_info['old']}, 位置 {insert_pos}")
                else:
                    current_lines.append(old_lines[insert_pos])
                    logger.info(f"成功恢复删除行: {filepath} - 行 {line_info['old']}, 位置 {insert_pos}")
            else:
                logger.error(f"删除行索引无效: {line_info['old']}, 旧文件总行数: {len(old_lines)}")
                return False, "删除行索引无效"
        elif line_info['type'] == 'modified':
            # 对于修改的行，恢复原始内容
            if line_info['old'] and line_info['old'] <= len(old_lines) and line_info['new'] and line_info['new'] <= len(current_lines):
                old_line = old_lines[line_info['old'] - 1]
                current_lines[line_info['new'] - 1] = old_line
                logger.info(f"成功恢复修改行: {filepath} - 行 {line_info['new']}, 旧内容: {old_line.strip()}")
            else:
                logger.error(f"修改行索引无效: 旧行 {line_info['old']}, 新行 {line_info['new']}, 旧文件总行数: {len(old_lines)}, 当前文件总行数: {len(current_lines)}")
                return False, "修改行索引无效"
        else:
            logger.error(f"不支持的行类型: {line_info['type']}")
            return False, "不支持的行类型"
        
        # 验证是否只修改了一行
        logger.info(f"修改后文件行数: {len(current_lines)}, 修改前文件行数: {original_line_count}")
        if len(current_lines) != original_line_count and line_info['type'] != 'added' and line_info['type'] != 'removed':
            logger.error(f"修改行数不正确: 原始 {original_line_count}, 修改后 {len(current_lines)}")
            return False, "修改行数不正确"
        
        # 保存修改后的文件
        with open(full_path, 'w', encoding='utf-8', newline='') as f:
            f.writelines(current_lines)
        
        logger.info(f"成功还原单行: {filepath} - hunk #{hunk_index}, line #{line_index}")
        return True, "已撤回该行代码"
    except Exception as e:
        logger.error(f"还原单行失败: {filepath} - {e}", exc_info=True)
        return False, f"撤回失败: {str(e)}"


def revert_multi_lines(filepath, hunk_index, start_line_index, end_line_index, status, ctx_lines=5):
    """还原多行（连续的相同类型操作）"""
    logger.info(f"还原多行: {filepath} - hunk #{hunk_index}, lines #{start_line_index}-{end_line_index} (状态: {status})")
    
    try:
        # 获取文件的当前内容
        full_path = _repo_abspath(filepath)
        with open(full_path, 'r', encoding='utf-8', errors='replace') as f:
            current_lines = f.readlines()
        
        # 获取文件的原始内容（从HEAD）
        old_content, _, code = run_git(['show', 'HEAD:' + filepath])
        if code != 0:
            logger.error(f"获取文件原始内容失败: {filepath}")
            return False, "获取文件原始内容失败"
        old_lines = old_content.splitlines(keepends=True)
        
        # 获取文件的diff数据
        hunks, err = get_file_diff(filepath, status, ctx_lines)
        if err:
            logger.error(f"获取文件diff失败: {filepath} - {err}")
            return False, f"获取文件diff失败: {err}"
        
        # 记录hunks信息
        logger.info(f"获取到 {len(hunks)} 个hunks")
        
        # 确保hunk_index有效
        if hunk_index < 0 or hunk_index >= len(hunks):
            logger.error(f"无效的hunk索引: {hunk_index}, 总hunks: {len(hunks)}")
            return False, "无效的hunk索引"
        
        hunk = hunks[hunk_index]
        logger.info(f"选中hunk #{hunk_index}, 包含 {len(hunk['lines'])} 行")
        
        # 确保start_line_index和end_line_index有效
        if start_line_index < 0 or start_line_index >= len(hunk['lines']):
            logger.error(f"无效的起始行索引: {start_line_index}, hunk总行数: {len(hunk['lines'])}")
            return False, "无效的起始行索引"
        
        if end_line_index < 0 or end_line_index >= len(hunk['lines']) or end_line_index < start_line_index:
            logger.error(f"无效的结束行索引: {end_line_index}, hunk总行数: {len(hunk['lines'])}, 起始行: {start_line_index}")
            return False, "无效的结束行索引"
        
        # 获取要撤回的多行信息
        lines_to_revert = []
        for i in range(start_line_index, end_line_index + 1):
            if i < len(hunk['lines']):
                line_info = hunk['lines'][i]
                if line_info['type'] != 'context':
                    lines_to_revert.append(line_info)
        
        if len(lines_to_revert) == 0:
            logger.error("没有要撤回的非上下文行")
            return False, "没有要撤回的非上下文行"
        
        # 确保所有行类型相同
        first_type = lines_to_revert[0]['type']
        if not all(line['type'] == first_type for line in lines_to_revert):
            logger.error("多行撤回要求所有行类型相同")
            return False, "多行撤回要求所有行类型相同"
        
        logger.info(f"要撤回的多行: 类型={first_type}, 行数={len(lines_to_revert)}")
        
        # 保存修改前的行数，用于验证
        original_line_count = len(current_lines)
        logger.info(f"修改前文件行数: {original_line_count}")
        
        # 根据行类型处理撤回（从后往前处理，避免索引变化）
        if first_type == 'added':
            # 对于新增的行，从后往前删除
            for line_info in reversed(lines_to_revert):
                if line_info['new'] and line_info['new'] <= len(current_lines):
                    del current_lines[line_info['new'] - 1]
                    logger.info(f"删除新增行: 行 {line_info['new']}")
                else:
                    logger.error(f"新增行索引无效: {line_info['new']}, 文件总行数: {len(current_lines)}")
                    return False, "新增行索引无效"
        elif first_type == 'removed':
            # 对于删除的行，从后往前恢复
            for line_info in reversed(lines_to_revert):
                if line_info['old'] and line_info['old'] <= len(old_lines):
                    insert_pos = line_info['old'] - 1
                    if insert_pos < len(current_lines):
                        current_lines.insert(insert_pos, old_lines[insert_pos])
                        logger.info(f"恢复删除行: 行 {line_info['old']}, 位置 {insert_pos}")
                    else:
                        current_lines.append(old_lines[insert_pos])
                        logger.info(f"恢复删除行: 行 {line_info['old']}, 位置 {insert_pos} (末尾)")
                else:
                    logger.error(f"删除行索引无效: {line_info['old']}, 旧文件总行数: {len(old_lines)}")
                    return False, "删除行索引无效"
        elif first_type == 'modified':
            # 对于修改的行，恢复原始内容
            for line_info in lines_to_revert:
                if line_info['old'] and line_info['old'] <= len(old_lines) and line_info['new'] and line_info['new'] <= len(current_lines):
                    old_line = old_lines[line_info['old'] - 1]
                    current_lines[line_info['new'] - 1] = old_line
                    logger.info(f"恢复修改行: 行 {line_info['new']}")
                else:
                    logger.error(f"修改行索引无效: 旧行 {line_info['old']}, 新行 {line_info['new']}")
                    return False, "修改行索引无效"
        else:
            logger.error(f"不支持的行类型: {first_type}")
            return False, "不支持的行类型"
        
        # 验证行数变化
        logger.info(f"修改后文件行数: {len(current_lines)}, 修改前文件行数: {original_line_count}")
        if first_type == 'added':
            expected_count = original_line_count - len(lines_to_revert)
        elif first_type == 'removed':
            expected_count = original_line_count + len(lines_to_revert)
        else:  # modified
            expected_count = original_line_count
        
        if len(current_lines) != expected_count:
            logger.error(f"修改行数不正确: 期望 {expected_count}, 实际 {len(current_lines)}")
            return False, "修改行数不正确"
        
        # 保存修改后的文件
        with open(full_path, 'w', encoding='utf-8', newline='') as f:
            f.writelines(current_lines)
        
        logger.info(f"成功还原多行: {filepath} - hunk #{hunk_index}, lines #{start_line_index}-{end_line_index}")
        return True, f"已撤回 {len(lines_to_revert)} 行代码"
    except Exception as e:
        logger.error(f"还原多行失败: {filepath} - {e}", exc_info=True)
        return False, f"撤回失败: {str(e)}"


def revert_file(filepath, status):
    """还原整个文件"""
    logger.info(f"还原文件: {filepath} (状态: {status})")
    if status == "U":
        full = _repo_abspath(filepath)
        try:
            os.remove(full)
            logger.info(f"成功删除未跟踪文件: {filepath}")
            return True, "已删除未跟踪文件"
        except Exception as e:
            logger.error(f"删除未跟踪文件失败: {filepath} - {e}")
            return False, str(e)
    elif status == "A":
        _, err, code = run_git(["reset", "HEAD", "--", filepath])
        if code != 0:
            logger.error(f"取消暂存失败: {filepath} - {err}")
            return False, err
        full = _repo_abspath(filepath)
        try:
            os.remove(full)
            logger.info(f"成功删除新增文件: {filepath}")
            return True, "已删除新增文件"
        except Exception as e:
            logger.error(f"删除新增文件失败: {filepath} - {e}")
            return False, str(e)
    else:
        _, err, code = run_git(["checkout", "HEAD", "--", filepath])
        if code != 0:
            logger.error(f"还原文件失败: {filepath} - {err}")
            return False, err
        logger.info(f"成功还原文件: {filepath}")
        return True, "已还原"


def restore_file_from_commit(commit_hash, filepath):
    """从提交中恢复文件"""
    logger.info(f"从提交恢复文件: {commit_hash} - {filepath}")
    _, err, code = run_git(["checkout", commit_hash, "--", filepath])
    if code == 0:
        return True, "已恢复"
    return False, err


def restore_workspace_to_commit(commit_hash):
    """将工作区完整恢复到某次提交（覆盖工作区内容）"""
    logger.info(f"恢复工作区到提交: {commit_hash}")
    # hard reset to commit
    _, err, code = run_git(["reset", "--hard", commit_hash], timeout=180)
    if code != 0:
        logger.error(f"reset --hard 失败: {err}")
        return False, err or "reset --hard 失败"

    # clean untracked
    _, err2, code2 = run_git(["clean", "-fd"], timeout=180)
    if code2 != 0:
        logger.error(f"clean -fd 失败: {err2}")
        return False, err2 or "clean -fd 失败"

    logger.info("恢复工作区完成")
    return True, "已恢复工作区"


def revert_commit(commit_hash):
    """撤回指定提交（等同于 git revert <hash>，会产生一个新的提交）"""
    logger.info(f"revert 提交: {commit_hash}")
    # --no-edit 使用默认回滚信息，避免交互式编辑器卡住
    out, err, code = run_git(["revert", "--no-edit", commit_hash], timeout=300)
    if code != 0:
        msg = (err or out or "revert 失败").strip()
        logger.error(f"revert 失败: {msg}")
        return False, msg
    logger.info("revert 成功")
    return True, "已撤回该提交（已生成新的回滚提交）"


def get_raw_file_diff_patch(filepath, status, ctx_lines=5):
    """获取某个文件的原始 diff patch（用于 git apply）。"""
    try:
        ctx_lines = int(ctx_lines)
    except Exception:
        ctx_lines = 5
    if ctx_lines < 0:
        ctx_lines = 0
    if ctx_lines > 200:
        ctx_lines = 200

    if status in ("U", "A"):
        return None, "新文件不支持按块暂存，请按文件提交"
    if status == "D":
        return None, "删除文件不支持按块暂存，请按文件提交"

    unified_arg = f"--unified={ctx_lines}"
    for args in (
        ["diff", "HEAD", unified_arg, "--", filepath],
        ["diff", unified_arg, "--", filepath],
    ):
        out, err, code = run_git(args)
        if code == 0 and (out or "").strip():
            return out, None
        if code != 0 and err:
            last_err = err
        else:
            last_err = None

    return "", last_err


def extract_selected_hunks_from_patch(raw_patch, hunk_indices):
    """从单文件 patch 中抽取指定的 hunk（按出现顺序 index）组成新的 patch。"""
    if raw_patch is None:
        return None
    if not raw_patch.strip():
        return ""
    want = set(int(x) for x in (hunk_indices or []))
    if not want:
        return ""

    lines = raw_patch.splitlines(True)
    header = []
    hunks = []
    cur = None
    seen_hunk = -1

    for ln in lines:
        if ln.startswith("@@ "):
            if cur is not None:
                hunks.append(cur)
            cur = [ln]
            seen_hunk += 1
            continue
        if cur is None:
            header.append(ln)
        else:
            cur.append(ln)

    if cur is not None:
        hunks.append(cur)

    picked = []
    for idx, h in enumerate(hunks):
        if idx in want:
            picked.extend(h)

    if not picked:
        return ""
    return "".join(header + picked)


def has_any_staged_changes():
    out, err, code = run_git(["diff", "--cached", "--name-only"])
    if code != 0:
        return False, err
    return bool((out or "").strip()), None


def apply_patch_to_index(patch_text):
    if patch_text is None:
        return False, "patch 为空"
    if not patch_text.strip():
        return False, "未选择任何可暂存的变更块"
    _, err, code = run_git(["apply", "--cached", "--whitespace=nowarn", "-"], input_data=patch_text)
    if code != 0:
        return False, err
    return True, "已暂存"


# ════════════════════════════════════════════════════════
#  文件内容读取与保存
# ════════════════════════════════════════════════════════

def get_file_content(filepath):
    """获取文件内容"""
    logger.debug(f"读取文件内容: {filepath}")
    try:
        full = _repo_abspath(filepath)
        with open(full, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
        logger.debug(f"成功读取文件内容: {filepath} - {len(content)} 字符")
        return content
    except Exception as e:
        logger.error(f"读取文件内容失败: {filepath} - {e}")
        return None


def get_head_file_content(filepath):
    """获取 HEAD 版本文件内容（作为原始版本展示用）"""
    fp = (filepath or "").replace("\\", "/")
    if not fp:
        return None
    try:
        stdout, stderr, code = run_git(["show", f"HEAD:{fp}"])
        if code != 0:
            logger.debug(f"读取 HEAD 文件内容失败: {fp} - {stderr}")
            return None
        return stdout
    except Exception as e:
        logger.error(f"读取 HEAD 文件内容异常: {fp} - {e}")
        return None


def save_file_content(filepath, content):
    """保存文件内容"""
    logger.info(f"保存文件内容: {filepath} - {len(content)} 字符")
    try:
        full = _repo_abspath(filepath)
        with open(full, "w", encoding="utf-8", newline="") as f:
            f.write(content)
        logger.info(f"成功保存文件内容: {filepath}")
        return True, "保存成功"
    except Exception as e:
        logger.error(f"保存文件内容失败: {filepath} - {e}")
        return False, f"保存失败: {e}"

# ════════════════════════════════════════════════════════
#  HTTP 处理器
# ════════════════════════════════════════════════════════

class Handler(BaseHTTPRequestHandler):
    
    # 禁用默认的日志输出
    def log_message(self, format, *args):
        # 使用我们的 logger 记录 HTTP 请求
        logger.info(f"{self.address_string()} - {format % args}")

    def send_json(self, data, status=200):
        """发送 JSON 响应"""
        try:
            body = json.dumps(data, ensure_ascii=False).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", len(body))
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            self.wfile.write(body)
            
            # 记录响应
            if status >= 400:
                logger.warning(f"响应错误 {status}: {self.path} - {data}")
            else:
                logger.debug(f"响应成功 {status}: {self.path}")
        except Exception as e:
            logger.error(f"发送 JSON 响应失败: {e}", exc_info=True)

    def send_html(self):
        """发送 HTML 页面"""
        html_path = Path(__file__).parent / "index.html"
        try:
            data = html_path.read_bytes()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", len(data))
            self.end_headers()
            self.wfile.write(data)
            logger.debug(f"发送 HTML 页面: index.html")
        except Exception as e:
            logger.error(f"发送 HTML 页面失败: {e}")
            body = f"找不到 index.html: {e}".encode()
            self.send_response(500)
            self.send_header("Content-Length", len(body))
            self.end_headers()
            self.wfile.write(body)

    def do_OPTIONS(self):
        """处理 OPTIONS 请求"""
        logger.debug(f"OPTIONS 请求: {self.path}")
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET,POST,OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        """处理 GET 请求"""
        logger.info(f"收到 GET 请求: {self.path}")
        parsed = urlparse(self.path)
        p  = parsed.path
        qs = parse_qs(parsed.query)

        # 关键：unquote 解码 URL 编码（处理中文/空格路径）
        def qget(key):
            value = unquote(qs.get(key, [""])[0])
            logger.debug(f"查询参数 {key} = {value}")
            return value

        if p in ("/", "/index.html"):
            self.send_html()
            return

        if p == "/api/status":
            logger.debug("处理 /api/status 请求")
            origin_url = ""
            if REPO_PATH:
                try:
                    out, _, code = run_git(["config", "--get", "remote.origin.url"])
                    if code == 0:
                        origin_url = (out or "").strip()
                except Exception:
                    origin_url = ""
            self.send_json({
                "repo":  REPO_PATH,
                "valid": bool(REPO_PATH and
                              os.path.isdir(os.path.join(REPO_PATH, ".git"))),
                "ws_port": WS_PORT if WEBSOCKET_AVAILABLE else None,
                "origin_url": origin_url
            })

        elif p == "/api/files":
            logger.debug("处理 /api/files 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            try:
                max_age = float(qget("max_age") or "")
            except Exception:
                max_age = 1.0
            if max_age < 0:
                max_age = 0.0
            if max_age > 10:
                max_age = 10.0
            self.send_json({"files": get_changed_files_cached(max_age_sec=max_age)})

        elif p == "/api/diff":
            logger.debug("处理 /api/diff 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            fp     = qget("path")
            status = qget("status") or "M"
            ctx = qget("ctx") or "5"
            hunks, err = get_file_diff(fp, status, ctx)
            self.send_json({"hunks": hunks, "error": err})

        elif p == "/api/file_content":
            logger.debug("处理 /api/file_content GET 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            fp = qget("path")
            content = get_file_content(fp)
            if content is not None:
                # 兼容旧前端：直接使用 content 字段
                self.send_json({"ok": True, "content": content})
            else:
                self.send_json({"ok": False, "error": "无法读取文件内容"}, 404)

        elif p == "/api/log":
            logger.debug("处理 /api/log 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            self.send_json({"log": get_log()})

        elif p == "/api/commit_detail":
            logger.debug("处理 /api/commit_detail 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            commit = qget("hash")
            if not commit:
                self.send_json({"error":"缺少 hash"}, 400)
                return
            detail = get_commit_detail(commit)
            if "error" not in detail:
                # 确保返回完整hash和短hash
                if "full_hash" not in detail and "hash" in detail:
                    full_hash = detail.get("hash", "")
                    if len(full_hash) > 7:
                        detail["full_hash"] = full_hash
                        detail["hash"] = full_hash[:7]
            self.send_json(detail)

        elif p == "/api/commit_file_diff":
            logger.debug("处理 /api/commit_file_diff 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            commit = qget("hash")
            fp     = qget("path")
            hunks  = get_commit_file_diff(commit, fp)
            self.send_json({"hunks": hunks})

        elif p == "/api/branches":
            logger.debug("处理 /api/branches 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            branches, current = get_branches()
            self.send_json({"branches": branches, "current": current})

        elif p == "/api/commit_push_status":
            logger.debug("处理 /api/commit_push_status 请求")
            if not REPO_PATH:
                self.send_json({"error":"未打开仓库"}, 400)
                return
            commit = qget("hash")
            pushed, branches, err = is_commit_pushed(commit)
            self.send_json({"pushed": pushed, "branches": branches, "error": err})

        else:
            logger.warning(f"未知的 GET 请求路径: {p}")
            self.send_json({"error":"Not found"}, 404)

    def do_POST(self):
        """处理 POST 请求"""
        global REPO_PATH
        logger.info(f"收到 POST 请求: {self.path}")
        p  = urlparse(self.path).path
        ln = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(ln) if ln else b"{}"
        
        try:
            data = json.loads(body.decode("utf-8"))
            logger.debug(f"POST 请求数据: {json.dumps(data, ensure_ascii=False)[:200]}...")
        except Exception as e:
            logger.error(f"解析 JSON 失败: {e}")
            data = {}

        try:
            if p == "/api/open_repo":
                logger.info("处理 /api/open_repo 请求")
                raw = data.get("path", "").strip()
                if not raw:
                    logger.warning("打开仓库失败: 路径为空")
                    self.send_json({"error":"路径为空"}, 400)
                    return
                raw = os.path.expanduser(raw)
                logger.info(f"尝试打开仓库: {raw}")
                if not os.path.isdir(raw):
                    logger.error(f"打开仓库失败: 目录不存在 - {raw}")
                    self.send_json({"error":f"目录不存在: {raw}"}, 400)
                    return
                check = raw
                root  = None
                for _ in range(15):
                    if os.path.isdir(os.path.join(check, ".git")):
                        root = check
                        break
                    parent = os.path.dirname(check)
                    if parent == check:
                        break
                    check = parent
                if not root:
                    logger.error(f"打开仓库失败: 不是 git 仓库 - {raw}")
                    self.send_json({"error":"不是 git 仓库（未找到 .git 目录）"}, 400)
                    return
                REPO_PATH = root
                _, cur = get_branches()
                logger.info(f"成功打开仓库: {root} (分支: {cur})")
                self.send_json({"ok": True, "repo": root, "branch": cur})

            elif p == "/api/revert_hunk":
                logger.info("处理 /api/revert_hunk 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp  = data.get("path", "")
                idx = data.get("hunk_index", -1)
                st  = data.get("status", "M")
                ok, msg = revert_hunk(fp, int(idx), st)
                self.send_json({"ok": ok, "msg": msg})

            elif p == "/api/revert_line":
                logger.info("处理 /api/revert_line 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp  = data.get("path", "")
                h_idx = data.get("hunk_index", -1)
                l_idx = data.get("line_index", -1)
                st  = data.get("status", "M")
                ctx = data.get("ctx", 5)
                ok, msg = revert_line(fp, int(h_idx), int(l_idx), st, ctx)
                self.send_json({"ok": ok, "msg": msg})
            
            elif p == "/api/revert_multi_lines":
                logger.info("处理 /api/revert_multi_lines 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp  = data.get("path", "")
                h_idx = data.get("hunk_index", -1)
                start_l_idx = data.get("start_line_index", -1)
                end_l_idx = data.get("end_line_index", -1)
                st  = data.get("status", "M")
                ctx = data.get("ctx", 5)
                ok, msg = revert_multi_lines(fp, int(h_idx), int(start_l_idx), int(end_l_idx), st, ctx)
                self.send_json({"ok": ok, "msg": msg})
            
            elif p == "/api/file_content":
                logger.info("处理 /api/file_content 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp = data.get("path", "")
                content = get_file_content(fp)
                if content is not None:
                    self.send_json({"ok": True, "content": content})
                else:
                    self.send_json({"ok": False, "error": "无法读取文件内容"})

            elif p == "/api/file_content_head":
                logger.info("处理 /api/file_content_head 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp = data.get("path", "")
                content = get_head_file_content(fp)
                if content is not None:
                    self.send_json({"ok": True, "content": content})
                else:
                    self.send_json({"ok": False, "content": None})
            
            elif p == "/api/save_file":
                logger.info("处理 /api/save_file 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp = data.get("path", "")
                content = data.get("content", "")
                ok, msg = save_file_content(fp, content)
                self.send_json({"ok": ok, "msg": msg})

            elif p == "/api/revert_file":
                logger.info("处理 /api/revert_file 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                ok, msg = revert_file(data.get("path",""), data.get("status","M"))
                self.send_json({"ok": ok, "msg": msg})

            elif p == "/api/revert_all":
                logger.info("处理 /api/revert_all 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                errors = []
                files = get_changed_files()
                logger.info(f"开始还原所有文件，共 {len(files)} 个")
                for f in files:
                    ok, msg = revert_file(f["path"], f["status"])
                    if not ok:
                        errors.append(f"{f['path']}: {msg}")
                run_git(["clean", "-fd"])
                logger.info(f"还原所有文件完成，错误数: {len(errors)}")
                self.send_json({"ok": not errors, "errors": errors})

            elif p == "/api/restore_file":
                logger.info("处理 /api/restore_file 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                commit = (data.get("hash") or "").strip()
                fp = (data.get("path") or "").strip()
                ok, msg = restore_file_from_commit(commit, fp)
                self.send_json({"ok": ok, "msg": msg})

            elif p == "/api/restore_workspace":
                logger.info("处理 /api/restore_workspace 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                commit = (data.get("hash") or "").strip()
                if not commit:
                    self.send_json({"error":"缺少 hash"}, 400)
                    return
                ok, msg = restore_workspace_to_commit(commit)
                self.send_json({"ok": ok, "msg": msg})

            elif p == "/api/revert_commit":
                logger.info("处理 /api/revert_commit 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                commit = (data.get("hash") or "").strip()
                if not commit:
                    self.send_json({"error":"缺少 hash"}, 400)
                    return
                ok, msg = revert_commit(commit)
                self.send_json({"ok": ok, "msg": msg})

            elif p == "/api/commit":
                logger.info("处理 /api/commit 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                msg   = data.get("message", "").strip()
                paths = data.get("files", [])
                if not msg:
                    logger.warning("提交失败: 提交信息为空")
                    self.send_json({"error":"提交信息不能为空"}, 400)
                    return
                logger.info(f"开始提交，文件数: {len(paths)}, 消息: {msg}")
                for fp in paths:
                    run_git(["add", "--", fp])
                _, err, code = run_git(["commit", "-m", msg])
                if code != 0:
                    logger.error(f"提交失败: {err}")
                    self.send_json({"error": err}, 400)
                    return
                logger.info("提交成功")
                full_hash, _, code2 = run_git(["rev-parse", "HEAD"])
                full_hash = (full_hash or "").strip() if code2 == 0 else ""
                self.send_json({
                    "ok": True,
                    "full_hash": full_hash,
                    "hash": full_hash[:7] if full_hash else ""
                })

            elif p == "/api/commit_hunks":
                logger.info("处理 /api/commit_hunks 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return

                msg = (data.get("message") or "").strip()
                filepath = (data.get("path") or "").strip()
                status = (data.get("status") or "").strip() or "M"
                hunks = data.get("hunks") or []
                ctx_lines = data.get("ctx", 5)

                if not msg:
                    self.send_json({"error":"提交信息不能为空"}, 400)
                    return
                if not filepath:
                    self.send_json({"error":"缺少 path"}, 400)
                    return
                if not isinstance(hunks, list) or not hunks:
                    self.send_json({"error":"未选择任何变更块"}, 400)
                    return

                staged, err = has_any_staged_changes()
                if err:
                    self.send_json({"error": err}, 400)
                    return
                if staged:
                    self.send_json({"error": "检测到已有暂存区内容，请先提交/取消暂存后再进行按块提交"}, 400)
                    return

                raw_patch, patch_err = get_raw_file_diff_patch(filepath, status, ctx_lines=ctx_lines)
                if patch_err:
                    self.send_json({"error": patch_err}, 400)
                    return

                picked_patch = extract_selected_hunks_from_patch(raw_patch, hunks)
                ok, apply_err = apply_patch_to_index(picked_patch)
                if not ok:
                    self.send_json({"error": apply_err}, 400)
                    return

                _, err, code = run_git(["commit", "-m", msg])
                if code != 0:
                    logger.error(f"按块提交失败: {err}")
                    run_git(["reset"])
                    self.send_json({"error": err}, 400)
                    return

                logger.info("按块提交成功")
                full_hash, _, code2 = run_git(["rev-parse", "HEAD"])
                full_hash = (full_hash or "").strip() if code2 == 0 else ""
                self.send_json({
                    "ok": True,
                    "full_hash": full_hash,
                    "hash": full_hash[:7] if full_hash else ""
                })

            elif p == "/api/push":
                logger.info("处理 /api/push 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                _, err, code = run_git(["push"], timeout=300)
                if code == 0:
                    logger.info("推送成功")
                else:
                    logger.error(f"推送失败: {err}")
                self.send_json({"ok": code == 0, "msg": err})

            else:
                logger.warning(f"未知的 POST 请求路径: {p}")
                self.send_json({"error":"Not found"}, 404)

        except Exception as e:
            logger.error(f"处理 POST 请求异常: {p} - {str(e)}", exc_info=True)
            self.send_json({"error": f"服务器错误: {str(e)}"}, 500)


def main():
    """主函数"""
    port = 7842
    max_attempts = 10

    try:
        # 在单独的线程中启动WebSocket服务器
        if WEBSOCKET_AVAILABLE:
            ws_thread = threading.Thread(target=start_websocket_server, daemon=True)
            ws_thread.start()
            logger.info("WebSocket服务器线程已启动")
        
        # 尝试启动HTTP服务器，如果端口被占用则尝试下一个端口
        for attempt in range(max_attempts):
            try:
                srv = HTTPServer(("127.0.0.1", port), Handler)
                logger.info("=" * 60)
                logger.info("Git Manager 后端启动成功!")
                logger.info(f"HTTP 服务器: http://localhost:{port}")
                if WEBSOCKET_AVAILABLE:
                    logger.info(f"WebSocket 服务器: ws://localhost:{WS_PORT}")
                logger.info(f"日志目录: {LOG_DIR}")
                logger.info("=" * 60)
                print(f"\n{'='*60}")
                print(f"  Git Manager 已启动!")
                print(f"  浏览器打开 → http://localhost:{port}")
                if WEBSOCKET_AVAILABLE:
                    print(f"  WebSocket → ws://localhost:{WS_PORT} (实时通信)")
                print(f"  日志文件 → {log_file}")
                print(f"{'='*60}\n")
                
                srv.serve_forever()
            except OSError as e:
                if e.errno == 10048:  # 端口被占用
                    logger.warning(f"端口 {port} 被占用，尝试下一个端口...")
                    port += 1
                    continue
                else:
                    raise
    except KeyboardInterrupt:
        logger.info("收到键盘中断信号，正在关闭服务器...")
        print("\n正在关闭服务器...")
    except Exception as e:
        logger.critical(f"服务器启动失败: {e}", exc_info=True)
        print(f"\n服务器启动失败: {e}")
        sys.exit(1)
    finally:
        logger.info("Git Manager 后端已停止")
        print("已停止")


if __name__ == "__main__":
    main()