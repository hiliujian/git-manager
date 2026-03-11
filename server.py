#!/usr/bin/env python3
"""
Git Manager Backend — 完整修复版 + 完善日志系统 + WebSocket实时通信
python3 server.py  →  http://localhost:7842
"""

import subprocess, os, json, re, sys, logging, threading, hashlib, time, difflib
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

try:
    import chardet
    CHARDET_AVAILABLE = True
except ImportError:
    CHARDET_AVAILABLE = False
    print("提示: chardet 库未安装，中文编码检测可能不够准确")
    print("安装方法: pip install chardet")

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
        ra = None
        try:
            ra = websocket.remote_address
        except Exception:
            ra = None
        logger.info(f"WebSocket连接关闭: {ra}")


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

def get_unmerged_files():
    """Return a list of unmerged (conflicted) files in the working tree.

    Used by /api/pull to detect merge conflicts.
    Returns: (files: List[str], raw_output: str)
    """
    if not REPO_PATH:
        return [], ""

    # Prefer diff-filter=U which directly lists unmerged paths
    out, err, code = run_git(["diff", "--name-only", "--diff-filter=U", "-z"], timeout=60)
    raw = (out or "")
    if code != 0:
        # Fallback to ls-files -u when diff fails
        out2, err2, code2 = run_git(["ls-files", "-u", "-z"], timeout=60)
        raw = (out2 or "")
        if code2 != 0:
            logger.debug(f"获取冲突文件失败: {err or err2}")
            return [], raw

        # ls-files -u -z format: <mode> <sha> <stage>\t<path>\0 ...
        files = []
        for item in raw.split("\x00"):
            if not item:
                continue
            if "\t" in item:
                path = item.split("\t", 1)[1]
                if path:
                    files.append(path)
        uniq = sorted({p.replace("\\", "/") for p in files if p})
        return uniq, raw

    items = [p for p in raw.split("\x00") if p]
    uniq = sorted({p.replace("\\", "/") for p in items if p})
    return uniq, raw

def has_any_staged_changes():
    if not REPO_PATH:
        return False, "未打开仓库"
    out, err, code = run_git(["diff", "--cached", "--name-only", "-z"], timeout=60)
    if code != 0:
        return False, (err or "检查暂存区失败")
    raw = out or ""
    files = [p for p in raw.split("\x00") if p]
    return (len(files) > 0), None

def _safe_repo_abspath(rel_path: str):
    """Resolve a repo-relative path to an absolute path, preventing path traversal."""
    if not REPO_PATH:
        return None
    repo_root = os.path.abspath(REPO_PATH)
    rel_path = (rel_path or "")
    try:
        rel_path = rel_path.replace("\x00", "")
    except Exception:
        pass
    rel_path = str(rel_path).strip()
    rel_path = rel_path.replace("\\", "/")
    if rel_path.lower().startswith("file://"):
        rel_path = rel_path[7:]

    try:
        if os.path.isabs(rel_path) or re.match(r"^[A-Za-z]:[\\/]", rel_path or ""):
            abs_in = os.path.abspath(rel_path)
            try:
                if os.path.commonpath([repo_root, abs_in]) != repo_root:
                    return None
            except Exception:
                return None
            rel_path = os.path.relpath(abs_in, repo_root).replace("\\", "/")
    except Exception:
        pass

    rel_path = rel_path.lstrip("/")
    rel_path = rel_path.replace("\r", "").replace("\n", "")
    if not rel_path:
        return None

    bad_chars = '<>:"|?*'
    parts = [p for p in rel_path.split("/") if p not in ("", ".")]
    for p in parts:
        if p in ("..",):
            return None
        if any((c in p) for c in bad_chars):
            return None
        if any((ord(c) < 32) for c in p):
            return None
        if p.endswith(" ") or p.endswith("."):
            return None

    rel_path = "/".join(parts)
    abs_path = os.path.abspath(os.path.join(repo_root, rel_path.replace("/", os.sep)))
    try:
        if os.path.commonpath([repo_root, abs_path]) != repo_root:
            return None
    except Exception:
        return None
    return abs_path


def get_file_content(filepath: str, return_encoding=False):
    """Read working tree file content as text.
    
    Args:
        filepath: 文件路径
        return_encoding: 是否返回检测到的编码，默认False（向后兼容）
    
    Returns:
        如果return_encoding=False: 返回文件内容字符串或None
        如果return_encoding=True: 返回(内容字符串, 编码名称)或(None, None)
    """
    try:
        full = _safe_repo_abspath(filepath)
        if not full or (not os.path.exists(full)) or os.path.isdir(full):
            return (None, None) if return_encoding else None
        with open(full, "rb") as f:
            data = f.read()
        
        # 如果数据为空,直接返回空字符串
        if not data:
            return ("", "utf-8") if return_encoding else ""
        
        detected_encoding = None
        
        # 首先尝试UTF-8（最常见的编码）
        try:
            # 先尝试纯UTF-8解码
            result = data.decode('utf-8')
            detected_encoding = "utf-8"
            logger.debug(f"文件 {filepath} 使用 UTF-8 编码")
            return (result, detected_encoding) if return_encoding else result
        except UnicodeDecodeError:
            pass
        
        # 尝试UTF-8 with BOM
        try:
            result = data.decode('utf-8-sig')
            detected_encoding = "utf-8-sig"
            logger.debug(f"文件 {filepath} 使用 UTF-8-BOM 编码")
            return (result, detected_encoding) if return_encoding else result
        except UnicodeDecodeError:
            pass
        
        # UTF-8 严格解码失败：仍使用 UTF-8+replace 返回。
        # 目标：避免把 UTF-8 文件误按 GBK/GB2312 解码导致典型乱码（并在保存后写回扩大损害）。
        result = data.decode("utf-8", errors="replace")
        detected_encoding = "utf-8"
        logger.warning(f"文件 {filepath} UTF-8 严格解码失败，已使用 UTF-8+replace 读取")
        return (result, detected_encoding) if return_encoding else result
    except Exception as e:
        logger.error(f"读取文件内容失败: {filepath} - {e}")
        return (None, None) if return_encoding else None


def _detect_text_encoding_from_bytes(data: bytes):
    """检测文本数据的编码格式"""
    if data is None or len(data) == 0:
        return "utf-8"
    
    # 检查 UTF-8 BOM
    try:
        if data.startswith(b"\xef\xbb\xbf"):
            return "utf-8-sig"
    except Exception:
        pass
    
    # 首先尝试UTF-8（最常见）
    try:
        data.decode('utf-8')
        return "utf-8"
    except UnicodeDecodeError:
        pass
    
    # 使用chardet检测（如果可用）
    if CHARDET_AVAILABLE:
        try:
            detected = chardet.detect(data)
            if detected and detected.get('encoding'):
                detected_enc = detected['encoding']
                confidence = detected.get('confidence', 0)
                
                if confidence > 0.5:
                    detected_enc_lower = detected_enc.lower()
                    # 标准化编码
                    if detected_enc_lower in ('gb2312',):
                        return 'gb2312'
                    if detected_enc_lower in ('gbk', 'windows-1252'):
                        return 'gbk'
                    if detected_enc_lower in ('gb18030',):
                        return 'gb18030'
                    elif detected_enc_lower.startswith('utf'):
                        return 'utf-8'
                    else:
                        # 验证检测到的编码是否有效
                        try:
                            data.decode(detected_enc)
                            return detected_enc
                        except Exception:
                            pass
        except Exception:
            pass
    
    # Fallback: 按优先级尝试常见编码
    for enc in ("gbk", "gb18030", "gb2312", "cp936", "latin-1"):
        try:
            data.decode(enc)
            return enc
        except Exception:
            continue
    
    return "utf-8"


def get_head_file_content(filepath: str):
    """Read HEAD version file content as text via git show."""
    filepath = (filepath or "").replace("\\", "/").lstrip("/")
    if not filepath:
        return None
    out, err, code = run_git(["show", f"HEAD:{filepath}"])
    if code != 0:
        logger.debug(f"读取 HEAD 文件内容失败: {filepath} - {err}")
        return None
    return out


def save_file_content(filepath: str, content: str, force_encoding: str = None):
    """Save content to working tree file (text).
    
    Args:
        filepath: 文件路径
        content: 文件内容
        force_encoding: 强制使用的编码（如果提供，将覆盖自动检测）
    """
    try:
        full = _safe_repo_abspath(filepath)
        if not full:
            logger.error(f"保存文件失败: 非法路径 {filepath}")
            return False, "非法路径"
        
        logger.info(f"开始保存文件: {filepath}, 内容长度: {len(content) if content else 0}, 强制编码: {force_encoding}")
        
        parent = os.path.dirname(full)
        if parent and (not os.path.exists(parent)):
            os.makedirs(parent, exist_ok=True)
            logger.debug(f"创建目录: {parent}")

        target_enc = "utf-8"
        file_exists = os.path.exists(full) and (not os.path.isdir(full))
        
        # 如果指定了编码，优先使用
        if force_encoding:
            target_enc = force_encoding
            logger.debug(f"使用强制指定的编码: {target_enc}")
        else:
            try:
                if file_exists:
                    with open(full, "rb") as rf:
                        raw0 = rf.read()
                    target_enc = _detect_text_encoding_from_bytes(raw0)
                    logger.debug(f"检测到已存在文件编码: {target_enc}")
                else:
                    logger.debug(f"新文件，使用默认编码: {target_enc}")
            except Exception as e:
                logger.warning(f"检测文件编码失败: {e}, 使用默认UTF-8")
                target_enc = "utf-8"

        rel_path = (filepath or "").replace("\\", "/").lstrip("/")

        # Decide target EOL:
        # Priority: 1) detect from original file (most reliable)
        #           2) git attributes (eol)
        #           3) core.autocrlf (working tree convention)
        #           4) fallback: LF
        target_eol = None

        # Step 1: Detect from existing file (highest priority - preserves original)
        try:
            if file_exists:
                with open(full, "rb") as rf:
                    data = rf.read()
                # Check if file has CRLF or LF
                if b"\r\n" in data:
                    target_eol = "\r\n"
                    logger.debug(f"检测到文件 {filepath} 使用 CRLF 换行符")
                elif b"\n" in data:
                    target_eol = "\n"
                    logger.debug(f"检测到文件 {filepath} 使用 LF 换行符")
        except Exception as e:
            logger.warning(f"检测文件换行符失败: {e}")

        # Step 2: Check git attributes if we couldn't detect from file
        if target_eol is None:
            try:
                out, _, code = run_git(["check-attr", "-z", "eol", "--", rel_path], timeout=30)
                if code == 0 and out:
                    parts = out.split("\x00")
                    # format: path\0attr\0value\0
                    if len(parts) >= 3:
                        val = (parts[2] or "").strip().lower()
                        if val == "crlf":
                            target_eol = "\r\n"
                            logger.debug(f"从 git 属性检测到 {filepath} 使用 CRLF")
                        elif val == "lf":
                            target_eol = "\n"
                            logger.debug(f"从 git 属性检测到 {filepath} 使用 LF")
            except Exception as e:
                logger.warning(f"检查 git 属性失败: {e}")

        # Step 3: Check core.autocrlf if still unknown
        if target_eol is None:
            try:
                out2, _, code2 = run_git(["config", "--get", "core.autocrlf"], timeout=10)
                if code2 == 0 and (out2 or "").strip().lower() == "true":
                    target_eol = "\r\n"
                    logger.debug(f"从 core.autocrlf 检测到使用 CRLF")
            except Exception as e:
                logger.warning(f"检查 core.autocrlf 失败: {e}")

        # Step 4: Default to LF if still unknown
        if target_eol is None:
            target_eol = "\n"
            logger.debug(f"使用默认换行符 LF")

        txt = content if content is not None else ""
        
        # Check if content already has the correct line endings
        has_crlf = "\r\n" in txt
        has_lf_only = "\n" in txt and not has_crlf
        
        if target_eol == "\r\n" and has_crlf:
            # Content already has CRLF and we want CRLF - no conversion needed
            logger.debug(f"内容已是 CRLF 格式,无需转换")
            pass
        elif target_eol == "\n" and has_lf_only:
            # Content already has LF only and we want LF - no conversion needed
            logger.debug(f"内容已是 LF 格式,无需转换")
            pass
        else:
            # Need to normalize and convert
            logger.debug(f"转换换行符: 当前={'CRLF' if has_crlf else 'LF'} -> 目标={repr(target_eol)}")
            txt = str(txt).replace("\r\n", "\n").replace("\r", "\n")
            if target_eol != "\n":
                txt = txt.replace("\n", target_eol)

        # Write exact newlines without implicit translation
        logger.debug(f"准备写入文件: {full}, 编码: {target_enc}, 换行符: {repr(target_eol)}, 内容长度: {len(txt)}")
        with open(full, "w", encoding=target_enc, newline="") as f:
            f.write(txt)
        
        logger.info(f"✓ 文件保存成功: {filepath} (编码: {target_enc}, 换行符: {repr(target_eol)}, {len(txt)}字符)")
        return True, "保存成功"
    except Exception as e:
        logger.error(f"保存文件失败: {filepath} - {e}", exc_info=True)
        return False, str(e)



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
                txt_u = get_file_content(p_key) or ""
                added = len(txt_u.splitlines())
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
            txt_u = get_file_content(filepath) or ""
            content = txt_u.splitlines(keepends=True)
            # Empty new file: still render one editable empty line so user can type.
            if not content:
                content = ["\n"]
            # Preserve trailing empty line for files ending with EOL.
            # Python splitlines(keepends=True) does not include the final empty line.
            if txt_u.endswith("\n") or txt_u.endswith("\r"):
                content.append("\n")
            logger.debug(f"读取新文件内容: {filepath} - {len(content)} 行")
            return [{
                "header":    f"@@ -0,0 +1,{len(content)} @@ 新文件",
                "old_start": 0,
                "new_start": 1,
                "lines": [{"type":"added","old":None,"new":i+1,"text":l.rstrip("\n").rstrip("\r")}
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
    removed_block = []
    added_block = []

    def _norm_line(s):
        if s is None:
            return ""
        return s[:-1] if s.endswith("\r") else s

    def _lcs_pairs(a, b):
        n = len(a)
        m = len(b)
        if n == 0 or m == 0:
            return []
        dp = [[0] * (m + 1) for _ in range(n + 1)]
        for i in range(n - 1, -1, -1):
            ai = a[i]
            row = dp[i]
            row_next = dp[i + 1]
            for j in range(m - 1, -1, -1):
                if ai == b[j]:
                    row[j] = row_next[j + 1] + 1
                else:
                    v1 = row_next[j]
                    v2 = row[j + 1]
                    row[j] = v1 if v1 >= v2 else v2

        pairs = []
        i = j = 0
        while i < n and j < m:
            if a[i] == b[j]:
                pairs.append((i, j))
                i += 1
                j += 1
            else:
                if dp[i + 1][j] >= dp[i][j + 1]:
                    i += 1
                else:
                    j += 1
        return pairs

    def _line_similarity(s1, s2):
        """计算两行文本的相似度 (0.0 - 1.0)"""
        if s1 == s2:
            return 1.0
        if not s1 or not s2:
            return 0.0

        s1_stripped = s1.strip()
        s2_stripped = s2.strip()
        if not s1_stripped or not s2_stripped:
            return 0.0

        def _collapse_ws(s: str):
            try:
                return " ".join((s or "").split())
            except Exception:
                return (s or "").strip()

        a = _collapse_ws(s1_stripped)
        b = _collapse_ws(s2_stripped)
        if not a or not b:
            return 0.0

        len1, len2 = len(a), len(b)
        max_len = max(len1, len2)
        if max_len > 0:
            len_ratio = min(len1, len2) / max_len
            if len_ratio < 0.15:
                return 0.0

        try:
            if a.startswith(b) or b.startswith(a):
                return max(len_ratio, 0.6)
        except Exception:
            pass

        try:
            return difflib.SequenceMatcher(None, a, b, autojunk=False).ratio()
        except Exception:
            return 0.0

    def flush_change_block():
        nonlocal removed_block, added_block, ol, nl, cur
        if not cur:
            removed_block = []
            added_block = []
            return
        if not removed_block and not added_block:
            return

        pairs = _lcs_pairs(removed_block, added_block)
        ri = ai = 0

        def emit_unmatched(r_end, a_end):
            nonlocal ri, ai, ol, nl
            r_len = r_end - ri
            a_len = a_end - ai
            
            # 纯新增场景
            if r_len == 0:
                for k in range(a_len):
                    cur["lines"].append({"type": "added", "old": None, "new": nl, "text": added_block[ai + k]})
                    nl += 1
                ri = r_end
                ai = a_end
                return
            
            # 纯删除场景
            if a_len == 0:
                for k in range(r_len):
                    cur["lines"].append({"type": "removed", "old": ol, "new": None, "text": removed_block[ri + k]})
                    ol += 1
                ri = r_end
                ai = a_end
                return
            
            # 同时存在删除和新增: 使用智能匹配
            # 构建相似度矩阵，找出最佳匹配
            removed_lines = removed_block[ri:r_end]
            added_lines = added_block[ai:a_end]

            sm = difflib.SequenceMatcher(a=removed_lines, b=added_lines, autojunk=False)
            for tag, i1, i2, j1, j2 in sm.get_opcodes():
                if tag == "equal":
                    for k in range(i2 - i1):
                        cur["lines"].append({"type": "context", "old": ol, "new": nl, "text": removed_lines[i1 + k]})
                        ol += 1
                        nl += 1

                elif tag == "delete":
                    for k in range(i1, i2):
                        cur["lines"].append({"type": "removed", "old": ol, "new": None, "text": removed_lines[k]})
                        ol += 1

                elif tag == "insert":
                    for k in range(j1, j2):
                        cur["lines"].append({"type": "added", "old": None, "new": nl, "text": added_lines[k]})
                        nl += 1

                else:  # replace
                    r_seg = removed_lines[i1:i2]
                    a_seg = added_lines[j1:j2]

                    if not r_seg:
                        for txt in a_seg:
                            cur["lines"].append({"type": "added", "old": None, "new": nl, "text": txt})
                            nl += 1
                        continue
                    if not a_seg:
                        for txt in r_seg:
                            cur["lines"].append({"type": "removed", "old": ol, "new": None, "text": txt})
                            ol += 1
                        continue


                    pairs = []
                    for rr, r_txt in enumerate(r_seg):
                        for aa, a_txt in enumerate(a_seg):
                            sim = _line_similarity(r_txt, a_txt)
                            if sim >= 0.25:
                                pairs.append((sim, rr, aa))

                    pairs.sort(reverse=True)
                    used_r = set()
                    used_a = set()
                    chosen = []
                    for sim, rr, aa in pairs:
                        if rr in used_r or aa in used_a:
                            continue
                        used_r.add(rr)
                        used_a.add(aa)
                        chosen.append((rr, aa))

                    chosen.sort()
                    r_i = 0
                    a_i = 0
                    c_i = 0
                    while r_i < len(r_seg) or a_i < len(a_seg):
                        if c_i < len(chosen):
                            mr, ma = chosen[c_i]
                            if r_i == mr and a_i == ma:
                                cur["lines"].append({
                                    "type": "modified",
                                    "old": ol,
                                    "new": nl,
                                    "text": a_seg[a_i],
                                    "old_text": r_seg[r_i]
                                })
                                ol += 1
                                nl += 1
                                r_i += 1
                                a_i += 1
                                c_i += 1
                                continue
                            if r_i < mr:
                                cur["lines"].append({"type": "removed", "old": ol, "new": None, "text": r_seg[r_i]})
                                ol += 1
                                r_i += 1
                                continue
                            if a_i < ma:
                                cur["lines"].append({"type": "added", "old": None, "new": nl, "text": a_seg[a_i]})
                                nl += 1
                                a_i += 1
                                continue

                        if r_i < len(r_seg):
                            cur["lines"].append({"type": "removed", "old": ol, "new": None, "text": r_seg[r_i]})
                            ol += 1
                            r_i += 1
                        elif a_i < len(a_seg):
                            cur["lines"].append({"type": "added", "old": None, "new": nl, "text": a_seg[a_i]})
                            nl += 1
                            a_i += 1
            
            ri = r_end
            ai = a_end

        for rj, aj in pairs:
            if rj > ri or aj > ai:
                emit_unmatched(rj, aj)

            cur["lines"].append({"type": "context", "old": ol, "new": nl, "text": removed_block[rj]})
            ol += 1
            nl += 1
            ri = rj + 1
            ai = aj + 1

        if ri < len(removed_block) or ai < len(added_block):
            emit_unmatched(len(removed_block), len(added_block))

        removed_block = []
        added_block = []

    
    for raw_line in (text or "").splitlines():
        if raw_line.startswith("\\ No newline at end of file"):
            continue
        if raw_line.startswith("+++") or raw_line.startswith("---"):
            continue
            
        m = re.match(r'^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@(.*)', raw_line)
        if m:
            if cur:
                flush_change_block()
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
            added_block.append(_norm_line(raw_line[1:]))

        elif raw_line.startswith("-"):
            removed_block.append(_norm_line(raw_line[1:]))

        else:
            flush_change_block()
            text = raw_line[1:] if raw_line.startswith(" ") else raw_line
            text = _norm_line(text)
            cur["lines"].append({"type":"context", "old":ol, "new":nl, "text":text})
            ol += 1
            nl += 1

    if cur:
        flush_change_block()
        hunks.append(cur)
    
    logger.debug(f"解析完成，共 {len(hunks)} 个 hunk")
    return hunks


def _get_raw_file_diff_patch(filepath, status, ctx_lines=5):
    try:
        ctx_lines = int(ctx_lines)
    except Exception:
        ctx_lines = 5
    if ctx_lines < 0:
        ctx_lines = 0
    if ctx_lines > 200:
        ctx_lines = 200

    filepath = (filepath or "").replace("\\", "/").lstrip("/")
    if not filepath:
        return None, "缺少 path"

    st = (status or "").strip().upper() or "M"
    if st == "U":
        return None, "未跟踪文件不支持按行/按块撤回"

    unified_arg = f"--unified={ctx_lines}"
    for args in (
        ["diff", "HEAD", unified_arg, "--", filepath],
        ["diff", unified_arg, "--", filepath],
        ["diff", "--cached", unified_arg, "--", filepath],
    ):
        out, err, code = run_git(args)
        if code == 0 and (out or "").strip():
            return out, None

    return "", None


def _parse_unified_patch_with_mapping(patch_text: str):
    lines = (patch_text or "").splitlines(True)  # keep line endings
    file_header = []
    hunks = []

    cur = None
    removed_buf = []  # [raw_idx]

    def flush_removed():
        nonlocal removed_buf, cur
        while removed_buf:
            raw_idx = removed_buf.pop(0)
            pi = cur["parsed_idx"]
            cur["map"][pi] = [raw_idx]
            cur["parsed_idx"] += 1

    for ln in lines:
        m = re.match(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', ln)
        if m:
            if cur:
                flush_removed()
                hunks.append(cur)
            cur = {
                "header": ln.rstrip("\n"),
                "old_start": int(m.group(1)),
                "new_start": int(m.group(3)),
                "raw_lines": [],
                "map": {},
                "parsed_idx": 0,
            }
            continue

        if not cur:
            file_header.append(ln)
            continue

        cur["raw_lines"].append(ln)
        raw_idx = len(cur["raw_lines"]) - 1

        if ln.startswith("+"):
            if removed_buf:
                old_raw_idx = removed_buf.pop(0)
                pi = cur["parsed_idx"]
                cur["map"][pi] = [old_raw_idx, raw_idx]
                cur["parsed_idx"] += 1
            else:
                pi = cur["parsed_idx"]
                cur["map"][pi] = [raw_idx]
                cur["parsed_idx"] += 1
        elif ln.startswith("-"):
            removed_buf.append(raw_idx)
        else:
            flush_removed()
            pi = cur["parsed_idx"]
            cur["map"][pi] = [raw_idx]
            cur["parsed_idx"] += 1

    if cur:
        flush_removed()
        hunks.append(cur)

    for h in hunks:
        h.pop("parsed_idx", None)
    return file_header, hunks


def _build_partial_hunk_patch(file_header_lines, hunk, include_raw_idx_set):
    raw_lines = hunk.get("raw_lines") or []
    include = set(int(x) for x in (include_raw_idx_set or set()) if x is not None)
    if not raw_lines or not include:
        return None

    old_ln = int(hunk.get("old_start") or 0)
    new_ln = int(hunk.get("new_start") or 0)

    hunks_out = []
    cur_start_old = None
    cur_start_new = None
    cur_old_len = 0
    cur_new_len = 0
    cur_lines = []

    def flush_current():
        nonlocal cur_start_old, cur_start_new, cur_old_len, cur_new_len, cur_lines
        if cur_start_old is None or not cur_lines:
            cur_start_old = None
            cur_start_new = None
            cur_old_len = 0
            cur_new_len = 0
            cur_lines = []
            return
        hdr = f"@@ -{cur_start_old},{cur_old_len} +{cur_start_new},{cur_new_len} @@\n"
        hunks_out.append(hdr + "".join(cur_lines))
        cur_start_old = None
        cur_start_new = None
        cur_old_len = 0
        cur_new_len = 0
        cur_lines = []

    for i, ln in enumerate(raw_lines):
        inc = (i in include)

        # If we are in a running hunk but current line is excluded, close the hunk.
        if (not inc) and cur_start_old is not None:
            flush_current()

        if inc:
            if cur_start_old is None:
                cur_start_old = old_ln
                cur_start_new = new_ln
            cur_lines.append(ln)
            if ln.startswith(" "):
                cur_old_len += 1
                cur_new_len += 1
            elif ln.startswith("-"):
                cur_old_len += 1
            elif ln.startswith("+"):
                cur_new_len += 1

        # advance counters regardless of inclusion
        if ln.startswith(" "):
            old_ln += 1
            new_ln += 1
        elif ln.startswith("-"):
            old_ln += 1
        elif ln.startswith("+"):
            new_ln += 1

    if cur_start_old is not None:
        flush_current()

    if not hunks_out:
        return None

    patch = "".join(file_header_lines) + "".join(hunks_out)
    if not patch.endswith("\n"):
        patch += "\n"
    return patch


def _git_apply_reverse_patch(patch_text: str):
    if not patch_text:
        return False, "空 patch"

    attempts = [
        ["apply", "-R", "--whitespace=nowarn", "--recount"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "-C0"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--unidiff-zero"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--unidiff-zero", "-C0"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--3way"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--3way", "-C0"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--3way", "--unidiff-zero"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--ignore-space-change"],
        ["apply", "-R", "--whitespace=nowarn", "--recount", "--ignore-whitespace"],
    ]

    last_msg = ""
    for args in attempts:
        out, err, code = run_git(args, input_data=patch_text, timeout=120)
        if code == 0:
            return True, ""
        last_msg = (err or out or "git apply 失败")

    return False, last_msg


def revert_file(filepath: str, status: str):
    if not REPO_PATH:
        return False, "未打开仓库"
    filepath = (filepath or "").replace("\\", "/").lstrip("/")
    if not filepath:
        return False, "缺少 path"

    st = (status or "").strip().upper() or "M"
    full = _safe_repo_abspath(filepath)
    if not full:
        return False, "非法路径"

    if st == "U":
        try:
            if os.path.exists(full) and (not os.path.isdir(full)):
                os.remove(full)
            return True, ""
        except Exception as e:
            return False, str(e)

    _, err, code = run_git(["checkout", "--", filepath], timeout=120)
    if code != 0:
        return False, (err or "撤回文件失败")
    return True, ""


def revert_hunk(filepath: str, hunk_idx: int, status: str, ctx_lines: int = 5):
    raw_patch, err = _get_raw_file_diff_patch(filepath, status, ctx_lines=ctx_lines)
    if err:
        return False, err
    if raw_patch is None or (not raw_patch.strip()):
        return False, "无可撤回变更"

    file_header, hunks = _parse_unified_patch_with_mapping(raw_patch)
    if hunk_idx < 0 or hunk_idx >= len(hunks):
        return False, "hunk_index 越界"

    h = hunks[hunk_idx]
    include = set(range(len(h.get("raw_lines") or [])))
    patch = _build_partial_hunk_patch(file_header, h, include)
    if not patch:
        return False, "构建 patch 失败"
    ok, msg = _git_apply_reverse_patch(patch)
    if ok:
        return True, ""
    # Retry with zero-context diff to reduce context mismatches
    raw_patch2, err2 = _get_raw_file_diff_patch(filepath, status, ctx_lines=0)
    if err2 or (not raw_patch2) or (not raw_patch2.strip()):
        return False, msg
    file_header2, hunks2 = _parse_unified_patch_with_mapping(raw_patch2)
    if hunk_idx < 0 or hunk_idx >= len(hunks2):
        return False, msg
    h2 = hunks2[hunk_idx]
    include2 = set(range(len(h2.get("raw_lines") or [])))
    patch2 = _build_partial_hunk_patch(file_header2, h2, include2)
    if not patch2:
        return False, msg
    return _git_apply_reverse_patch(patch2)


def revert_line(filepath: str, hunk_idx: int, line_idx: int, status: str, ctx_lines: int = 5, signature: dict | None = None):
    if not REPO_PATH:
        return False, "未打开仓库"

    filepath = (filepath or "").replace("\\", "/").lstrip("/")
    if not filepath:
        return False, "缺少 path"

    full = _safe_repo_abspath(filepath)
    if not full:
        return False, "非法路径"

    st = (status or "").strip().upper() or "M"
    if st == "U":
        return False, "未跟踪文件不支持按行撤回"

    try:
        hunk_idx = int(hunk_idx)
        line_idx = int(line_idx)
    except Exception:
        return False, "参数非法"

    hunks, err = get_file_diff(filepath, st, ctx_lines)
    if err:
        return False, err
    if not hunks:
        return False, "无可撤回变更"
    if hunk_idx < 0 or hunk_idx >= len(hunks):
        return False, "hunk_index 越界"

    h = hunks[hunk_idx] or {}
    lines = h.get("lines") or []

    def _to_int(x):
        try:
            return int(x)
        except Exception:
            return None

    def _sig_match(dl0: dict, sig0: dict) -> bool:
        if not dl0 or not sig0:
            return False
        t0 = (dl0.get("type") or "").lower()
        ts = (sig0.get("type") or "").lower()
        if t0 != ts:
            return False
        if (dl0.get("text") or "") != (sig0.get("text") or ""):
            return False
        if (dl0.get("old_text") or "") != (sig0.get("old_text") or ""):
            return False
        n0 = _to_int(dl0.get("new"))
        ns = _to_int(sig0.get("new"))
        o0 = _to_int(dl0.get("old"))
        os = _to_int(sig0.get("old"))
        if ns is not None and n0 != ns:
            return False
        if os is not None and o0 != os:
            return False
        return True

    if signature:
        found_idx = None
        for i, dli in enumerate(lines):
            try:
                if _sig_match(dli or {}, signature):
                    found_idx = i
                    break
            except Exception:
                pass
        if found_idx is not None:
            line_idx = found_idx

    if line_idx < 0 or line_idx >= len(lines):
        return False, "line_index 越界"
    dl = lines[line_idx] or {}

    full = _safe_repo_abspath(filepath)
    if not full:
        return False, "非法路径"

    try:
        with open(full, "r", encoding="utf-8", errors="replace", newline="") as f:
            cur_lines = f.readlines()
    except Exception as e:
        return False, str(e)

    eol = "\n"
    for l in cur_lines:
        if l.endswith("\r\n"):
            eol = "\r\n"
            break
        if l.endswith("\n"):
            eol = "\n"
            break

    def _ensure_eol(s: str) -> str:
        if s is None:
            s = ""
        if s.endswith("\r\n") or s.endswith("\n"):
            return s
        return s + eol

    t = (dl.get("type") or "").lower()
    if t == "context":
        return False, "无法撤回上下文行"

    if t in ("added", "modified"):
        new_no = dl.get("new")
        if new_no is None:
            return False, "缺少 new 行号"
        try:
            new_no = int(new_no)
        except Exception:
            return False, "new 行号非法"
        idx0 = new_no - 1
        if idx0 < 0 or idx0 >= len(cur_lines):
            return False, "目标行号越界"

        if t == "added":
            cur_lines.pop(idx0)
        else:
            old_text = dl.get("old_text")
            if old_text is None:
                return False, "缺少 old_text"
            ending = ""
            if cur_lines[idx0].endswith("\r\n"):
                ending = "\r\n"
            elif cur_lines[idx0].endswith("\n"):
                ending = "\n"
            cur_lines[idx0] = (old_text + ending) if ending else _ensure_eol(old_text)

    elif t == "removed":
        ins_text = dl.get("text")
        if ins_text is None:
            return False, "缺少 text"
        ins_line = _ensure_eol(ins_text)

        insert_at = None
        for j in range(line_idx + 1, len(lines)):
            nxt = lines[j] or {}
            n_new = nxt.get("new")
            if n_new is not None:
                try:
                    insert_at = max(0, int(n_new) - 1)
                    break
                except Exception:
                    pass
        if insert_at is None:
            for j in range(line_idx - 1, -1, -1):
                prv = lines[j] or {}
                p_new = prv.get("new")
                if p_new is not None:
                    try:
                        insert_at = max(0, int(p_new))
                        break
                    except Exception:
                        pass
        if insert_at is None:
            insert_at = len(cur_lines)
        if insert_at > len(cur_lines):
            insert_at = len(cur_lines)
        cur_lines.insert(insert_at, ins_line)

    else:
        return False, "不支持的行类型"

    try:
        with open(full, "w", encoding="utf-8", errors="replace", newline="") as f:
            f.writelines(cur_lines)
    except Exception as e:
        return False, str(e)

    return True, ""


def revert_multi_lines(filepath: str, hunk_idx: int, start_line_idx: int, end_line_idx: int, status: str, ctx_lines: int = 5):
    if not REPO_PATH:
        return False, "未打开仓库"

    filepath = (filepath or "").replace("\\", "/").lstrip("/")
    if not filepath:
        return False, "缺少 path"

    st = (status or "").strip().upper() or "M"
    if st == "U":
        return False, "未跟踪文件不支持按行撤回"

    try:
        hunk_idx = int(hunk_idx)
        start_line_idx = int(start_line_idx)
        end_line_idx = int(end_line_idx)
    except Exception:
        return False, "参数非法"

    if start_line_idx > end_line_idx:
        start_line_idx, end_line_idx = end_line_idx, start_line_idx

    hunks, err = get_file_diff(filepath, st, ctx_lines)
    if err:
        return False, err
    if not hunks:
        return False, "无可撤回变更"
    if hunk_idx < 0 or hunk_idx >= len(hunks):
        return False, "hunk_index 越界"

    h = hunks[hunk_idx] or {}
    lines = h.get("lines") or []
    if not lines:
        return False, "无可撤回变更"

    start_line_idx = max(0, start_line_idx)
    end_line_idx = min(len(lines) - 1, end_line_idx)
    if start_line_idx > end_line_idx:
        return False, "line_index 越界"

    targets = []
    for li in range(start_line_idx, end_line_idx + 1):
        dl = lines[li] or {}
        t = (dl.get("type") or "").lower()
        if not t or t == "context":
            continue
        sig = {
            "type": dl.get("type"),
            "new": dl.get("new"),
            "old": dl.get("old"),
            "text": dl.get("text"),
            "old_text": dl.get("old_text"),
        }
        pos = dl.get("new") if t in ("added", "modified") else dl.get("old")
        try:
            pos = int(pos) if pos is not None else None
        except Exception:
            pos = None
        targets.append((li, pos, sig))

    if not targets:
        return False, "无可撤回变更"

    first_type = (targets[0][2].get("type") or "").lower()
    for _, __, sig in targets:
        if (sig.get("type") or "").lower() != first_type:
            return False, "多行撤回要求所有行类型相同"

    for li, pos, sig in sorted(targets, key=lambda x: (x[1] is None, x[1] if x[1] is not None else x[0]), reverse=True):
        ok, msg = revert_line(filepath, hunk_idx, li, st, ctx_lines, sig)
        if not ok:
            return False, msg

    return True, ""


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

def _has_worktree_changes():
    """Return (dirty: bool, detail: str)."""
    out, err, code = run_git(["status", "--porcelain=v1"])
    if code != 0:
        return True, (err or "无法检测工作区状态")
    dirty = bool((out or "").strip())
    return dirty, (out or "")

def _branch_exists_local(branch_name: str):
    branch_name = (branch_name or "").strip()
    if not branch_name:
        return False
    _, _, code = run_git(["show-ref", "--verify", "--quiet", f"refs/heads/{branch_name}"])
    return code == 0

def switch_branch(branch_name: str):
    """Switch to a branch.

    - If working tree is dirty, refuse (consistent with safe UI behavior).
    - If selecting a remote branch (remotes/origin/foo), create a local tracking branch.
    """
    if not REPO_PATH:
        return False, None, "未打开仓库", "", True

    branch_name = (branch_name or "").strip()
    if not branch_name:
        return False, None, "缺少分支名", "", True

    dirty, detail = _has_worktree_changes()
    if dirty:
        return False, None, "工作区有未提交更改，请先提交/撤回/暂存（stash）后再切换分支", detail, True

    # Normalize
    raw = branch_name
    is_remote = raw.startswith("remotes/")
    remote_ref = raw.replace("remotes/", "", 1) if is_remote else None

    # Prefer git switch, fallback to checkout
    if is_remote and remote_ref:
        # remote_ref like origin/foo
        local_name = remote_ref
        if "/" in remote_ref:
            local_name = remote_ref.split("/", 1)[1]

        if _branch_exists_local(local_name):
            out, err, code = run_git(["switch", local_name], timeout=120)
            if code != 0:
                out, err, code = run_git(["checkout", local_name], timeout=120)
        else:
            out, err, code = run_git(["switch", "-c", local_name, "--track", remote_ref], timeout=120)
            if code != 0:
                out, err, code = run_git(["checkout", "-b", local_name, "--track", remote_ref], timeout=120)
    else:
        out, err, code = run_git(["switch", raw], timeout=120)
        if code != 0:
            out, err, code = run_git(["checkout", raw], timeout=120)

    if code != 0:
        return False, None, (err or "切换分支失败"), (out or ""), False

    # Refresh current branch
    _, cur = get_branches()
    return True, cur, "", (out or ""), False

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
            content, encoding = get_file_content(fp, return_encoding=True)
            if content is not None:
                self.send_json({"ok": True, "content": content, "encoding": encoding})
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
                head_out, _, head_code = run_git(["rev-parse", "HEAD"])
                head_full = (head_out or "").strip() if head_code == 0 else ""
                detail["is_head"] = bool(head_full and (detail.get("full_hash") == head_full or detail.get("hash") == head_full))
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
                sig = data.get("signature")
                ok, msg = revert_line(fp, int(h_idx), int(l_idx), st, ctx, sig)
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
                content, encoding = get_file_content(fp, return_encoding=True)
                if content is not None:
                    self.send_json({"ok": True, "content": content, "encoding": encoding})
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

            elif p == "/api/delete_file":
                logger.info("处理 /api/delete_file 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                fp = (data.get("path") or "").strip()
                full = _safe_repo_abspath(fp)
                if not full:
                    self.send_json({"ok": False, "msg": "非法路径"}, 400)
                    return
                try:
                    if os.path.isdir(full):
                        self.send_json({"ok": False, "msg": "目标是目录"}, 400)
                        return
                    if os.path.exists(full):
                        os.remove(full)
                    self.send_json({"ok": True, "msg": "删除成功"})
                except Exception as e:
                    logger.error(f"删除文件失败: {fp} - {e}", exc_info=True)
                    self.send_json({"ok": False, "msg": str(e)}, 500)

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
                ok, msg, full_hash = revert_commit(commit)
                self.send_json({
                    "ok": ok,
                    "msg": msg,
                    "full_hash": full_hash,
                    "hash": full_hash[:7] if full_hash else "",
                })

            elif p == "/api/soft_reset_commit":
                logger.info("处理 /api/soft_reset_commit 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return
                commit = (data.get("hash") or "").strip()
                if not commit:
                    self.send_json({"error":"缺少 hash"}, 400)
                    return

                head_out, head_err, head_code = run_git(["rev-parse", "HEAD"])
                if head_code != 0:
                    self.send_json({"error": head_err or "无法获取 HEAD"}, 400)
                    return
                head_full = (head_out or "").strip()

                if commit != head_full and commit != head_full[:7]:
                    self.send_json({"error": "仅允许撤销当前分支最新一次提交（HEAD）"}, 400)
                    return

                pushed, _, perr = is_commit_pushed(head_full)
                if perr:
                    self.send_json({"error": perr}, 400)
                    return
                if pushed:
                    self.send_json({"error": "该提交已推送到远端，无法使用软回退撤销；请使用 Revert"}, 400)
                    return

                _, err, code = run_git(["reset", "--soft", f"{head_full}^"], timeout=120)
                if code != 0:
                    self.send_json({"error": err or "软回退失败"}, 400)
                    return

                new_head_out, _, new_head_code = run_git(["rev-parse", "HEAD"])
                new_head_full = (new_head_out or "").strip() if new_head_code == 0 else ""
                self.send_json({
                    "ok": True,
                    "full_hash": new_head_full,
                    "hash": new_head_full[:7] if new_head_full else "",
                })

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
                    # Refresh remote-tracking refs so commit_push_status becomes accurate immediately
                    run_git(["fetch", "--prune"], timeout=300)
                else:
                    logger.error(f"推送失败: {err}")
                self.send_json({"ok": code == 0, "msg": err})

            elif p == "/api/pull":
                logger.info("处理 /api/pull 请求")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return

                out, err, code = run_git(["pull", "--no-edit"], timeout=300)
                output = (out or "")
                error = (err or "")

                # 检测本地修改会被覆盖的情况
                local_changes_conflict = False
                affected_files = []
                
                # Git会在error中输出类似:
                # "error: Your local changes to the following files would be overwritten by merge:"
                # 或者中文版本可能是其他提示
                if code != 0 and ("would be overwritten" in error.lower() or 
                                 "will be overwritten" in error.lower() or
                                 "本地修改" in error or
                                 "覆盖" in error):
                    local_changes_conflict = True
                    # 尝试提取受影响的文件列表
                    lines = error.split('\n')
                    in_file_list = False
                    for line in lines:
                        line = line.strip()
                        if 'would be overwritten' in line.lower() or 'will be overwritten' in line.lower():
                            in_file_list = True
                            continue
                        if in_file_list:
                            if line.startswith('Please') or line.startswith('Aborting') or not line:
                                break
                            # 去除可能的制表符或空格
                            if line and not line.startswith('error:') and not line.startswith('hint:'):
                                affected_files.append(line.strip())
                
                conflict_files, _ = get_unmerged_files()
                has_conflicts = bool(conflict_files)

                ok = (code == 0) and (not has_conflicts)
                self.send_json({
                    "ok": ok,
                    "output": output.strip(),
                    "error": error.strip(),
                    "has_conflicts": has_conflicts,
                    "conflict_files": conflict_files,
                    "local_changes_conflict": local_changes_conflict,
                    "affected_files": affected_files,
                })

            elif p == "/api/stash_and_pull":
                logger.info("处理 /api/stash_and_pull 请求 (暂存修改并更新)")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return

                # 1. git stash
                stash_out, stash_err, stash_code = run_git(["stash", "push", "-m", "Auto stash before pull"], timeout=60)
                if stash_code != 0:
                    logger.error(f"暂存失败: {stash_err}")
                    self.send_json({"error": f"暂存失败: {stash_err}"}, 400)
                    return
                
                # 检查是否真的有内容被暂存（如果工作区干净，stash不会创建新条目）
                stashed = "No local changes to save" not in (stash_out or "")
                
                # 2. git pull
                pull_out, pull_err, pull_code = run_git(["pull", "--no-edit"], timeout=300)
                
                # 3. git stash pop (只有在实际暂存了内容时才恢复)
                pop_conflict = False
                pop_err = ""
                if stashed:
                    pop_out, pop_err_raw, pop_code = run_git(["stash", "pop"], timeout=60)
                    pop_err = pop_err_raw or ""
                    # 检测stash pop是否产生冲突
                    if pop_code != 0 or "CONFLICT" in (pop_out or "") or "CONFLICT" in pop_err:
                        pop_conflict = True
                
                # 检查合并冲突
                conflict_files, _ = get_unmerged_files()
                has_conflicts = bool(conflict_files) or pop_conflict
                
                ok = (pull_code == 0) and (not has_conflicts)
                
                response = {
                    "ok": ok,
                    "stashed": stashed,
                    "pull_output": (pull_out or "").strip(),
                    "pull_error": (pull_err or "").strip(),
                    "has_conflicts": has_conflicts,
                    "conflict_files": conflict_files,
                }
                
                if pop_conflict:
                    response["pop_conflict"] = True
                    response["pop_error"] = pop_err.strip()
                    response["message"] = "更新成功，但恢复暂存的修改时发生冲突，请手动解决冲突"
                elif ok:
                    response["message"] = "成功暂存修改、更新并恢复修改"
                
                self.send_json(response)

            elif p == "/api/commit_and_pull":
                logger.info("处理 /api/commit_and_pull 请求 (提交并更新)")
                if not REPO_PATH:
                    self.send_json({"error":"未打开仓库"}, 400)
                    return

                commit_msg = (data.get("message") or "").strip()
                if not commit_msg:
                    self.send_json({"error": "提交信息不能为空"}, 400)
                    return

                # 1. git add -A (暂存所有修改)
                add_out, add_err, add_code = run_git(["add", "-A"], timeout=60)
                if add_code != 0:
                    logger.error(f"暂存文件失败: {add_err}")
                    self.send_json({"error": f"暂存文件失败: {add_err}"}, 400)
                    return

                # 2. git commit
                commit_out, commit_err, commit_code = run_git(["commit", "-m", commit_msg], timeout=60)
                if commit_code != 0:
                    logger.error(f"提交失败: {commit_err}")
                    self.send_json({"error": f"提交失败: {commit_err}"}, 400)
                    return

                # 3. git pull
                pull_out, pull_err, pull_code = run_git(["pull", "--no-edit"], timeout=300)
                
                # 检查合并冲突
                conflict_files, _ = get_unmerged_files()
                has_conflicts = bool(conflict_files)
                
                ok = (pull_code == 0) and (not has_conflicts)
                
                self.send_json({
                    "ok": ok,
                    "commit_output": (commit_out or "").strip(),
                    "pull_output": (pull_out or "").strip(),
                    "pull_error": (pull_err or "").strip(),
                    "has_conflicts": has_conflicts,
                    "conflict_files": conflict_files,
                    "message": "成功提交并更新" if ok else "提交成功但更新时发生冲突"
                })

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
    