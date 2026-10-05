import os
import io
import re
import sys
import time
import json
import base64
import logging
import atexit
import queue
import threading
import subprocess
import ctypes
import unicodedata
from tkinter import font as tkfont
from logging.handlers import RotatingFileHandler

import requests
import pyperclip
import tkinter as tk
from pynput import mouse
import soundfile as sf
import sounddevice as sd
import numpy as np

# ============================================================
# Fast Translate — Index-Translate-2B academic EN→FA build
# Python 3.12 / Windows / llama.cpp / Kokoro / Tkinter
# ============================================================
# Tuned for:
#   • Index-Translate-2B.Q4_K_M.gguf  (Qwen3.5, official GGUF)
#   • English → Persian, academic register, greedy decoding
#   • official instTrans prompt format (源文 / 约束要求)
#   • bundled Persian BiDi + joining (no python-bidi required)
#   • selecting the same word repeatedly always works
#   • cached translations appear immediately
#   • no Tkinter calls from worker threads
# ============================================================

# ------------------------------------------------------------
# Paths / model settings
# ------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(BASE_DIR, "dictionary_cache_index2b.json")
LOG_PATH = os.path.join(BASE_DIR, "fast_translate.log")
FONT_FAMILY = "Vazir"
FONT_WEIGHT = "bold"
FONT_FILE_PATH = os.path.join(BASE_DIR, "Vazir-Bold.ttf")
FONT_PRIVATE_FLAGS = 0x10  # FR_PRIVATE

HWND_BROADCAST = 0xFFFF
WM_FONTCHANGE = 0x001D
SMTO_ABORTIFHUNG = 0x0002
OBSIDIAN_VAULT_PATH = r"L:\llama\flashcards_words"
KOKORO_DIR = r"H:\Kokoro82M"

LOCAL_API_BASE = "http://127.0.0.1:8080"
LOCAL_API_URL = f"{LOCAL_API_BASE}/v1/chat/completions"
LOCAL_HEALTH_URL = f"{LOCAL_API_BASE}/health"
MODEL_NAME = "Index-Translate-2B"
MODEL_PATH = os.path.join(BASE_DIR, "Index-Translate-2B.Q4_K_M.gguf")
LLAMA_SERVER_PATH = os.path.join(BASE_DIR, "llama-server.exe")

# Official Index-Translate language names used inside the prompt.
SOURCE_LANG_NAME = "英语"      # English
TARGET_LANG_NAME = "波斯语"    # Persian / Farsi
ACADEMIC_GENRE = "学术论文"

KOKORO_VOICE = "am_adam"
KOKORO_SAMPLE_RATE = 24000

# A real model request, unlike /health, is used for warm-up.
LLAMA_WARMUP_INTERVAL = 2.0
LLAMA_START_TIMEOUT = 45.0
SELECTION_COPY_TIMEOUT = 1.35
SELECTION_MIN_DRAG = 4

# ------------------------------------------------------------
# Logging
# ------------------------------------------------------------
logger = logging.getLogger("FastTranslate")
logger.setLevel(logging.INFO)
try:
    handler = RotatingFileHandler(
        LOG_PATH,
        maxBytes=1_500_000,
        backupCount=2,
        encoding="utf-8",
    )
    handler.setFormatter(logging.Formatter("%(asctime)s | %(levelname)s | %(message)s"))
    logger.addHandler(handler)
except Exception:
    pass


def log_info(message):
    try:
        logger.info(message)
    except Exception:
        pass
    try:
        print(message)
    except Exception:
        pass


def log_error(message, exc=None):
    try:
        if exc:
            logger.exception(message)
        else:
            logger.error(message)
    except Exception:
        pass
    try:
        print(f"ERROR: {message}")
    except Exception:
        pass


# ------------------------------------------------------------
# Windows helpers
# ------------------------------------------------------------
user32 = ctypes.windll.user32 if os.name == "nt" else None
kernel32 = ctypes.windll.kernel32 if os.name == "nt" else None

VK_CONTROL = 0x11
VK_C = 0x43
KEYEVENTF_KEYUP = 0x0002
GA_ROOT = 2
SW_RESTORE = 9
MONITOR_DEFAULTTONEAREST = 2


class POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class RECT(ctypes.Structure):
    _fields_ = [
        ("left", ctypes.c_long),
        ("top", ctypes.c_long),
        ("right", ctypes.c_long),
        ("bottom", ctypes.c_long),
    ]


class MONITORINFO(ctypes.Structure):
    _fields_ = [
        ("cbSize", ctypes.c_ulong),
        ("rcMonitor", RECT),
        ("rcWork", RECT),
        ("dwFlags", ctypes.c_ulong),
    ]


def is_windows():
    return os.name == "nt" and user32 is not None


def get_foreground_window():
    if not is_windows():
        return 0
    try:
        return int(user32.GetForegroundWindow())
    except Exception:
        return 0


def is_window_valid(hwnd):
    if not is_windows():
        return False
    try:
        return bool(hwnd) and bool(user32.IsWindow(hwnd))
    except Exception:
        return False


def get_window_title(hwnd):
    if not is_window_valid(hwnd):
        return ""
    try:
        length = int(user32.GetWindowTextLengthW(hwnd))
        buf = ctypes.create_unicode_buffer(max(length + 1, 1))
        user32.GetWindowTextW(hwnd, buf, len(buf))
        return buf.value
    except Exception:
        return ""


def get_root_window(hwnd):
    if not is_window_valid(hwnd):
        return 0
    try:
        return int(user32.GetAncestor(hwnd, GA_ROOT))
    except Exception:
        return hwnd


def window_from_screen_point(x, y):
    """Get the top-level window directly under the pointer."""
    if not is_windows():
        return 0
    try:
        point = POINT(int(x), int(y))
        hwnd = int(user32.WindowFromPoint(point))
        return get_root_window(hwnd)
    except Exception:
        return 0


def get_monitor_work_area(x, y):
    """Return the work area of the physical monitor containing screen point (x, y)."""
    if not is_windows():
        try:
            return (
                0,
                0,
                int(root.winfo_screenwidth()),
                int(root.winfo_screenheight()),
            )
        except Exception:
            return (0, 0, 1920, 1080)

    try:
        point = POINT(int(x), int(y))
        monitor = user32.MonitorFromPoint(
            point,
            MONITOR_DEFAULTTONEAREST,
        )
        if not monitor:
            raise RuntimeError("MonitorFromPoint returned NULL")

        info = MONITORINFO()
        info.cbSize = ctypes.sizeof(MONITORINFO)

        if not user32.GetMonitorInfoW(
            monitor,
            ctypes.byref(info),
        ):
            raise RuntimeError("GetMonitorInfoW failed")

        work = info.rcWork
        return (
            int(work.left),
            int(work.top),
            int(work.right),
            int(work.bottom),
        )
    except Exception as exc:
        log_error("Could not determine monitor work area.", exc)
        try:
            screen_w = int(root.winfo_screenwidth())
            screen_h = int(root.winfo_screenheight())
        except Exception:
            screen_w, screen_h = 1920, 1080
        return (0, 0, screen_w, screen_h)


def place_popup_near_screen_point(x, y, width, height, offset=14, margin=8):
    """Place the popup near the selection point, constrained to that same monitor."""
    left, top, right, bottom = get_monitor_work_area(x, y)

    max_left = max(left + margin, right - width - margin)
    max_top = max(top + margin, bottom - height - margin)

    popup_left = min(
        max(left + margin, int(x + offset)),
        max_left,
    )
    popup_top = min(
        max(top + margin, int(y + offset)),
        max_top,
    )

    return popup_left, popup_top


def bring_to_foreground(hwnd):
    """Focus the source window without changing its maximized/restored state."""
    if not is_window_valid(hwnd):
        return False

    # IMPORTANT: never call SW_RESTORE on an already-maximized window.
    try:
        if user32.IsIconic(hwnd):
            user32.ShowWindow(hwnd, SW_RESTORE)
    except Exception:
        pass

    try:
        user32.BringWindowToTop(hwnd)
    except Exception:
        pass

    try:
        user32.SetForegroundWindow(hwnd)
        time.sleep(0.035)
        return get_foreground_window() == hwnd
    except Exception:
        return False


def send_ctrl_c(target_hwnd):
    """Send Ctrl+C only to the verified source application."""
    if not is_windows() or not is_window_valid(target_hwnd):
        return False

    title = get_window_title(target_hwnd).upper()
    if "IDLE" in title or "PYTHON SHELL" in title:
        log_info("Selection skipped: Python IDLE/Shell detected as target.")
        return False

    if not bring_to_foreground(target_hwnd):
        log_info("Selection skipped: source window could not be focused safely.")
        return False

    try:
        user32.keybd_event(VK_CONTROL, 0, 0, 0)
        user32.keybd_event(VK_C, 0, 0, 0)
        time.sleep(0.025)
        user32.keybd_event(VK_C, 0, KEYEVENTF_KEYUP, 0)
        user32.keybd_event(VK_CONTROL, 0, KEYEVENTF_KEYUP, 0)
        return True
    except Exception as exc:
        log_error("Ctrl+C injection failed.", exc)
        return False


def get_clipboard_sequence_number():
    if not is_windows():
        return None
    try:
        return int(user32.GetClipboardSequenceNumber())
    except Exception:
        return None


def clipboard_copy_text(text, attempts=5):
    for _ in range(attempts):
        try:
            pyperclip.copy(text)
            return True
        except Exception:
            time.sleep(0.025)
    return False


def clipboard_read_text():
    try:
        return pyperclip.paste()
    except Exception:
        return ""


# ------------------------------------------------------------
# Global application state
# ------------------------------------------------------------
root = None
text_area = None
source_label = None
btn_tts = None
btn_obsidian = None
status_label = None

popup_visible = False
p_left = 0
p_top = 0
p_width = 360
p_height = 145

current_word = ""
current_translation = ""
is_single_word = False

gui_queue = queue.Queue()
MAIN_THREAD_ID = None

selection_state_lock = threading.Lock()
selection_request_id = 0
selection_target_hwnd = 0
selection_clipboard_lock = threading.Lock()

is_dragging = False
start_x = 0
start_y = 0
mouse_listener = None
root_hwnd = 0
UI_FONT_FAMILY = "Tahoma"

cache_data = {}
cache_lock = threading.RLock()
cache_write_lock = threading.Lock()

llama_process = None
owns_llama_process = False
llama_request_lock = threading.Lock()
llama_ready = threading.Event()
llama_shutdown = threading.Event()

kokoro_pipeline = None
kokoro_lock = threading.Lock()
tts_lock = threading.RLock()
tts_playing = False
tts_stop_event = threading.Event()
tts_session_id = 0
audio_inflight_lock = threading.Lock()
audio_inflight = set()


# ------------------------------------------------------------
# Generic helpers
# ------------------------------------------------------------
def normalize_key(text):
    """Stable cache key while preserving the original source text separately."""
    return unicodedata.normalize("NFKC", text or "").strip().casefold()


def clean_source_text(text):
    text = unicodedata.normalize("NFC", text or "")
    text = text.replace("\x00", "")
    return text.strip()


def clean_model_result(result):
    """Strip Index-Translate / Qwen3.5 thinking blocks and leftover wrappers."""
    result = (result or "").strip()
    if not result:
        return ""

    lower = result.lower()
    if "</think>" in lower:
        idx = lower.rfind("</think>")
        result = result[idx + len("</think>"):].strip()
    for opener in ("<think>", "<｜hy_Assistant｜>", "<|hy_Assistant|>", "<|im_start|>assistant"):
        if result.startswith(opener):
            result = result[len(opener):].strip()
    result = result.replace("<think>", "").replace("</think>", "").strip()

    # Drop a leading "translation:" style label if the model slips one in.
    result = re.sub(
        r"^(?:translation|translated text|译文|ترجمه)\s*[:：]\s*",
        "",
        result,
        count=1,
        flags=re.IGNORECASE,
    ).strip()

    if len(result) >= 2 and result.startswith('"') and result.endswith('"'):
        result = result[1:-1].strip()
    if len(result) >= 2 and result.startswith("«") and result.endswith("»"):
        result = result[1:-1].strip()
    return result


def run_background(target, *args, name=None):
    thread = threading.Thread(target=target, args=args, daemon=True, name=name)
    thread.start()
    return thread


# ------------------------------------------------------------
# Cache subsystem
# ------------------------------------------------------------
def init_cache():
    global cache_data
    if not os.path.exists(JSON_PATH):
        with cache_lock:
            cache_data = {}
        save_json_file()
        return

    try:
        with open(JSON_PATH, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if not isinstance(raw, dict):
            raise ValueError("Cache root is not an object")
        with cache_lock:
            cache_data = raw
        log_info(f"Cache loaded: {len(cache_data)} entries")
    except Exception as exc:
        log_error("Cache file is invalid; creating a fresh cache.", exc)
        try:
            corrupt = JSON_PATH + f".corrupt-{int(time.time())}"
            os.replace(JSON_PATH, corrupt)
        except Exception:
            pass
        with cache_lock:
            cache_data = {}
        save_json_file()


def save_json_file():
    """Atomic JSON save. Never writes a half-complete dictionary cache."""
    with cache_write_lock:
        try:
            with cache_lock:
                snapshot = dict(cache_data)

            directory = os.path.dirname(JSON_PATH) or "."
            temp_path = os.path.join(directory, ".dictionary_cache_index2b.tmp")
            with open(temp_path, "w", encoding="utf-8") as f:
                json.dump(snapshot, f, ensure_ascii=False, indent=2)
                f.flush()
                try:
                    os.fsync(f.fileno())
                except Exception:
                    pass
            os.replace(temp_path, JSON_PATH)
        except Exception as exc:
            log_error("Could not save dictionary cache.", exc)


def schedule_cache_save():
    run_background(save_json_file, name="CacheWriter")


def get_cached_entry(text):
    key = normalize_key(text)
    if not key:
        return None
    legacy_key = (text or "").strip().lower()
    with cache_lock:
        value = cache_data.get(key)
        if value is None and legacy_key != key:
            value = cache_data.get(legacy_key)
        if isinstance(value, str):
            return {"translation": value}
        if isinstance(value, dict):
            return dict(value)
    return None


def get_cached_translation(text):
    entry = get_cached_entry(text)
    if not entry:
        return None
    value = entry.get("translation")
    if isinstance(value, str) and value.strip():
        return value.strip()
    return None


def get_cached_audio_b64(text):
    entry = get_cached_entry(text)
    if not entry:
        return None
    value = entry.get("audio_b64")
    return value if isinstance(value, str) and value else None


def safe_filename(text):
    value = normalize_key(text)
    value = re.sub(r'[<>:"/\\|?*\x00-\x1f]', '_', value)
    value = value.rstrip(" .") or "card"
    reserved = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}
    if value.upper() in reserved:
        value = f"_{value}"
    return value[:120]


def save_translation_to_cache(source, translated):
    source = clean_source_text(source)
    translated = (translated or "").strip()
    if not source or not translated:
        return
    key = normalize_key(source)
    with cache_lock:
        old = cache_data.get(key, {})
        entry = {"translation": old} if isinstance(old, str) else dict(old or {})
        entry["source"] = source
        entry["translation"] = translated
        entry["model"] = MODEL_NAME
        cache_data[key] = entry
    schedule_cache_save()


def save_audio_to_cache(source, audio_b64):
    source = clean_source_text(source)
    if not source or not audio_b64:
        return
    key = normalize_key(source)
    with cache_lock:
        old = cache_data.get(key, {})
        entry = {"translation": old} if isinstance(old, str) else dict(old or {})
        entry["source"] = source
        entry["audio_b64"] = audio_b64
        entry["audio_rate"] = KOKORO_SAMPLE_RATE
        cache_data[key] = entry
    schedule_cache_save()


# ------------------------------------------------------------
# llama.cpp server  (Index-Translate-2B / Qwen3.5)
# ------------------------------------------------------------
def server_health_ok():
    try:
        response = requests.get(LOCAL_HEALTH_URL, timeout=0.8)
        return response.status_code == 200
    except Exception:
        return False


def _llama_server_cmd(with_jinja=True):
    cmd = [
        LLAMA_SERVER_PATH,
        "-m", MODEL_PATH,
        "--ctx-size", "8192",
        "--n-gpu-layers", "99",
        "--host", "127.0.0.1",
        "--port", "8080",
        "--temp", "0",
    ]
    if with_jinja:
        # Qwen3.5 chat template: thinking MUST be off or the first tokens
        # are a <think> block and translation latency explodes.
        cmd.extend([
            "--jinja",
            "--chat-template-kwargs",
            '{"enable_thinking":false}',
        ])
    return cmd


def start_llama_server():
    """Reuse a healthy server; otherwise start exactly one private server process."""
    global llama_process, owns_llama_process

    if server_health_ok():
        log_info("Existing llama-server is already healthy; reusing it.")
        owns_llama_process = False
        llama_ready.set()
        return True

    if not os.path.exists(LLAMA_SERVER_PATH):
        log_error(f"llama-server.exe not found: {LLAMA_SERVER_PATH}")
        return False
    if not os.path.exists(MODEL_PATH):
        log_error(f"Translation model not found: {MODEL_PATH}")
        return False

    creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)

    def _spawn(cmd):
        global llama_process, owns_llama_process
        llama_process = subprocess.Popen(
            cmd,
            creationflags=creationflags,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        owns_llama_process = True
        deadline = time.monotonic() + LLAMA_START_TIMEOUT
        while time.monotonic() < deadline:
            if llama_process.poll() is not None:
                return False
            if server_health_ok():
                llama_ready.set()
                log_info("llama-server is ready.")
                return True
            time.sleep(0.25)
        return False

    cmd = _llama_server_cmd(with_jinja=True)
    log_info("Starting llama-server for Index-Translate-2B (thinking disabled).")
    try:
        if _spawn(cmd):
            return True
    except Exception as exc:
        log_error("Could not start llama-server with Jinja chat template.", exc)

    if llama_process is not None and llama_process.poll() is None:
        try:
            llama_process.terminate()
            llama_process.wait(timeout=2)
        except Exception:
            pass

    log_info("Retrying llama-server without --jinja (older llama.cpp build).")
    try:
        if _spawn(_llama_server_cmd(with_jinja=False)):
            return True
    except Exception as exc:
        log_error("Could not start llama-server.", exc)
        return False

    log_error("Timed out waiting for llama-server /health.")
    return False


def llama_chat(messages, max_tokens=1024, temperature=0.0):
    if not llama_ready.is_set():
        if not server_health_ok():
            return None
        llama_ready.set()

    payload = {
        "model": MODEL_NAME,
        "messages": messages,
        "temperature": temperature,
        "top_p": 1.0,
        "max_tokens": max_tokens,
        "stream": False,
        "chat_template_kwargs": {"enable_thinking": False},
    }

    try:
        with llama_request_lock:
            response = requests.post(LOCAL_API_URL, json=payload, timeout=45)
        if response.status_code != 200:
            log_info(f"llama response HTTP {response.status_code}: {response.text[:300]}")
            return None
        data = response.json()
        message = data.get("choices", [{}])[0].get("message", {}) or {}
        content = message.get("content", "") or ""
        # Some Qwen3.5 builds park thinking in a separate field.
        if not content:
            content = message.get("reasoning_content", "") or ""
        return clean_model_result(content)
    except Exception as exc:
        log_error("llama request failed.", exc)
        return None


def build_translate_prompt(text, is_word):
    """Official Index-Translate instTrans prompt, locked to academic EN→FA."""
    source = text.strip()
    if is_word:
        return (
            f"请将以下{SOURCE_LANG_NAME}文本翻译成{TARGET_LANG_NAME}，并且严格遵循所有约束要求。\n"
            "\n"
            "【源文】\n"
            f"{source}\n"
            "\n"
            "【约束要求】\n"
            "1. 【硬性要求】这是一个单独的英语单词。按从最常见到较不常见的顺序给出多个常见波斯语（Farsi）义项，用逗号分隔。\n"
            "2. 【硬性要求】只输出波斯语译文本身，不要英语解释、音标、词性、编号或任何寒暄。\n"
            "3. 【注意】学术语境下优先给出精确、规范的对应术语。\n"
            "\n"
            "只输出译文，不要有任何额外说明。"
        )

    return (
        f"请将以下{SOURCE_LANG_NAME}{ACADEMIC_GENRE}翻译成{TARGET_LANG_NAME}，并且严格遵循所有约束要求。\n"
        "\n"
        "【源文】\n"
        f"{source}\n"
        "\n"
        "【约束要求】\n"
        "1. 【硬性要求】完整翻译全部源文，不得省略、截断、改写或概括任何部分。\n"
        "2. 【硬性要求】保留原文的编号、公式、变量名、缩写、专名、引号与标点结构。\n"
        "3. 【硬性要求】只输出波斯语（Farsi）译文，不要夹杂解释性英语或译者注。\n"
        "4. 【注意】译文必须准确、流畅，并使用规范的学术语域；术语在全文中保持前后一致。\n"
        "5. 【注意】专有名词与通行缩写（如 DNA、COVID-19、p-value）若学界通用则保留原文形式。\n"
        "\n"
        "只输出译文，不要有任何额外说明。"
    )


def translate_text(text):
    text = clean_source_text(text)
    if not text:
        return None

    cached = get_cached_translation(text)
    if cached:
        return cached

    is_word = len(text.split()) == 1
    prompt = build_translate_prompt(text, is_word)
    result = llama_chat(
        [{"role": "user", "content": prompt}],
        max_tokens=192 if is_word else 1024,
        temperature=0.0,
    )

    if result:
        save_translation_to_cache(text, result)
    return result


def llama_real_warmup():
    """Trigger a minimal actual inference; /health alone is intentionally not used."""
    prompt = (
        f"请将以下{SOURCE_LANG_NAME}文本翻译为{TARGET_LANG_NAME}，直接输出翻译结果，不要进行任何解释。\n"
        "\n"
        "OK"
    )
    result = llama_chat(
        [{"role": "user", "content": prompt}],
        max_tokens=4,
        temperature=0.0,
    )
    return bool(result is not None)


def llama_keep_warm_worker():
    next_warmup = time.monotonic()

    while not llama_shutdown.is_set():
        wait_for = max(0.0, next_warmup - time.monotonic())
        if llama_shutdown.wait(wait_for):
            break

        try:
            if server_health_ok():
                llama_real_warmup()
            else:
                time.sleep(0.25)
        except Exception as exc:
            log_error("llama warm-up loop error.", exc)

        next_warmup = time.monotonic() + LLAMA_WARMUP_INTERVAL


# ------------------------------------------------------------
# Kokoro
# ------------------------------------------------------------
def load_kokoro():
    global kokoro_pipeline
    try:
        if KOKORO_DIR not in sys.path:
            sys.path.insert(0, KOKORO_DIR)
        from kokoro import KPipeline, KModel

        device = "cpu"
        lang = KOKORO_VOICE[0] if KOKORO_VOICE else "a"

        model_path = None
        for filename in ("kokoro-v1_0.pth", "kokoro-v0_19.pth", "kokoro.pth"):
            path = os.path.join(KOKORO_DIR, filename)
            if os.path.exists(path):
                model_path = path
                break

        if not model_path and os.path.isdir(KOKORO_DIR):
            for filename in os.listdir(KOKORO_DIR):
                if filename.lower().endswith(".pth"):
                    model_path = os.path.join(KOKORO_DIR, filename)
                    break

        config_path = os.path.join(KOKORO_DIR, "config.json")
        if not model_path or not os.path.exists(config_path):
            log_info("Kokoro: local model/config not found.")
            return

        log_info(f"Loading local Kokoro from {model_path} on CPU")
        model = KModel(model=model_path, config=config_path).to(device).eval()
        kokoro_pipeline = KPipeline(
            lang_code=lang,
            model=model,
            repo_id="hexgrad/Kokoro-82M",
            device=device,
        )
        log_info("Kokoro loaded successfully on CPU (offline local model).")
    except Exception as exc:
        kokoro_pipeline = None
        log_error("Kokoro load failed.", exc)


def kokoro_generate_audio(text):
    if kokoro_pipeline is None:
        return None

    try:
        chunks = []
        voice_path = os.path.join(KOKORO_DIR, "voices", f"{KOKORO_VOICE}.pt")
        if not os.path.exists(voice_path):
            voice_path = os.path.join(KOKORO_DIR, f"{KOKORO_VOICE}.pt")

        with kokoro_lock:
            if os.path.exists(voice_path):
                try:
                    voice_data = kokoro_pipeline.load_voice(voice_path)
                except Exception:
                    voice_data = voice_path
            else:
                voice_data = KOKORO_VOICE

            generator = kokoro_pipeline(" ".join(text.split()), voice=voice_data, speed=0.92)
            for _, _, audio in generator:
                if audio is not None:
                    chunks.append(np.asarray(audio, dtype=np.float32))

        if chunks:
            return np.concatenate(chunks)
    except Exception as exc:
        log_error("Kokoro generation failed.", exc)
    return None


def audio_to_b64(audio_array):
    buffer = io.BytesIO()
    sf.write(buffer, audio_array, KOKORO_SAMPLE_RATE, format="WAV")
    return base64.b64encode(buffer.getvalue()).decode("ascii")


def b64_to_audio(b64_str):
    buffer = io.BytesIO(base64.b64decode(b64_str))
    data, _ = sf.read(buffer, dtype="float32")
    return data


def _precache_audio_when_idle(text):
    deadline = time.monotonic() + 12.0
    while time.monotonic() < deadline:
        with tts_lock:
            playing = tts_playing
        if not playing:
            break
        time.sleep(0.08)
    _precache_audio(text)


def _precache_audio(text):
    key = normalize_key(text)
    if not key or kokoro_pipeline is None:
        return

    with audio_inflight_lock:
        if key in audio_inflight:
            return
        audio_inflight.add(key)

    try:
        if get_cached_audio_b64(text):
            return
        audio = kokoro_generate_audio(text)
        if audio is not None:
            save_audio_to_cache(text, audio_to_b64(audio))
    finally:
        with audio_inflight_lock:
            audio_inflight.discard(key)


def _set_tts_icon(icon):
    if btn_tts:
        btn_tts.config(text=icon)


def _post_tts_icon(icon):
    post_to_gui(_set_tts_icon, icon)


def play_tts_async(text):
    global tts_playing, tts_stop_event, tts_session_id

    text = clean_source_text(text)
    if not text:
        return

    with tts_lock:
        if tts_playing:
            tts_stop_event.set()
            try:
                sd.stop()
            except Exception:
                pass
            tts_playing = False
            tts_session_id += 1
            _post_tts_icon("🔊")
            return

        tts_stop_event = threading.Event()
        local_stop_event = tts_stop_event
        tts_session_id += 1
        session_id = tts_session_id
        tts_playing = True

    _post_tts_icon("⏹")

    def speak_worker():
        global tts_playing
        try:
            audio = None
            cached_b64 = get_cached_audio_b64(text)
            if cached_b64:
                try:
                    audio = b64_to_audio(cached_b64)
                except Exception:
                    audio = None

            if audio is None and not local_stop_event.is_set():
                if kokoro_pipeline is not None:
                    audio = kokoro_generate_audio(text)
                    if audio is not None:
                        save_audio_to_cache(text, audio_to_b64(audio))
                else:
                    try:
                        import pyttsx3
                        engine = pyttsx3.init()
                        engine.setProperty("rate", 142)
                        engine.say(text)
                        engine.runAndWait()
                    except Exception as exc:
                        log_error("pyttsx3 playback failed.", exc)

            if audio is not None and not local_stop_event.is_set():
                try:
                    sd.play(audio, samplerate=KOKORO_SAMPLE_RATE)
                    while True:
                        if local_stop_event.is_set():
                            try:
                                sd.stop()
                            except Exception:
                                pass
                            break
                        try:
                            active = sd.get_stream().active
                        except Exception:
                            active = False
                        if not active:
                            break
                        time.sleep(0.04)
                except Exception as exc:
                    log_error("Audio playback failed.", exc)
        finally:
            with tts_lock:
                if session_id == tts_session_id:
                    tts_playing = False
                    _post_tts_icon("🔊")

    run_background(speak_worker, name="TTS")


# ------------------------------------------------------------
# Bundled Persian / Arabic display (joining + BiDi)
# Never depends on python-bidi / arabic-reshaper.
# ------------------------------------------------------------
# Each letter: (isolated, final, initial, medial)
_ARABIC_FORMS = {
    "\u0621": ("\uFE80", "\uFE80", "\uFE80", "\uFE80"),  # hamza
    "\u0622": ("\uFE81", "\uFE82", "\uFE81", "\uFE82"),  # alef madda
    "\u0623": ("\uFE83", "\uFE84", "\uFE83", "\uFE84"),  # alef hamza above
    "\u0624": ("\uFE85", "\uFE86", "\uFE85", "\uFE86"),  # waw hamza
    "\u0625": ("\uFE87", "\uFE88", "\uFE87", "\uFE88"),  # alef hamza below
    "\u0626": ("\uFE89", "\uFE8A", "\uFE8B", "\uFE8C"),  # yeh hamza
    "\u0627": ("\uFE8D", "\uFE8E", "\uFE8D", "\uFE8E"),  # alef
    "\u0628": ("\uFE8F", "\uFE90", "\uFE91", "\uFE92"),  # beh
    "\u067E": ("\uFB56", "\uFB57", "\uFB58", "\uFB59"),  # peh
    "\u062A": ("\uFE95", "\uFE96", "\uFE97", "\uFE98"),  # teh
    "\u062B": ("\uFE99", "\uFE9A", "\uFE9B", "\uFE9C"),  # theh
    "\u062C": ("\uFE9D", "\uFE9E", "\uFE9F", "\uFEA0"),  # jeem
    "\u0686": ("\uFB7A", "\uFB7B", "\uFB7C", "\uFB7D"),  # tcheh
    "\u062D": ("\uFEA1", "\uFEA2", "\uFEA3", "\uFEA4"),  # hah
    "\u062E": ("\uFEA5", "\uFEA6", "\uFEA7", "\uFEA8"),  # khah
    "\u062F": ("\uFEA9", "\uFEAA", "\uFEA9", "\uFEAA"),  # dal
    "\u0630": ("\uFEAB", "\uFEAC", "\uFEAB", "\uFEAC"),  # thal
    "\u0631": ("\uFEAD", "\uFEAE", "\uFEAD", "\uFEAE"),  # reh
    "\u0632": ("\uFEAF", "\uFEB0", "\uFEAF", "\uFEB0"),  # zain
    "\u0698": ("\uFB8A", "\uFB8B", "\uFB8A", "\uFB8B"),  # jeh
    "\u0633": ("\uFEB1", "\uFEB2", "\uFEB3", "\uFEB4"),  # seen
    "\u0634": ("\uFEB5", "\uFEB6", "\uFEB7", "\uFEB8"),  # sheen
    "\u0635": ("\uFEB9", "\uFEBA", "\uFEBB", "\uFEBC"),  # sad
    "\u0636": ("\uFEBD", "\uFEBE", "\uFEBF", "\uFEC0"),  # dad
    "\u0637": ("\uFEC1", "\uFEC2", "\uFEC3", "\uFEC4"),  # tah
    "\u0638": ("\uFEC5", "\uFEC6", "\uFEC7", "\uFEC8"),  # zah
    "\u0639": ("\uFEC9", "\uFECA", "\uFECB", "\uFECC"),  # ain
    "\u063A": ("\uFECD", "\uFECE", "\uFECF", "\uFED0"),  # ghain
    "\u0641": ("\uFED1", "\uFED2", "\uFED3", "\uFED4"),  # feh
    "\u0642": ("\uFED5", "\uFED6", "\uFED7", "\uFED8"),  # qaf
    "\u0643": ("\uFED9", "\uFEDA", "\uFEDB", "\uFEDC"),  # kaf
    "\u06A9": ("\uFB8E", "\uFB8F", "\uFB90", "\uFB91"),  # keheh
    "\u06AF": ("\uFB92", "\uFB93", "\uFB94", "\uFB95"),  # gaf
    "\u0644": ("\uFEDD", "\uFEDE", "\uFEDF", "\uFEE0"),  # lam
    "\u0645": ("\uFEE1", "\uFEE2", "\uFEE3", "\uFEE4"),  # meem
    "\u0646": ("\uFEE5", "\uFEE6", "\uFEE7", "\uFEE8"),  # noon
    "\u0647": ("\uFEE9", "\uFEEA", "\uFEEB", "\uFEEC"),  # heh
    "\u0648": ("\uFEED", "\uFEEE", "\uFEED", "\uFEEE"),  # waw
    "\u0629": ("\uFE93", "\uFE94", "\uFE93", "\uFE94"),  # teh marbuta
    "\u0649": ("\uFEEF", "\uFEF0", "\uFBE8", "\uFBE9"),  # alef maksura
    "\u064A": ("\uFEF1", "\uFEF2", "\uFEF3", "\uFEF4"),  # yeh
    "\u06CC": ("\uFBFC", "\uFBFD", "\uFBFE", "\uFBFF"),  # farsi yeh
    "\u06C0": ("\uFBA4", "\uFBA5", "\uFBA4", "\uFBA5"),  # heh yeh
    "\u06C1": ("\uFBA6", "\uFBA7", "\uFBA8", "\uFBA9"),  # heh goal
    "\u06BE": ("\uFBAA", "\uFBAB", "\uFBAC", "\uFBAD"),  # heh doachashmee
    "\u06D5": ("\uFEE9", "\uFEEA", "\uFEE9", "\uFEEA"),  # ae
}

_LAM_ALEF = {
    "\u0622": ("\uFEF5", "\uFEF6"),  # lam + alef madda  (isolated, final)
    "\u0623": ("\uFEF7", "\uFEF8"),  # lam + alef hamza above
    "\u0625": ("\uFEF9", "\uFEFA"),  # lam + alef hamza below
    "\u0627": ("\uFEFB", "\uFEFC"),  # lam + alef
}

# Dual-joining if initial form differs from isolated form.
_DUAL_JOINING = {ch for ch, forms in _ARABIC_FORMS.items() if forms[0] != forms[2]}
_RIGHT_JOINING = {ch for ch, forms in _ARABIC_FORMS.items() if forms[0] != forms[1] and forms[0] == forms[2]}
_JOINING_LETTERS = _DUAL_JOINING | _RIGHT_JOINING

_HARAKAT = set(
    "\u064B\u064C\u064D\u064E\u064F\u0650\u0651\u0652\u0653\u0654\u0655"
    "\u0656\u0657\u0658\u0670\u06D6\u06D7\u06D8\u06D9\u06DA\u06DB\u06DC"
    "\u06DF\u06E0\u06E1\u06E2\u06E3\u06E4\u06E7\u06E8\u06EA\u06EB\u06EC\u06ED"
)
_ZWNJ = "\u200C"
_ZWJ = "\u200D"
_TATWEEL = "\u0640"

_RTL_LETTERS_RE = re.compile(
    r"[\u0590-\u05FF\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF"
    r"\uFB1D-\uFDFF\uFE70-\uFEFF]"
)
_LTR_LETTERS_RE = re.compile(r"[A-Za-z\u00C0-\u024F]")
_DIGIT_RE = re.compile(r"[0-9\u06F0-\u06F9\u0660-\u0669]")


def contains_rtl(text):
    for char in text or "":
        bidi = unicodedata.bidirectional(char)
        if bidi in ("R", "AL"):
            return True
    return False


def _is_transparent(ch):
    return ch in _HARAKAT or ch in ("\u200B", "\u200E", "\u200F", "\uFEFF")


def _next_joining_letter(chars, start):
    i = start
    while i < len(chars):
        ch = chars[i]
        if ch in (_ZWNJ,):
            return None
        if ch == _ZWJ or ch == _TATWEEL or _is_transparent(ch):
            i += 1
            continue
        if ch in _JOINING_LETTERS:
            return ch
        return None
    return None


def _prev_joining_letter(chars, start):
    i = start
    while i >= 0:
        ch = chars[i]
        if ch in (_ZWNJ,):
            return None
        if ch == _ZWJ or ch == _TATWEEL or _is_transparent(ch):
            i -= 1
            continue
        if ch in _JOINING_LETTERS:
            return ch
        return None
    return None


def reshape_arabic(text):
    """Join Arabic/Persian letters into presentation forms for Tk."""
    if not text:
        return text
    chars = list(text)
    out = []
    i = 0
    while i < len(chars):
        ch = chars[i]
        if ch not in _ARABIC_FORMS:
            out.append(ch)
            i += 1
            continue

        # Lam + Alef ligature
        if ch == "\u0644":
            j = i + 1
            while j < len(chars) and _is_transparent(chars[j]):
                j += 1
            if j < len(chars) and chars[j] in _LAM_ALEF:
                held = "".join(chars[i + 1:j])  # harakat between lam and alef
                prev = _prev_joining_letter(chars, i - 1)
                joins_prev = bool(prev) and prev in _DUAL_JOINING
                lig_iso, lig_final = _LAM_ALEF[chars[j]]
                out.append(lig_final if joins_prev else lig_iso)
                if held:
                    out.append(held)
                i = j + 1
                continue

        prev = _prev_joining_letter(chars, i - 1)
        nxt = _next_joining_letter(chars, i + 1)
        joins_prev = bool(prev) and prev in _DUAL_JOINING
        joins_next = bool(nxt) and ch in _DUAL_JOINING
        iso, final, initial, medial = _ARABIC_FORMS[ch]
        if joins_prev and joins_next:
            form = medial
        elif joins_prev:
            form = final
        elif joins_next:
            form = initial
        else:
            form = iso
        out.append(form)
        i += 1
    return "".join(out)


def _bidi_class(ch):
    bidi = unicodedata.bidirectional(ch)
    if bidi in ("R", "AL"):
        return "R"
    # Letters AND numbers stay internally LTR so COVID-19 / p-value / 0.03
    # are never reversed digit-by-digit.
    if bidi in ("L", "EN", "AN"):
        return "L"
    if bidi in ("BN", "NSM"):
        return "T"
    return "O"


def _bidi_runs(text):
    """Split into strong-direction runs. Neutrals attach to neighbouring RTL in an RTL paragraph."""
    if not text:
        return []

    classes = [_bidi_class(ch) for ch in text]
    last_strong = "R"
    resolved = []
    for cls in classes:
        if cls == "T":
            resolved.append(resolved[-1] if resolved else last_strong)
        elif cls in ("L", "R"):
            last_strong = cls
            resolved.append(cls)
        else:
            resolved.append("O")

    for i, cls in enumerate(resolved):
        if cls != "O":
            continue
        prev = next((resolved[j] for j in range(i - 1, -1, -1) if resolved[j] in ("L", "R")), "R")
        nxt = next((resolved[j] for j in range(i + 1, len(resolved)) if resolved[j] in ("L", "R")), "R")
        # Hyphen / slash / period between LTR pieces (COVID-19, p-value, 0.03)
        # must stay LTR. Spaces between Persian and English attach to RTL.
        if prev == "L" and nxt == "L":
            resolved[i] = "L"
        else:
            resolved[i] = "R"

    runs = []
    start = 0
    for i in range(1, len(text) + 1):
        if i == len(text) or resolved[i] != resolved[start]:
            runs.append((resolved[start], text[start:i]))
            start = i
    return runs


def bidi_reorder(text, base_rtl=True):
    """
    Visual reorder for a Tk LTR canvas.

    RTL runs are reversed; LTR letters and numbers stay in logical order so
    'COVID-19' and 'p = 0.03' never come out backwards.
    """
    if not text:
        return text
    runs = _bidi_runs(text)
    visual_parts = []
    for cls, chunk in runs:
        if cls == "R":
            visual_parts.append(chunk[::-1])
        else:
            visual_parts.append(chunk)
    if base_rtl:
        visual_parts.reverse()
    return "".join(visual_parts)


def fix_bidi_text(text):
    """
    Prepare Persian/English mixed text for Tkinter.

    Windows Tk Text already uses Uniscribe for joining AND wrapping.
    If we reshape + visually reverse a wrapping widget, lines come out
    scrambled (the exact garbage in the popup). On Windows we only mark
    the paragraph as RTL with RLE/PDF and leave glyphs to the OS.

    On Linux/mac, Tk has no Uniscribe, so we still reshape and
    visually reorder each logical line.
    """
    text = unicodedata.normalize("NFC", text or "")
    if not text:
        return ""

    output_lines = []
    for line in text.split("\n"):
        if not line:
            output_lines.append("")
            continue
        if not contains_rtl(line):
            output_lines.append(line)
            continue
        try:
            if os.name == "nt":
                # RIGHT-TO-LEFT EMBEDDING ... POP DIRECTIONAL FORMATTING
                output_lines.append("\u202B" + line + "\u202C")
            else:
                reshaped = reshape_arabic(line)
                visual = bidi_reorder(reshaped, base_rtl=True)
                output_lines.append("\u202D" + visual + "\u202C")
        except Exception as exc:
            log_error("Bundled BiDi pass failed; showing raw line.", exc)
            output_lines.append("\u202B" + line + "\u202C")
    return "\n".join(output_lines)


def load_bidi_support():
    """Windows: OS-native RTL. Other OS: bundled joining + visual reorder."""
    if os.name == "nt":
        log_info("BiDi: Windows Uniscribe path (logical Persian, RLE mark, no reverse).")
    else:
        log_info("BiDi: bundled Persian joining + visual reorder.")


# ------------------------------------------------------------
# Font / rounded paper window
# ------------------------------------------------------------
def load_custom_font():
    """Register the local Vazir TTF and select its real Tk family name."""
    global FONT_FAMILY

    if root is None:
        return

    if not os.path.exists(FONT_FILE_PATH):
        log_info(f"Font file not found: {FONT_FILE_PATH}")
        FONT_FAMILY = "Tahoma"
        return

    if is_windows():
        try:
            add_font = getattr(ctypes.windll.gdi32, "AddFontResourceExW", None)
            if add_font is not None:
                add_font.argtypes = [
                    ctypes.c_wchar_p,
                    ctypes.c_uint,
                    ctypes.c_void_p,
                ]
                add_font.restype = ctypes.c_int
                added = int(add_font(FONT_FILE_PATH, FONT_PRIVATE_FLAGS, None))
            else:
                added = int(ctypes.windll.gdi32.AddFontResourceW(FONT_FILE_PATH))

            if added > 0:
                try:
                    ctypes.windll.user32.SendMessageTimeoutW(
                        HWND_BROADCAST,
                        WM_FONTCHANGE,
                        0,
                        0,
                        SMTO_ABORTIFHUNG,
                        1000,
                        None,
                    )
                except Exception:
                    pass

                root.update_idletasks()
                time.sleep(0.12)
                log_info(f"Registered local font: {os.path.basename(FONT_FILE_PATH)}")
            else:
                log_info(f"Windows could not register font: {FONT_FILE_PATH}")

        except Exception as exc:
            log_error("Could not register local Vazir font.", exc)

    try:
        families = set(tkfont.families(root))

        if "Vazir" in families:
            FONT_FAMILY = "Vazir"
            log_info("Using UI font: family='Vazir', weight='bold'")
        elif FONT_FAMILY in families:
            log_info(f"Using UI font: {FONT_FAMILY!r}")
        else:
            log_info(
                "Vazir is not visible to Tk after registration; "
                "Tk will use Tahoma as fallback."
            )
            FONT_FAMILY = "Tahoma"

    except Exception as exc:
        log_error("Could not inspect registered Tk fonts.", exc)
        FONT_FAMILY = "Tahoma"


def apply_rounded_corners(window, radius=22):
    if not is_windows():
        return
    try:
        window.update_idletasks()
        width = max(window.winfo_width(), 1)
        height = max(window.winfo_height(), 1)
        hrgn = ctypes.windll.gdi32.CreateRoundRectRgn(
            0, 0, width + 1, height + 1, radius, radius
        )
        user32.SetWindowRgn(window.winfo_id(), hrgn, True)
    except Exception:
        pass


# ------------------------------------------------------------
# GUI queue
# ------------------------------------------------------------
def post_to_gui(callback, *args):
    gui_queue.put((callback, args))


def process_gui_queue():
    if root is None:
        return

    while True:
        try:
            callback, args = gui_queue.get_nowait()
        except queue.Empty:
            break

        try:
            callback(*args)
        except Exception as exc:
            log_error(f"GUI callback failed: {getattr(callback, '__name__', callback)}", exc)

    try:
        root.after(20, process_gui_queue)
    except Exception:
        pass


# ------------------------------------------------------------
# GUI state / rendering
# ------------------------------------------------------------
PALETTE = {
    "bg_outer": "#0D0D1A",
    "bg_main": "#12121F",
    "bg_sidebar": "#0A0A15",
    "bg_header": "#1A1A2E",
    "text_primary": "#E8E3FF",
    "text_secondary": "#9B8FCC",
    "accent_blue": "#7B9CF4",
    "accent_purple": "#A78BFA",
    "accent_green": "#6EE7B7",
    "accent_yellow": "#FDE68A",
    "accent_pink": "#F9A8D4",
    "btn_disabled": "#2D2B45",
    "separator": "#1E1E35",
}


def set_text(text, tag="translation"):
    if not text_area:
        return
    text_area.config(state="normal")
    text_area.delete("1.0", tk.END)
    text_area.insert(tk.END, text)
    if text:
        text_area.tag_add(tag, "1.0", tk.END)
    text_area.config(state="disabled")


def set_source_label(text):
    return


def set_status(text):
    return


def update_action_buttons():
    if not btn_tts or not btn_obsidian:
        return
    if current_word:
        btn_tts.config(fg=PALETTE["accent_blue"], cursor="hand2")
    else:
        btn_tts.config(fg=PALETTE["btn_disabled"], cursor="arrow")

    if is_single_word and current_word and current_translation:
        btn_obsidian.config(fg=PALETTE["accent_green"], cursor="hand2")
    else:
        btn_obsidian.config(fg=PALETTE["btn_disabled"], cursor="arrow")


def auto_fit_window():
    global p_width, p_height, p_left, p_top
    if root is None or text_area is None:
        return

    try:
        root.update_idletasks()
        line_count = max(1, int(float(text_area.index("end-1c").split(".")[0])))
        line_height = 25 if is_single_word else 23
        target = 132 + min(line_count, 8) * line_height
        p_height = max(140, min(target, 320))
        p_width = max(320, min(p_width, 420))
        root.geometry(f"{p_width}x{p_height}+{p_left}+{p_top}")
        apply_rounded_corners(root, 20)
    except Exception as exc:
        log_error("Auto-fit failed.", exc)


def hide_popup():
    global popup_visible
    if root and popup_visible:
        try:
            root.withdraw()
        except Exception:
            pass
        popup_visible = False


def show_loading(request_id):
    if request_id != selection_request_id:
        return
    set_text(fix_bidi_text("در حال ترجمه…"), "loading")
    set_status("در حال پردازش")
    auto_fit_window()


def show_translation_result(request_id, selected_text, result, from_cache=False):
    global current_translation

    if request_id != selection_request_id:
        return
    if normalize_key(current_word) != normalize_key(selected_text):
        return

    if not result:
        current_translation = "ترجمه انجام نشد."
        set_text(fix_bidi_text(current_translation), "error")
        set_status("خطا")
        update_action_buttons()
        auto_fit_window()
        return

    current_translation = result
    visual = fix_bidi_text(result)
    tag = "word_translation" if is_single_word else "phrase_translation"
    set_text(visual, tag)
    set_status("از کش" if from_cache else "آماده")
    update_action_buttons()
    auto_fit_window()

    if is_single_word and kokoro_pipeline is not None and not get_cached_audio_b64(current_word):
        run_background(_precache_audio_when_idle, current_word, name="AudioPrecache")


def _accept_selection(mx, my, selected_text, request_id):
    global popup_visible, p_left, p_top, p_height
    global current_word, current_translation, is_single_word

    if request_id != selection_request_id:
        return

    selected_text = clean_source_text(selected_text)
    if not selected_text:
        return

    current_word = selected_text
    current_translation = ""
    is_single_word = len(selected_text.split()) == 1

    p_height = 140

    try:
        popup_w = max(320, min(p_width, 420))
        p_left, p_top = place_popup_near_screen_point(
            mx,
            my,
            popup_w,
            p_height,
            offset=14,
            margin=8,
        )
    except Exception as exc:
        log_error("Could not position translation popup on the selection monitor.", exc)
        p_left = int(mx + 14)
        p_top = int(my + 14)

    source_preview = selected_text.replace("\n", " ").strip()
    if len(source_preview) > 80:
        source_preview = source_preview[:77] + "…"
    set_source_label(source_preview)
    set_status("بررسی کش…")
    show_loading(request_id)
    update_action_buttons()

    root.geometry(f"{p_width}x{p_height}+{p_left}+{p_top}")
    apply_rounded_corners(root, 22)
    root.deiconify()
    popup_visible = True

    if is_single_word:
        play_tts_async(current_word)

    cached = get_cached_translation(selected_text)
    if cached:
        show_translation_result(request_id, selected_text, cached, True)
        return

    def translate_worker():
        result = translate_text(selected_text)
        post_to_gui(show_translation_result, request_id, selected_text, result, False)

    run_background(translate_worker, name=f"Translate-{request_id}")


# ------------------------------------------------------------
# Clipboard selection workflow
# ------------------------------------------------------------
def process_selection_worker(mx, my, target_hwnd, request_id):
    """Copy the selected source text without touching Tkinter."""
    old_clipboard = ""
    marker = f"__FAST_TRANSLATE_{time.time_ns()}__"
    marker_seq = None

    with selection_clipboard_lock:
        try:
            with selection_state_lock:
                if request_id != selection_request_id:
                    return

            old_clipboard = clipboard_read_text()

            if target_hwnd and root_hwnd and get_root_window(target_hwnd) == root_hwnd:
                return

            time.sleep(0.035)

            if not clipboard_copy_text(marker):
                log_info("Could not place clipboard marker; selection aborted safely.")
                return

            marker_seq = get_clipboard_sequence_number()

            if not send_ctrl_c(target_hwnd):
                return

            selected_text = ""
            deadline = time.monotonic() + SELECTION_COPY_TIMEOUT

            while time.monotonic() < deadline:
                with selection_state_lock:
                    if request_id != selection_request_id:
                        return

                candidate = clean_source_text(clipboard_read_text())
                current_seq = get_clipboard_sequence_number()

                if candidate and candidate != marker:
                    if marker_seq is None or current_seq is None or current_seq != marker_seq:
                        selected_text = candidate
                        break
                time.sleep(0.035)

            if selected_text:
                post_to_gui(_accept_selection, mx, my, selected_text, request_id)
        except Exception as exc:
            log_error("Selection worker failed.", exc)
        finally:
            clipboard_copy_text(old_clipboard)


# ------------------------------------------------------------
# Global mouse listener
# ------------------------------------------------------------
def popup_contains(x, y):
    if not popup_visible:
        return False
    try:
        return (
            p_left <= x <= p_left + p_width
            and p_top <= y <= p_top + p_height
        )
    except Exception:
        return False


def on_click(x, y, button, pressed):
    global is_dragging, start_x, start_y, selection_target_hwnd, selection_request_id

    try:
        if button != mouse.Button.left:
            return

        if pressed:
            start_x, start_y = x, y
            target = window_from_screen_point(x, y)
            if not target:
                target = get_foreground_window()
            selection_target_hwnd = target

            if popup_contains(x, y):
                is_dragging = False
                return

            if popup_visible:
                post_to_gui(hide_popup)

            is_dragging = True
            return

        if not is_dragging:
            return

        is_dragging = False
        dx = abs(x - start_x)
        dy = abs(y - start_y)
        if dx < SELECTION_MIN_DRAG and dy < SELECTION_MIN_DRAG:
            return

        with selection_state_lock:
            selection_request_id += 1
            request_id = selection_request_id

        hwnd = selection_target_hwnd
        run_background(
            process_selection_worker,
            x,
            y,
            hwnd,
            request_id,
            name=f"Selection-{request_id}",
        )
    except Exception as exc:
        log_error("Mouse callback failed.", exc)


def start_mouse_listener():
    global mouse_listener
    try:
        mouse_listener = mouse.Listener(on_click=on_click)
        mouse_listener.start()
        log_info("Global mouse listener started.")
    except Exception as exc:
        log_error("Could not start mouse listener.", exc)


# ------------------------------------------------------------
# Obsidian flashcard
# ------------------------------------------------------------
def create_obsidian_flashcard():
    if not is_single_word or not current_word or not current_translation:
        return

    try:
        os.makedirs(OBSIDIAN_VAULT_PATH, exist_ok=True)
        filename = f"{safe_filename(current_word)}.md"
        file_path = os.path.join(OBSIDIAN_VAULT_PATH, filename)

        if os.path.exists(file_path):
            set_status("فلش‌کارت از قبل وجود دارد")
            return

        with open(file_path, "w", encoding="utf-8") as f:
            f.write(f"Q |{current_word}|\n")
            f.write(f"A |{current_translation}|\n")

        if btn_obsidian:
            btn_obsidian.config(fg=PALETTE["accent_blue"])
        set_status("فلش‌کارت ذخیره شد")
        root.after(900, update_action_buttons)
    except Exception as exc:
        log_error("Could not create Obsidian flashcard.", exc)
        set_status("ذخیره انجام نشد")


# ------------------------------------------------------------
# Tooltip
# ------------------------------------------------------------
def add_tooltip(widget, text):
    tip = {"window": None}

    def show(_event=None):
        if tip["window"] is not None:
            return
        try:
            x = widget.winfo_rootx() - 72
            y = widget.winfo_rooty() + widget.winfo_height() + 5
            win = tk.Toplevel(widget)
            win.overrideredirect(True)
            win.attributes("-topmost", True)
            win.configure(bg=PALETTE["text_primary"])
            label = tk.Label(
                win,
                text=text,
                bg=PALETTE["text_primary"],
                fg=PALETTE["bg_main"],
                font=("Segoe UI", 8),
                padx=7,
                pady=4,
            )
            label.pack()
            win.geometry(f"+{x}+{y}")
            tip["window"] = win
        except Exception:
            pass

    def hide(_event=None):
        win = tip.get("window")
        if win is not None:
            try:
                win.destroy()
            except Exception:
                pass
            tip["window"] = None

    widget.bind("<Enter>", show, add="+")
    widget.bind("<Leave>", hide, add="+")


def on_enter_obs(_event=None):
    if btn_obsidian:
        btn_obsidian.config(bg="#1C1C30")


def on_leave_obs(_event=None):
    if btn_obsidian:
        btn_obsidian.config(bg=PALETTE["bg_sidebar"])


# ------------------------------------------------------------
# GUI construction
# ------------------------------------------------------------
def setup_gui():
    global root, root_hwnd, text_area, btn_tts, btn_obsidian, MAIN_THREAD_ID

    MAIN_THREAD_ID = threading.get_ident()

    root = tk.Tk()
    root.title("Fast Translate")
    root.overrideredirect(True)
    root.attributes("-topmost", True)
    root.geometry(f"{p_width}x{p_height}-2000-2000")
    root.configure(bg=PALETTE["bg_outer"])

    root.update_idletasks()
    root_hwnd = int(root.winfo_id())
    load_custom_font()
    try:
        if FONT_FAMILY not in set(tkfont.families(root)):
            log_info(f"Warning: {FONT_FAMILY!r} is not installed; Tk will render with its fallback font.")
    except Exception:
        pass

    main_frame = tk.Frame(root, bg=PALETTE["bg_main"], bd=0)
    main_frame.pack(fill="both", expand=True, padx=1, pady=1)

    header = tk.Frame(main_frame, bg=PALETTE["bg_header"], height=28)
    header.pack(fill="x", side="top")
    header.pack_propagate(False)

    dot_frame = tk.Frame(header, bg=PALETTE["bg_header"])
    dot_frame.pack(side="left", padx=10, pady=0)

    for color in ("#FF5F56", "#FFBD2E", "#27C93F"):
        tk.Label(
            dot_frame, text="●", font=("Segoe UI", 8),
            fg=color, bg=PALETTE["bg_header"]
        ).pack(side="left", padx=2, pady=7)

    tk.Label(
        header, text="✦  Fast Translate  ✦",
        font=("Segoe UI", 8, "bold"),
        fg=PALETTE["text_secondary"],
        bg=PALETTE["bg_header"],
    ).pack(side="left", padx=4)

    close_btn = tk.Label(
        header, text="✕", font=("Segoe UI", 9, "bold"),
        fg=PALETTE["text_secondary"], bg=PALETTE["bg_header"],
        cursor="hand2"
    )
    close_btn.pack(side="right", padx=10)
    close_btn.bind("<Button-1>", lambda _e: hide_popup())
    close_btn.bind("<Enter>", lambda _e: close_btn.config(fg=PALETTE["accent_pink"]))
    close_btn.bind("<Leave>", lambda _e: close_btn.config(fg=PALETTE["text_secondary"]))

    tk.Frame(main_frame, bg=PALETTE["accent_purple"], height=1).pack(fill="x", side="top")

    content_frame = tk.Frame(main_frame, bg=PALETTE["bg_main"])
    content_frame.pack(fill="both", expand=True)

    sidebar = tk.Frame(content_frame, bg=PALETTE["bg_sidebar"], width=44)
    sidebar.pack(side="right", fill="y")
    sidebar.pack_propagate(False)

    tk.Frame(content_frame, bg=PALETTE["separator"], width=1).pack(side="right", fill="y")

    btn_tts = tk.Label(
        sidebar, text="🔊", font=("Segoe UI Emoji", 12),
        bg=PALETTE["bg_sidebar"], fg=PALETTE["accent_blue"], cursor="hand2"
    )
    btn_tts.pack(side="top", fill="x", pady=(11, 5))
    btn_tts.bind("<Button-1>", lambda _e: play_tts_async(current_word))

    btn_obsidian = tk.Label(
        sidebar, text="📝", font=("Segoe UI Emoji", 12),
        bg=PALETTE["bg_sidebar"], fg=PALETTE["accent_green"], cursor="hand2"
    )
    btn_obsidian.pack(side="top", fill="x", pady=5)
    btn_obsidian.bind("<Button-1>", lambda _e: create_obsidian_flashcard())

    btn_tts.bind("<Enter>", lambda _e: btn_tts.config(bg="#1C1C30"), add="+")
    btn_tts.bind("<Leave>", lambda _e: btn_tts.config(bg=PALETTE["bg_sidebar"]), add="+")
    btn_obsidian.bind("<Enter>", lambda _e: on_enter_obs(None), add="+")
    btn_obsidian.bind("<Leave>", lambda _e: on_leave_obs(None), add="+")
    add_tooltip(btn_tts, "پخش / توقف")
    add_tooltip(btn_obsidian, "ذخیره فلش‌کارت")

    text_area = tk.Text(
        content_frame,
        font=(FONT_FAMILY, 13, FONT_WEIGHT),
        fg=PALETTE["text_primary"],
        bg=PALETTE["bg_main"],
        insertbackground=PALETTE["bg_main"],
        relief="flat", borderwidth=0, highlightthickness=0,
        wrap="word", selectbackground=PALETTE["accent_purple"],
        selectforeground="#FFFFFF",
        spacing1=3, spacing2=1, spacing3=3,
        padx=12, pady=7,
        cursor="arrow", takefocus=0,
    )
    text_area.pack(side="left", fill="both", expand=True)

    text_area.tag_configure(
        "loading", font=(FONT_FAMILY, 11, FONT_WEIGHT), justify="center",
        foreground=PALETTE["text_secondary"], spacing1=7, spacing2=2, spacing3=7
    )
    text_area.tag_configure(
        "word_translation", font=(FONT_FAMILY, 13, FONT_WEIGHT), justify="center",
        foreground=PALETTE["text_primary"], spacing1=5, spacing2=1, spacing3=5
    )
    text_area.tag_configure(
        "phrase_translation", font=(FONT_FAMILY, 12, FONT_WEIGHT), justify="right",
        foreground=PALETTE["text_primary"], spacing1=4, spacing2=1, spacing3=4
    )
    text_area.tag_configure(
        "error", font=(FONT_FAMILY, 11, FONT_WEIGHT), justify="center",
        foreground=PALETTE["accent_pink"]
    )
    text_area.config(state="disabled")

    footer = tk.Frame(main_frame, bg=PALETTE["bg_header"], height=18)
    footer.pack(fill="x", side="bottom")
    footer.pack_propagate(False)

    tk.Label(
        footer, text="Index-Translate-2B  •  Kokoro TTS",
        font=("Segoe UI", 7),
        fg=PALETTE["text_secondary"], bg=PALETTE["bg_header"]
    ).pack(side="right", padx=8)

    root.bind("<Escape>", lambda _e: hide_popup())

    root.withdraw()
    root.after(20, process_gui_queue)
    root.after(200, _initial_gui_update)
    root.mainloop()


def _initial_gui_update():
    update_action_buttons()
    set_status("آماده")


# ------------------------------------------------------------
# Shutdown
# ------------------------------------------------------------
shutdown_lock = threading.Lock()
shutting_down = False


def cleanup_resources():
    global shutting_down
    global llama_process, owns_llama_process

    with shutdown_lock:
        if shutting_down:
            return
        shutting_down = True

    llama_shutdown.set()

    try:
        if mouse_listener:
            mouse_listener.stop()
    except Exception:
        pass

    try:
        tts_stop_event.set()
        sd.stop()
    except Exception:
        pass

    try:
        save_json_file()
    except Exception:
        pass

    if owns_llama_process and llama_process is not None:
        try:
            if llama_process.poll() is None:
                llama_process.terminate()
                try:
                    llama_process.wait(timeout=2)
                except Exception:
                    pass
        except Exception:
            pass


atexit.register(cleanup_resources)


def shutdown_from_gui():
    try:
        cleanup_resources()
    finally:
        try:
            if root:
                root.destroy()
        except Exception:
            pass


# ------------------------------------------------------------
# Startup
# ------------------------------------------------------------
def main():
    load_bidi_support()
    init_cache()

    start_llama_server()

    if llama_ready.is_set():
        run_background(llama_keep_warm_worker, name="LlamaKeepWarm")

    run_background(load_kokoro, name="KokoroLoader")

    start_mouse_listener()
    setup_gui()


if __name__ == "__main__":
    main()
