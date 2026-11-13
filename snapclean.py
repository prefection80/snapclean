#!/usr/bin/env python3
"""
snapclean.py - snapshot pages from the screen, then remove a repeated watermark.

One window, two tabs:

  1  Snapshot           Press a hotkey (default F9) in your browser or any program,
                        mark an area of the screen, and it saves a numbered PNG,
                        presses a key (e.g. Right arrow), waits, and repeats.
  2  Remove watermark   Learns whatever stays put across the pages (the watermark),
                        shows what it found, and saves cleaned copies - optionally
                        also as one searchable PDF with an OCR text layer.

  3  Make PDF / Word / HTML    Takes a scanned, rasterised or otherwise poor PDF - or PNG pages - and makes a
                        new PDF and/or Word file from it: text that can be matched to
                        an installed font is redrawn as real text in the same place;
                        figures, plots, table lines and anything unmatched stay as they
                        look now. It can also hand the pages to tab 2 first.

"Remove watermark from these snapshots" on tab 1 hands the folder to tab 2.

Run:    python snapclean.py          (or double-click it)

This single file replaces snapkey_hotkey.py, dewatermark.py and dewatermark_gui.py.
Everything it needs is installed automatically the first time it starts: numpy,
pillow, opencv-python, pynput and pymupdf with pip, plus an OCR engine for the
searchable-PDF option - RapidOCR and the Tesseract program (through winget; Windows
may ask for permission once). Where RapidOCR has no build for your Python version
(very new Pythons), the program installs Python 3.13 beside yours, sets itself up
there and restarts in it, at every later start too. Set SNAPCLEAN_ONE_PYTHON=1 to
stay in the Python you started it with.

The command line of the old dewatermark.py still works:

    python snapclean.py analyze pages/
    python snapclean.py run pages/ cleaned/ [--pdf report.pdf] [--select 1,3] ...
    python snapclean.py pdf cleaned/ report.pdf [--retypeset] [--docx report.docx] [--jobs N]
    python snapclean.py rebuild scanned.pdf outfolder/ [--docx] [--no-pdf] [--plain] [--dpi N]
    python snapclean.py selftest

HOW THE WATERMARK REMOVAL WORKS
A watermark is the thing that stays put while the page content changes. The
per-pixel median across the pages keeps only static elements; those are split
into translucent pieces (watermark-like) and solid ones (headers, logos). The
selected pieces are un-blended with
    clean = background + (pixel - median) / (1 - alpha)
which restores text that crosses the watermark instead of painting over it.
Pixels outside the selected pieces are copied byte for byte. It needs at least
3 pages of the same pixel size with the watermark in the same place.
"""
from __future__ import annotations

import argparse
import ctypes
import glob
import hashlib
import importlib
import importlib.util
import json
import math
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback
from dataclasses import dataclass
from pathlib import Path

APP = "SnapClean"
VERSION = "1.52"
PYTHON_TESTED = "3.12 or 3.13"

if sys.version_info < (3, 10):
    # said plainly, before anything fails further on in a way that explains nothing
    _old = ("%s needs Python %s.\n\nThis is Python %d.%d, which is too old for the packages it uses.\n"
            "Install Python 3.13 from python.org and start the program with that."
            % (APP, PYTHON_TESTED, sys.version_info[0], sys.version_info[1]))
    print(_old)
    try:
        import tkinter as _tk
        from tkinter import messagebox as _mb
        _r = _tk.Tk()
        _r.withdraw()
        _mb.showerror(APP, _old)
        _r.destroy()
    except Exception:
        pass
    sys.exit(1)
HERE = Path(__file__).resolve().parent
LOG = HERE / "snapclean_error.log"
IS_WINDOWS = sys.platform.startswith("win")
CLI_MODE = len(sys.argv) > 1 and sys.argv[1] in ("analyze", "run", "pdf", "rebuild", "selftest", "-h", "--help")
import multiprocessing  # noqa: E402
IS_WORKER = multiprocessing.parent_process() is not None    # a helper process preparing PDF pages in parallel

# Make screen coordinates mean real pixels on scaled (125%, 150%...) displays.
if IS_WINDOWS and not CLI_MODE and not IS_WORKER:
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
except ImportError:                      # only acceptable for command-line use
    if not CLI_MODE:
        raise
    tk = ttk = filedialog = messagebox = None

CORE = {"numpy": "numpy", "PIL": "pillow", "cv2": "opencv-python"}      # import name -> pip name
GUI_ONLY = {"pynput": "pynput"}
SETUP_FILE = Path.home() / ".snapclean_setup.json"     # remembers installs that cannot work here
PYVER = f"{sys.version_info.major}.{sys.version_info.minor}"
_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)


def _python_exe():
    exe = sys.executable
    if os.path.basename(exe).lower() == "pythonw.exe":             # windowless launcher -> real interpreter
        alt = os.path.join(os.path.dirname(exe), "python.exe")
        exe = alt if os.path.exists(alt) else exe
    return exe


def _fatal(title, text):
    """Startup problem: write it to a log next to this file and show it in a dialog,
    so it is readable even when the console window closes straight away."""
    try:
        LOG.write_text(text, encoding="utf-8")
        text += f"\n\n(Also saved to {LOG})"
    except OSError:
        pass
    print(text, file=sys.stderr)
    if not CLI_MODE:
        try:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror(title, text)
            root.destroy()
        except Exception:
            pass
    sys.exit(1)


def _have(*modules):
    return all(importlib.util.find_spec(m) is not None for m in modules)


def _pip(packages):
    """pip install; returns (ok, output)."""
    try:
        p = subprocess.run([_python_exe(), "-m", "pip", "install", *packages], stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, errors="replace", creationflags=_NO_WINDOW)
        out, ok = p.stdout or "", p.returncode == 0
    except Exception as e:
        out, ok = str(e), False
    importlib.invalidate_caches()
    return ok, out


def _find_tesseract():
    exe = shutil.which("tesseract")
    if exe:
        return exe
    for base in (os.environ.get("ProgramFiles"), os.environ.get("ProgramFiles(x86)"),
                 os.path.join(os.environ.get("LOCALAPPDATA", ""), "Programs")):
        if base:
            cand = Path(base) / "Tesseract-OCR" / "tesseract.exe"
            if cand.exists():
                return str(cand)
    return None


OTHER_PYTHONS = ("3.13", "3.12")        # versions the RapidOCR reader has builds for, best first
_OTHER_NEEDS = ["numpy", "pillow", "opencv-python", "pynput", "pymupdf", "pyspellchecker", "rapidocr"]
_OTHER_CHECK = "import tkinter, numpy, PIL, cv2, pynput, rapidocr, onnxruntime"


def _run_quiet(cmd, timeout=1800):
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace",
                           timeout=timeout, creationflags=_NO_WINDOW)
        return p.returncode == 0, p.stdout or ""
    except Exception as e:
        return False, str(e)


def _find_other_python():
    """Another Python on this computer (3.13 or 3.12) that the better reader can be installed in, or None.
    SNAPCLEAN_PYTHON names one outright."""
    named = os.environ.get("SNAPCLEAN_PYTHON")
    if named:
        return named if os.path.exists(named) else None
    here = os.path.normcase(os.path.realpath(_python_exe()))
    for ver in OTHER_PYTHONS:
        if ver == PYVER:
            continue
        cands = []
        if shutil.which("py"):
            ok, out = _run_quiet(["py", f"-{ver}", "-c", "import sys; print(sys.executable)"], 60)
            if ok and out.strip():
                cands.append(out.strip().splitlines()[-1])
        nodot = ver.replace(".", "")
        for base in (os.path.join(os.environ.get("LOCALAPPDATA", ""), "Programs", "Python"),
                     os.environ.get("ProgramFiles"), os.environ.get("ProgramFiles(x86)"), "C:\\"):
            if base:
                cands.append(os.path.join(base, f"Python{nodot}", "python.exe"))
        if not IS_WINDOWS:
            cands.append(shutil.which(f"python{ver}") or "")
        for c in cands:
            if c and os.path.exists(c) and os.path.normcase(os.path.realpath(c)) != here:
                return c
    return None


def _other_python_ready(exe):
    return bool(exe) and os.path.exists(exe) and _run_quiet([exe, "-c", _OTHER_CHECK], 180)[0]


def _prepare_other_python(say):
    """This Python is too new for the RapidOCR reader. Find - or, on Windows, install - Python 3.13 beside
    it and put everything the program needs in that one. Returns (its python.exe or None, what went wrong)."""
    exe = _find_other_python()
    if not exe and IS_WINDOWS and shutil.which("winget"):
        say(f"Installing Python {OTHER_PYTHONS[0]} beside Python {PYVER}\n(the better text reader needs it)")
        _run_quiet(["winget", "install", "-e", "--id", f"Python.Python.{OTHER_PYTHONS[0]}", "--silent",
                    "--accept-package-agreements", "--accept-source-agreements", "--disable-interactivity"], 1800)
        exe = _find_other_python()
    if not exe:
        return None, f"Python {OTHER_PYTHONS[0]} is not on this computer and could not be installed."
    if _other_python_ready(exe):
        return exe, ""
    say(f"Installing the program's packages in {os.path.basename(os.path.dirname(exe)) or 'the other Python'}\n"
        "(this can take several minutes)")
    _run_quiet([exe, "-m", "ensurepip", "--upgrade"], 600)
    ok, out = _run_quiet([exe, "-m", "pip", "install", *_OTHER_NEEDS])
    if ok:
        # the build that can use the graphics card on Windows; the plain one if that will not install
        runtimes = (["onnxruntime-directml"] if IS_WINDOWS else []) + ["onnxruntime"]
        for runtime in runtimes:
            if _run_quiet([exe, "-c", "import onnxruntime"], 120)[0]:
                break
            ok, out = _run_quiet([exe, "-m", "pip", "install", runtime])
    if _other_python_ready(exe):
        return exe, ""
    return None, "The packages could not be installed in " + exe + ":\n" + out[-600:]


def _restart_with(exe):
    """Start this program again with another Python and end this one."""
    if os.path.basename(_python_exe()).lower() != os.path.basename(sys.executable).lower():   # started windowless
        alt = os.path.join(os.path.dirname(exe), "pythonw.exe")
        exe = alt if os.path.exists(alt) else exe
    env = dict(os.environ, SNAPCLEAN_RESTARTED="1")
    try:
        subprocess.Popen([exe, os.path.abspath(__file__), *sys.argv[1:]], env=env)
    except Exception:
        return False
    sys.exit(0)


_CARD_ASK = ("import onnxruntime as o, importlib.metadata as m\n"
             "print('PROVIDERS=' + ','.join(o.get_available_providers()))\n"
             "print('PACKAGES=' + ','.join(sorted(d.metadata['Name'] + ' ' + d.version for d in m.distributions()"
             " if (d.metadata['Name'] or '').lower().startswith('onnxruntime'))))")


def _card_support(exe=None):
    """What the reader's engine (onnxruntime) in this Python can run on, asked in a separate process so
    its files are not held open here: {"providers": [...], "packages": [...], "card": bool, "error": str}."""
    ok, out = _run_quiet([exe or _python_exe(), "-c", _CARD_ASK], 180)
    got = {"providers": [], "packages": [], "card": False, "error": "" if ok else out.strip()[-500:]}
    for line in out.splitlines():
        if line.startswith("PROVIDERS="):
            got["providers"] = [p for p in line[10:].split(",") if p]
        elif line.startswith("PACKAGES="):
            got["packages"] = [p for p in line[9:].split(",") if p]
    got["card"] = any(p in got["providers"] for p in ("DmlExecutionProvider", "CUDAExecutionProvider"))
    return got


def _video_cards():
    """Names of the graphics cards Windows knows about."""
    if not IS_WINDOWS:
        return []
    ok, out = _run_quiet(["powershell", "-NoProfile", "-Command",
                          "Get-CimInstance Win32_VideoController | ForEach-Object { $_.Name }"], 60)
    return [line.strip() for line in out.splitlines() if line.strip()] if ok else []


def _install_card_support(say):
    """Make the reader's engine in this Python the one that can use a graphics card (onnxruntime-directml).
    The plain onnxruntime and the DirectML one are the same module: with both installed, or only the plain
    one, no graphics card is seen - so every onnxruntime is removed first. Returns _card_support() after."""
    before = _card_support()
    if before["card"]:
        return before
    say("Installing graphics card support for the text reader\n(onnxruntime-directml)")
    exe = _python_exe()
    _run_quiet([exe, "-m", "pip", "uninstall", "-y", "onnxruntime", "onnxruntime-directml", "onnxruntime-gpu"], 600)
    ok, out = _run_quiet([exe, "-m", "pip", "install", "--no-cache-dir", "onnxruntime-directml"])
    after = _card_support()
    if not after["providers"]:                          # left without any: put the plain one back
        _run_quiet([exe, "-m", "pip", "install", "onnxruntime"])
        after = _card_support()
        after["error"] = "onnxruntime-directml could not be installed:\n" + out.strip()[-500:]
    elif not after["card"] and not after["error"]:
        has = any("directml" in p.lower() for p in after["packages"])
        after["error"] = ("onnxruntime-directml is installed, but it reports no graphics card support." if has else
                          "onnxruntime-directml could not be installed:\n" + out.strip()[-500:])
    importlib.invalidate_caches()
    return after


def _setup_state():
    try:
        return json.loads(SETUP_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _startup_setup():
    """Install everything the program needs that is not there yet, before the window opens.

    Required (the program cannot run without them): numpy, pillow, opencv-python, pynput.
    For the searchable-PDF option: pymupdf, an English word list (pyspellchecker), plus an OCR engine - RapidOCR where pip has it
    for this Python, otherwise the Tesseract program (installed with winget on Windows).
    An install that cannot work on this computer is remembered in ~/.snapclean_setup.json
    so it is not retried at every start; delete that file to make it try again."""
    state = _setup_state()
    restarted = bool(os.environ.get("SNAPCLEAN_RESTARTED")) or os.environ.get("SNAPCLEAN_ONE_PYTHON") == "1"
    # The better reader does not exist for this Python, and an earlier start set it up in another one:
    # carry on there straight away.
    if not CLI_MODE and not restarted and not _have("rapidocr", "onnxruntime") and state.get("other_python"):
        if _other_python_ready(state["other_python"]):
            _restart_with(state["other_python"])
        state.pop("other_python", None)                 # it has gone or broken: set it up again below
    required = [pkg for mod, pkg in {**CORE, **({} if CLI_MODE else GUI_ONLY)}.items() if not _have(mod)]
    want_pdf = not CLI_MODE and not _have("pymupdf") and state.get("pymupdf_failed") != PYVER
    want_rapid = not CLI_MODE and not _have("rapidocr", "onnxruntime") and state.get("rapid_failed") != PYVER
    want_words = not CLI_MODE and not _have("spellchecker") and state.get("words_failed") != PYVER

    def want_tesseract():                               # used on its own, and as RapidOCR's second opinion
        return (not CLI_MODE and not _find_tesseract() and shutil.which("winget") and not state.get("winget_tried"))

    def want_other_python():
        """RapidOCR cannot be had for this Python, and another Python has not been tried yet."""
        return (not CLI_MODE and not restarted and not _have("rapidocr", "onnxruntime")
                and (want_rapid or state.get("rapid_failed") == PYVER) and not state.get("other_python")
                and state.get("other_python_failed") != VERSION
                and (IS_WINDOWS or bool(os.environ.get("SNAPCLEAN_PYTHON"))))

    card_tag = f"{VERSION}/{PYVER}"

    def want_card():
        """The reader is here; make sure once (per version and Python) that it can use the graphics card."""
        return (not CLI_MODE and (IS_WINDOWS or bool(os.environ.get("SNAPCLEAN_TEST_CARD")))
                and _have("rapidocr", "onnxruntime") and state.get("card_tried") != card_tag
                and os.environ.get("DEWATERMARK_GPU", "1") != "0")

    if not (required or want_pdf or want_rapid or want_words or want_tesseract() or want_other_python() or want_card()):
        return
    progress = {"text": "Starting...", "fatal": None, "restart": None}

    def say(text):
        progress["text"] = text
        print(text, file=sys.stderr, flush=True)

    def work():
        if required:
            say("Installing: " + ", ".join(required))
            ok, out = _pip(required)
            if not ok:
                progress["fatal"] = ("Could not install: " + ", ".join(required) + "\n\n" + out[-1200:] +
                                     "\n\nTry it yourself in a Command Prompt:\n\n"
                                     f'    "{_python_exe()}" -m pip install {" ".join(required)}')
                return
        if want_pdf:
            say("Installing the PDF writer: pymupdf")
            if not _pip(["pymupdf"])[0]:
                state["pymupdf_failed"] = PYVER
        if want_words:
            say("Installing the English word list: pyspellchecker")
            if not _pip(["pyspellchecker"])[0]:
                state["words_failed"] = PYVER
        if want_rapid:
            say("Installing the OCR engine: rapidocr, onnxruntime")
            # on Windows the DirectML build, which can use the graphics card; the plain one if that fails
            first = "onnxruntime-directml" if sys.platform.startswith("win") else "onnxruntime"
            if not (_pip(["rapidocr", first])[0] and _have("rapidocr", "onnxruntime")) and \
                    (not _pip(["rapidocr", "onnxruntime"])[0] or not _have("rapidocr", "onnxruntime")):
                state["rapid_failed"] = PYVER            # typically: no build for this Python version yet
        if want_tesseract():
            say("Installing the Tesseract OCR program\n(Windows may ask for permission - choose Yes)")
            state["winget_tried"] = True
            try:
                subprocess.run(["winget", "install", "-e", "--id", "UB-Mannheim.TesseractOCR", "--silent",
                                "--accept-package-agreements", "--accept-source-agreements",
                                "--disable-interactivity"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               timeout=1200, creationflags=_NO_WINDOW)
            except Exception:
                pass
            state["tesseract_installed"] = bool(_find_tesseract())
        if want_card():
            say("Checking graphics card support for the text reader...")
            got = _install_card_support(say)
            state["card_tried"], state["card_ok"], state["card_problem"] = card_tag, got["card"], got["error"]
        if want_other_python():
            exe, problem = _prepare_other_python(say)
            if exe:
                state["other_python"] = progress["restart"] = exe
                state.pop("other_python_failed", None)
            else:                                       # not retried until the next version of the program
                state["other_python_failed"], state["other_python_problem"] = VERSION, problem
        try:
            SETUP_FILE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        except OSError:
            pass

    t = threading.Thread(target=work, daemon=True)
    t.start()
    if not CLI_MODE:
        try:
            win = tk.Tk()
            win.title(f"{APP} - first-time setup")
            win.resizable(False, False)
            ttk.Label(win, padding=(24, 18, 24, 4), justify="center",
                      text="Setting up what this program needs.\nThis happens once and can take a few minutes.").pack()
            label = ttk.Label(win, padding=(24, 4, 24, 8), justify="center", width=58, anchor="center")
            label.pack()
            bar = ttk.Progressbar(win, mode="indeterminate", length=360)
            bar.pack(padx=24, pady=(0, 20))
            bar.start(12)
            win.protocol("WM_DELETE_WINDOW", lambda: None)         # wait for the installs to finish

            def check():
                label.configure(text=progress["text"])
                if t.is_alive():
                    win.after(150, check)
                else:
                    bar.stop()
                    win.destroy()

            win.after(50, check)
            win.mainloop()
        except tk.TclError:
            pass
    t.join()
    importlib.invalidate_caches()
    if progress["fatal"]:
        _fatal(f"{APP} - automatic install failed", progress["fatal"])
    if progress["restart"]:
        _restart_with(progress["restart"])              # carries on in the other Python; this one ends here


# ---- settings: the switches that used to need environment variables --------------------------------
# name: (environment variable, {choice shown: value put in the variable ("" = leave it unset)}, what it does)
SETTINGS = {
    "reader": ("DEWATERMARK_OCR", {"Automatic (RapidOCR with Tesseract, if both are there)": "", "Tesseract only": "tesseract",
                                   "RapidOCR": "rapid"}, "Text reader"),
    "gpu": ("DEWATERMARK_GPU", {"Use the graphics card when there is one": "", "Never use the graphics card": "0"}, "Graphics card"),
    "card": ("DEWATERMARK_CARD", {"Choose automatically (high-performance card first)": "", "Card 0": "0", "Card 1": "1", "Card 2": "2"},
             "Which graphics card"),
    "models": ("DEWATERMARK_MODELS", {"Larger reading models on a graphics card": "", "Standard reading models always": "small"},
               "Reading models"),
    "extras": ("DEWATERMARK_EXTRA", {"On with a graphics card (second reading, second look at doubtful words)": "",
                                     "Always on (slow on a processor)": "1", "Off": "0"}, "Extra readings"),
    "enlarge": ("DEWATERMARK_ENLARGE", {"Enlarge pages with small type automatically": "", "Never enlarge": "0", "Always enlarge 2 times": "2",
                                        "Always enlarge 3 times": "3"}, "Small type"),
    "python": ("SNAPCLEAN_ONE_PYTHON", {"Use a second Python for the better reader when this one cannot have it": "",
                                        "Stay in the Python the program was started with": "1"}, "Python"),
}


def _apply_settings():
    """Put the saved settings into force for this run. A variable already set outside the program wins."""
    saved = _setup_state().get("settings") or {}
    for name, (var, choices, _) in SETTINGS.items():
        value = saved.get(name, "")
        if value and value in choices.values() and not os.environ.get(var):
            os.environ[var] = value


if not IS_WORKER:
    _apply_settings()
    _startup_setup()
try:
    import cv2
    import numpy as np
    from PIL import Image
except ImportError as e:
    _fatal(f"{APP} - missing package",
           f"A required Python package could not be loaded:\n\n    {e}\n\n"
           "Install the packages by running this in a Command Prompt:\n\n"
           f'    "{_python_exe()}" -m pip install numpy pillow opencv-python pynput\n\n'
           "then start the program again.")

keyboard = None
mouse = None
KEYBOARD_ERROR = ""
if not CLI_MODE and not IS_WORKER:
    from PIL import ImageGrab, ImageTk
    try:
        from pynput import keyboard
        try:
            from pynput import mouse
        except Exception:
            mouse = None
    except Exception as e:               # no display, or the package would not load
        KEYBOARD_ERROR = str(e)


def log_error(context=""):
    """Record the exception being handled in snapclean_error.log (next to this file), with the time.

    Problems inside background work never reach the console of a double-clicked program, so they are
    kept here; the file is what to send when reporting a problem."""
    text = traceback.format_exc()
    print(text, file=sys.stderr)
    try:
        with open(LOG, "a", encoding="utf-8") as fh:
            fh.write(f"\n--- {time.strftime('%Y-%m-%d %H:%M:%S')}  {APP} {VERSION}  {context}\n{text}")
    except OSError:
        pass
    return text


def friendly(exc):
    """A message a person can act on, for the errors that have an obvious cause."""
    if isinstance(exc, MemoryError) or "bad allocation" in str(exc) or "Insufficient memory" in str(exc):
        return ("The computer ran out of memory.\n\nThings that help: set 'CPU cores' to 1 or 2, read PDF pages at "
                "150 or 200 dpi instead of 300, close other programs, or work on fewer pages at a time.")
    return str(exc) or exc.__class__.__name__


class Eta:
    """Elapsed time and an estimate of the time left, from 'done of total' progress reports."""

    def __init__(self):
        self.reset()

    def reset(self):
        self.t0 = self.t1 = self.last = None
        self.d1 = self.done = self.total = 0

    def update(self, done, total):
        now = time.monotonic()
        if total <= 0 or done < self.done or (done == 0 and self.done):
            self.reset()
        if total <= 0:
            return
        if self.t0 is None:
            self.t0 = now
        if done >= 1 and self.t1 is None:        # the first item is often slow (start-up): time the rest from here
            self.t1, self.d1 = now, done
        self.done, self.total, self.last = done, total, now

    @staticmethod
    def _clock(seconds):
        seconds = int(round(seconds))
        return f"{seconds // 3600}:{seconds % 3600 // 60:02d}:{seconds % 60:02d}" if seconds >= 3600 \
            else f"{seconds // 60}:{seconds % 60:02d}"

    def text(self):
        if self.t0 is None or self.total <= 0 or self.done >= self.total:
            return ""
        now = time.monotonic()
        out = f"{self._clock(now - self.t0)} elapsed"
        if self.done < 1:
            return out
        if self.done - self.d1 >= 2:
            each = (self.last - self.t1) / (self.done - self.d1)
        else:
            each = (self.last - self.t0) / self.done
        left = max(0.0, each * (self.total - self.done) - (now - self.last))
        finish = time.strftime("%I:%M %p", time.localtime(time.time() + left)).lstrip("0")
        return f"{out}, about {self._clock(left)} left (done around {finish})"


ANSWERS_FILE = "snapclean_answers.json"     # kept in the output folder: the words typed in for that document


def fit_photo(png, room, height, most=2.0):
    """A strip of page (PNG bytes) as a Tk picture scaled to fit `room` x `height` - enlarged up to
    `most` times when there is space, smoothly reduced when it is too wide. None if it cannot be shown."""
    try:
        import base64
        import io
        im = Image.open(io.BytesIO(png)).convert("RGB")
        scale = min(room / im.width, height / im.height, most)
        if abs(scale - 1.0) > 0.03:
            im = im.resize((max(1, int(im.width * scale)), max(1, int(im.height * scale))), Image.LANCZOS)
        out = io.BytesIO()
        im.save(out, "PNG")
        return tk.PhotoImage(data=base64.b64encode(out.getvalue()))
    except Exception:
        try:
            import base64
            return tk.PhotoImage(data=base64.b64encode(png))
        except Exception:
            return None


class ReviewDialog(tk.Toplevel if tk else object):
    """Shows, one after another, each word the program left as a picture; the user types what it says.

    One entry per different reading, most frequent first - so every answer settles all the places the
    same reading occurs. The answers are saved in the output folder and used on the next run."""

    def __init__(self, master, items, answers_path):
        super().__init__(master)
        self.title("Type in the words the program was not sure of")
        self.transient(master)
        self.items, self.path = items, Path(answers_path)
        self.answers = load_answers(self.path)
        self.given = 0                  # answers typed in this sitting
        self.i = 0
        self.photo = None
        wide = max(900, min(1500, self.winfo_screenwidth() - 80))
        self.geometry(f"{wide}x{min(780, self.winfo_screenheight() - 80)}")
        self.minsize(820, 640)
        pad = {"padx": 10, "pady": 4}
        self.where = ttk.Label(self, font=("Segoe UI", 10, "bold"))
        self.where.pack(anchor="w", **pad)
        ttk.Label(self, text="On the page now (the word in the red box):", foreground="#444").pack(anchor="w", padx=10)
        self.canvas = tk.Canvas(self, height=226, bg="white", highlightthickness=1, highlightbackground="#999")
        self.canvas.pack(fill="x", **pad)
        self.after_lbl = ttk.Label(self, foreground="#444")
        self.after_lbl.pack(anchor="w", padx=10)
        self.canvas2 = tk.Canvas(self, height=226, bg="white", highlightthickness=1, highlightbackground="#999")
        self.canvas2.pack(fill="x", **pad)
        self.photo2 = None
        self._pending = None
        self.read_lbl = ttk.Label(self, foreground="#444")
        self.read_lbl.pack(anchor="w", **pad)
        row = ttk.Frame(self)
        row.pack(fill="x", **pad)
        ttk.Label(row, text="The boxed word is:").pack(side="left")
        self.text = tk.StringVar()
        self.entry = ttk.Entry(row, textvariable=self.text, width=40, font=("Segoe UI", 14))
        self.entry.pack(side="left", padx=8)
        ttk.Label(row, text="Enter = use it     Esc = skip (leave as a picture)", foreground="#555").pack(side="left")
        row = ttk.Frame(self)
        row.pack(fill="x", **pad)
        ttk.Button(row, text="Use it  (Enter)", style="Go.TButton", command=self._use).pack(side="left")
        ttk.Button(row, text="Skip  (Esc)", command=self._skip).pack(side="left", padx=6)
        ttk.Button(row, text="< Back", command=self._back).pack(side="left")
        ttk.Button(row, text="Finish", command=self._finish).pack(side="right")
        self.note = ttk.Label(self, foreground="#555", wraplength=860, justify="left",
                              text="Type exactly what the boxed word says, with its punctuation - one word, no spaces. "
                                   "Your answer is used everywhere the program read the same thing, in this run and "
                                   "later ones. You can stop at any time: what you have typed is kept.")
        self.note.pack(anchor="w", **pad)
        self.text.trace_add("write", lambda *a: self._preview_soon())
        self.bind("<Return>", lambda e: self._use())
        self.bind("<Escape>", lambda e: self._skip())
        self.protocol("WM_DELETE_WINDOW", self._finish)
        self.update_idletasks()
        self._show()
        self.bind("<Configure>", self._resized)
        self.grab_set()
        self.entry.focus_set()

    def _show(self):
        while self.i < len(self.items) and self.items[self.i]["reading"] in self.answers and not self.items[self.i].get("revisit"):
            self.i += 1                 # answered in an earlier sitting
        if self.i >= len(self.items):
            self._finish()
            return
        item = self.items[self.i]
        times = item.get("count", 1)
        self.where.config(text=f"Word {self.i + 1} of {len(self.items)}      "
                               f"({times} place{'s' if times != 1 else ''} in the document, first on {item.get('page', '')})")
        note = ("\nThe program is NOT SURE THE BOX IS ON THIS WORD. If the box is not on one whole word that looks "
                "like the reading, press Skip.") if item.get("loose") else ""
        self.read_lbl.config(text=f"The program read:  {item['reading']}        Left as a picture because: {item['reason']}." + note,
                             foreground="#b00000" if note else "")
        self.canvas.delete("all")
        self.photo = self._put(self.canvas, item["png"])
        if self.photo is None:
            self.canvas.create_text(20, 85, anchor="w", text="(the picture of this word could not be shown)")
        self.text.set(self.answers.get(item["reading"], item.get("guess") or item["reading"]))
        self.entry.focus_set()
        self.entry.selection_range(0, "end")
        self.entry.icursor("end")

    def _put(self, canvas, png):
        """Show a strip of page (PNG bytes) in the middle of a canvas, enlarged twice when there is room."""
        canvas.delete("all")
        room = canvas.winfo_width()
        room = room if room > 100 else 1100             # (not laid out yet: about the width it is made with)
        photo = fit_photo(png, room - 12, 218)
        if photo is not None:
            canvas.create_image(room // 2, 113, image=photo)
        return photo

    def _resized(self, event):
        """The window was made wider or narrower: show the pictures again at the new size."""
        if event.widget is self and event.width != getattr(self, "_last_width", 0):
            self._last_width = event.width
            if self.i < len(self.items):
                self.after(60, lambda: (setattr(self, "photo", self._put(self.canvas, self.items[self.i]["png"]))
                                        if self.i < len(self.items) and self.winfo_exists() else None, self._preview_soon()))

    def _preview_soon(self):
        if self._pending is not None:
            try:
                self.after_cancel(self._pending)
            except Exception:
                pass
        self._pending = self.after(120, self._preview)      # not on every keystroke of fast typing

    def _preview(self):
        """The same strip of page with what is typed drawn in place of the boxed word."""
        self._pending = None
        if self.i >= len(self.items) or not self.winfo_exists():
            return
        word = self.text.get().strip()
        got = None
        if word and " " not in word:
            try:
                got = preview_word(self.items[self.i], word)
            except Exception:
                got = None
        if got is None:
            self.canvas2.delete("all")
            self.photo2 = None
            self.after_lbl.config(text="With your word:  (nothing to show - type the word)" if not word else
                                       "With your word:  (no preview for this one)")
            return
        self.photo2 = self._put(self.canvas2, got[0])
        self.after_lbl.config(text="With your word, as it will be redrawn (green box):" if got[1] else
                                   "With your word (orange box): it does not fit the space the program found for this "
                                   "word, so the picture will be kept here.")

    def _use(self):
        if self.i >= len(self.items):
            return
        word = self.text.get().strip()
        if not word:
            self._skip()
            return
        if " " in word:
            messagebox.showinfo(APP, "One word at a time, please - no spaces.\n\nIf the box holds two words, "
                                     "skip it: it stays as its picture.", parent=self)
            return
        self.answers[self.items[self.i]["reading"]] = word
        self.items[self.i].pop("revisit", None)
        self.given += 1
        try:
            save_answers(self.path, self.answers)      # after every word: nothing is lost by stopping
        except Exception:
            pass
        self.i += 1
        self._show()

    def _skip(self):
        if self.i < len(self.items):
            self.items[self.i].pop("revisit", None)
        self.i += 1
        self._show()

    def _back(self):
        if self.i > 0:
            self.i -= 1
            self.items[self.i]["revisit"] = True
            self._show()

    def _finish(self):
        try:
            self.grab_release()
        except Exception:
            pass
        self.destroy()


class NewWordsDialog(tk.Toplevel if tk else object):
    """A list of words the program thinks are real but its dictionary does not have - abbreviations
    mostly. The user ticks the ones that are right; those are added to their own dictionary."""

    def __init__(self, master, candidates):
        super().__init__(master)
        self.title("New words for your dictionary")
        self.transient(master)
        self.cands = candidates
        self.ticked = {c["word"] for c in candidates if c.get("suggest")}
        self.result = []
        self.photo = None
        self.geometry(f"{max(900, min(1300, self.winfo_screenwidth() - 80))}x660")
        self.minsize(760, 520)
        pad = {"padx": 10, "pady": 4}
        ttk.Label(self, wraplength=860, justify="left",
                  text="These were left as pictures because the dictionary does not know them. Tick the ones that are "
                       "real words or abbreviations, spelled exactly as shown. They are added to your own word list "
                       f"({WORDS_FILE}, next to the program) and count as known words from now on, in every document. "
                       "Click a row to see the word on the page; click its box (or press Space) to tick or untick it."
                  ).pack(anchor="w", **pad)
        box = ttk.Frame(self)
        box.pack(fill="both", expand=True, **pad)
        self.tree = ttk.Treeview(box, columns=("add", "word", "places", "note"), show="headings", height=12,
                                 selectmode="browse")
        for col, title, width, anchor in (("add", "Add", 50, "center"), ("word", "Word", 190, "w"),
                                          ("places", "Places", 70, "e"), ("note", "The program's view", 480, "w")):
            self.tree.heading(col, text=title)
            self.tree.column(col, width=width, anchor=anchor, stretch=(col == "note"))
        bar = ttk.Scrollbar(box, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=bar.set)
        self.tree.pack(side="left", fill="both", expand=True)
        bar.pack(side="left", fill="y")
        for i, c in enumerate(candidates):
            self.tree.insert("", "end", iid=str(i), values=(self._mark(c), c["word"], c["count"], c.get("note", "")))
        self.canvas = tk.Canvas(self, height=170, bg="white", highlightthickness=1, highlightbackground="#999")
        self.canvas.pack(fill="x", **pad)
        row = ttk.Frame(self)
        row.pack(fill="x", **pad)
        self.add_btn = ttk.Button(row, style="Go.TButton", command=self._add)
        self.add_btn.pack(side="left")
        ttk.Button(row, text="Tick all", command=lambda: self._all(True)).pack(side="left", padx=6)
        ttk.Button(row, text="Untick all", command=lambda: self._all(False)).pack(side="left")
        ttk.Button(row, text="Add none", command=self._close).pack(side="right")
        self.tree.bind("<<TreeviewSelect>>", lambda e: self._show())
        self.tree.bind("<Button-1>", self._click)
        self.tree.bind("<space>", lambda e: self._toggle(self.tree.focus()))
        self.tree.bind("<Double-1>", lambda e: self._toggle(self.tree.focus()))
        self.protocol("WM_DELETE_WINDOW", self._close)
        self._count()
        self.update_idletasks()
        if candidates:
            self.tree.selection_set("0")
            self.tree.focus("0")
        self.grab_set()
        self.tree.focus_set()

    def _mark(self, c):
        return "[x]" if c["word"] in self.ticked else "[  ]"

    def _count(self):
        n = len(self.ticked)
        self.add_btn.config(text=f"Add the {n} ticked word(s) to my dictionary" if n else "Nothing ticked")

    def _toggle(self, iid):
        if not iid:
            return
        c = self.cands[int(iid)]
        (self.ticked.discard if c["word"] in self.ticked else self.ticked.add)(c["word"])
        self.tree.set(iid, "add", self._mark(c))
        self._count()

    def _click(self, event):
        if self.tree.identify_column(event.x) == "#1":
            self._toggle(self.tree.identify_row(event.y))

    def _all(self, on):
        self.ticked = {c["word"] for c in self.cands} if on else set()
        for i, c in enumerate(self.cands):
            self.tree.set(str(i), "add", self._mark(c))
        self._count()

    def _show(self):
        sel = self.tree.selection()
        self.canvas.delete("all")
        if not sel:
            return
        c = self.cands[int(sel[0])]
        room = self.canvas.winfo_width()
        room = room if room > 100 else 1000
        self.photo = fit_photo(c["png"], room - 12, 166)
        if self.photo is not None:
            self.canvas.create_image(room // 2, 85, image=self.photo)
        else:
            self.canvas.create_text(20, 85, anchor="w", text="(no picture for this word)")

    def _add(self):
        self.result = [c["word"] for c in self.cands if c["word"] in self.ticked]
        self._close()

    def _close(self):
        try:
            self.grab_release()
        except Exception:
            pass
        self.destroy()


class ReviewListDialog(tk.Toplevel if tk else object):
    """The words left as pictures as a list: picture, the program's guess (to correct), how often it
    occurs. Most frequent first, a screenful at a time. Enter accepts a row and moves down; "Accept this
    screen" takes every row as it stands; an emptied box leaves that word a picture."""
    ROWS = 12

    def __init__(self, master, items, answers_path):
        super().__init__(master)
        self.title("Words the program was not sure of - list")
        self.transient(master)
        self.path = Path(answers_path)
        self.answers = load_answers(self.path)
        # sure boxes first: a doubtful box may not be on the word at all
        self.items = [it for it in items if it["reading"] not in self.answers or it.get("revisit")]
        self.items.sort(key=lambda it: (bool(it.get("loose")), -it.get("count", 1)))
        self.given, self.page, self.rows, self.photos = 0, 0, [], []
        self.geometry(f"{min(1040, self.winfo_screenwidth() - 80)}x{min(820, self.winfo_screenheight() - 80)}")
        self.head = ttk.Label(self, font=("Segoe UI", 10, "bold"), padding=(12, 8, 12, 2))
        self.head.pack(anchor="w")
        ttk.Label(self, padding=(12, 0, 12, 6), foreground="#555", wraplength=980, justify="left",
                  text="Each row: the word as it is on the page (red box), and what the program thinks it says. Correct the ones "
                       "that are wrong. Enter = accept the row and go down. Empty the box to leave a word as a picture. "
                       "Rows marked '?' may not be boxed on the right word - check them or empty them.").pack(anchor="w")
        self.body = ttk.Frame(self, padding=(12, 0, 12, 0))
        self.body.pack(fill="both", expand=True)
        bar = ttk.Frame(self, padding=(12, 8, 12, 10))
        bar.pack(fill="x")
        ttk.Button(bar, text="Accept this screen and go on  (Ctrl+Enter)", style="Go.TButton", command=self._accept_page).pack(side="left")
        ttk.Button(bar, text="Skip this screen", command=lambda: self._turn(1)).pack(side="left", padx=6)
        ttk.Button(bar, text="< Back", command=lambda: self._turn(-1)).pack(side="left")
        ttk.Button(bar, text="Finish", command=self._finish).pack(side="right")
        self.bind("<Control-Return>", lambda e: self._accept_page())
        self.bind("<Escape>", lambda e: self._finish())
        self.protocol("WM_DELETE_WINDOW", self._finish)
        self._show()
        self.grab_set()

    def _crop(self, item):
        """The word with a little of the line round it, boxed."""
        try:
            import io
            im = Image.open(io.BytesIO(item["png"])).convert("RGB")
            box = (item.get("draw") or {}).get("box")
            if box:
                from PIL import ImageDraw
                x0, y0, x1, y1 = box
                tall = max(8.0, y1 - y0)
                ImageDraw.Draw(im).rectangle((x0 - 2, y0 - 2, x1 + 2, y1 + 2), outline=(215, 30, 30), width=2)
                im = im.crop((int(max(0, x0 - 6 * tall)), int(max(0, y0 - 0.9 * tall)), int(min(im.width, x1 + 6 * tall)), int(min(im.height, y1 + 0.9 * tall))))
            out = io.BytesIO()
            im.save(out, "PNG")
            return fit_photo(out.getvalue(), 520, 44, most=3.0)
        except Exception:
            return None

    def _show(self):
        for child in self.body.winfo_children():
            child.destroy()
        self.rows, self.photos = [], []
        start = self.page * self.ROWS
        chunk = self.items[start:start + self.ROWS]
        if not chunk:
            self._finish()
            return
        left = sum(it.get("count", 1) for it in self.items[start:])
        self.head.config(text=f"Readings {start + 1} - {start + len(chunk)} of {len(self.items)}   "
                              f"({left:,} place(s) in the document still to settle)")
        for r, item in enumerate(chunk):
            photo = self._crop(item)
            self.photos.append(photo)
            pic = tk.Label(self.body, image=photo, bg="white", relief="solid", bd=1) if photo else ttk.Label(self.body, text="(no picture)")
            pic.grid(row=r, column=0, sticky="w", pady=3)
            var = tk.StringVar(value=self.answers.get(item["reading"], item.get("guess") or item["reading"]))
            entry = ttk.Entry(self.body, textvariable=var, width=26, font=("Segoe UI", 13))
            entry.grid(row=r, column=1, padx=10)
            note = ("? " if item.get("loose") else "") + f"×{item.get('count', 1)}   read as: {item['reading']}   ({item['reason']})"
            ttk.Label(self.body, text=note, foreground="#a00" if item.get("loose") else "#555").grid(row=r, column=2, sticky="w")
            entry.bind("<Return>", lambda e, k=r: self._down(k))
            entry.bind("<Down>", lambda e, k=r: self._focus(k + 1))
            entry.bind("<Up>", lambda e, k=r: self._focus(k - 1))
            self.rows.append((item, var, entry))
        self.after(50, lambda: self._focus(0))

    def _focus(self, k):
        if 0 <= k < len(self.rows):
            self.rows[k][2].focus_set()
            self.rows[k][2].selection_range(0, "end")

    def _keep(self, item, var):
        text = var.get().strip()
        if text and " " not in text:
            if self.answers.get(item["reading"]) != text:
                self.given += 1
            self.answers[item["reading"]] = text
            return True
        return False

    def _down(self, k):
        self._keep(*self.rows[k][:2])
        if k + 1 < len(self.rows):
            self._focus(k + 1)
        else:
            self._accept_page()

    def _accept_page(self):
        for item, var, _ in self.rows:
            self._keep(item, var)
        self._save()
        self._turn(1)

    def _turn(self, by):
        self.page = max(0, self.page + by)
        self._show()

    def _save(self):
        try:
            save_answers(self.path, self.answers)
        except OSError as e:
            messagebox.showerror(APP, f"Could not save your answers in {self.path}:\n{e}", parent=self)

    def _finish(self):
        self._save()
        self.destroy()


def offer_review(master, review, answers_path, rerun, ask=True):
    """After a run: offer to go through the words left as pictures - first the ones that look like new
    words for the dictionary (to approve from a list), then the rest (to type in one by one) - and then
    to run again so the answers are used."""
    review = [r for r in (review or []) if r.get("png")]
    if not review:
        if not ask:
            messagebox.showinfo(APP, "There is nothing to go through: the last run left no words as pictures, "
                                     "or it has not been run yet with 'Re-typeset' ticked.")
        return
    try:
        cands = new_word_candidates(review)
    except Exception:
        log_error("new word candidates")
        cands = []
    places = sum(r.get("count", 1) for r in review)
    new = (f"{len(cands):,} of them look like words or abbreviations the dictionary does not have - you can "
           "approve those from a list first.\n\n") if cands else ""
    if ask and not messagebox.askyesno(APP, f"{places:,} word(s) were left as pictures ({len(review):,} different readings).\n\n"
                                            + new + "Do you want to go through them now?\n"
                                            "The most frequent come first, and you can stop whenever you like.\n\n"
                                            "(You can also do this later with the 'Review words...' button.)"):
        return
    added, where = [], None
    if cands:
        chooser = NewWordsDialog(master, cands)
        master.wait_window(chooser)
        added = list(chooser.result)
        if added:
            where = add_user_words(added)
            gone = set(added)

            def core_of(reading):
                core = _core(reading)[1]
                return core[:-2] if core.endswith(("'s", "’s")) else core
            review = [r for r in review if core_of(r["reading"]) not in gone]
    given = 0
    if review and (not cands or messagebox.askyesno(
            APP, (f"{len(added)} word(s) added to your dictionary.\n\n" if added else "")
            + f"{len(review):,} other reading(s) are left. Do you want to type those in one by one now?")):
        # a quick list for the many, or the page view for a careful look at each
        as_list = len(review) >= 4 and messagebox.askyesno(
            APP, "How do you want to go through them?\n\nYes - a LIST: every word's picture in a row with the program's guess "
                 "beside it; correct the wrong ones, Enter moves down, one button accepts the screen. Fastest.\n\n"
                 "No - ONE AT A TIME: each word shown in its place on the page, with a preview of the page as it will be.")
        dialog = (ReviewListDialog if as_list else ReviewDialog)(master, review, answers_path)
        master.wait_window(dialog)
        given = dialog.given
    if not (added or given):
        return
    done = []
    if added:
        done.append(f"{len(added)} word(s) added to your dictionary" + (f"\n({where})" if where else
                    "\n(the word list could not be written, so they count for this session only)"))
    if given:
        done.append(f"{given} word(s) typed in and saved in\n{answers_path}")
    if messagebox.askyesno(APP, "\n\n".join(done) + "\n\nRun again now so they are used?\n"
                                "(The pages do not have to be read again, so this is quicker.)"):
        rerun()


# =============================================================================
# PART 1 - WATERMARK ENGINE (learn, select, remove, OCR / PDF, command line)
# =============================================================================

MAX_ALPHA = 0.92          # never amplify by more than 1/(1-0.92) = 12.5x
INK_DEV = 40.0            # deviation that counts as "there is ink here"


# --------------------------------------------------------------------------- I/O

# Page pictures the program takes. Whatever comes in, cleaned pages go out as PNG (nothing is lost in it).
PICTURE_TYPES = (".png", ".jpg", ".jpeg", ".tif", ".tiff", ".bmp", ".webp", ".gif")
PICTURE_PATTERNS = " ".join("*" + e for e in PICTURE_TYPES)


def is_picture(path):
    return str(path).lower().endswith(PICTURE_TYPES)


def picture_size(path):
    """(width, height) of a page picture as it will be loaded - a photograph stored sideways counted upright."""
    with Image.open(path) as im:
        w, h = im.size
        try:
            turn = im.getexif().get(0x0112, 1)
        except Exception:
            turn = 1
    return (h, w) if turn in (5, 6, 7, 8) else (w, h)


_SPLIT_DIRS = []


def expand_pictures(files):
    """A picture file that holds several pages (a multi-page TIFF, a GIF of frames) is laid out as one PNG
    per page in a temporary folder; every other file is passed on as it is. Order is kept."""
    out = []
    for f in files:
        f = Path(f)
        try:
            with Image.open(f) as im:
                n = int(getattr(im, "n_frames", 1) or 1)
                if n <= 1:
                    out.append(f)
                    continue
                if not _SPLIT_DIRS:
                    import atexit
                    import shutil
                    _SPLIT_DIRS.append(Path(tempfile.mkdtemp(prefix="snapclean_pages_")))
                    atexit.register(shutil.rmtree, str(_SPLIT_DIRS[0]), True)
                digits = max(3, len(str(n)))
                for i in range(n):
                    im.seek(i)
                    (_SPLIT_DIRS[0] / f.stem).mkdir(exist_ok=True)      # the folder's name names the results
                    page = _SPLIT_DIRS[0] / f.stem / f"{f.stem}_page{i + 1:0{digits}d}.png"
                    keep = {"dpi": im.info["dpi"]} if im.info.get("dpi") else {}
                    im.convert("RGB").save(page, "PNG", **keep)
                    out.append(page)
        except Exception:
            out.append(f)                               # unreadable: let the reading of it say so
    return out


def load_png(path):
    """Return (rgb uint8 HxWx3, info) for a page picture of any kind the program takes (PNG, JPEG, TIFF,
    BMP, WebP, GIF). info keeps what is needed to save faithfully."""
    im = Image.open(path)
    try:                                               # a photograph taken sideways says so: turn it upright
        from PIL import ImageOps
        turned = ImageOps.exif_transpose(im)
        if turned is not None:
            im = turned
    except Exception:
        pass
    info = {"mode": im.mode, "dpi": im.info.get("dpi"),
            "icc": im.info.get("icc_profile"), "alpha": None}
    if im.mode.startswith("I"):                       # 16/32-bit greyscale -> 8-bit
        arr = np.asarray(im).astype(np.float64)
        if arr.max() > 255:
            arr = arr / 257.0
        g = np.clip(np.rint(arr), 0, 255).astype(np.uint8)
        return np.stack([g, g, g], axis=-1), info
    if im.mode in ("RGBA", "LA") or (im.mode == "P" and "transparency" in im.info):
        rgba = np.asarray(im.convert("RGBA"))
        info["alpha"] = rgba[..., 3].copy()
        return rgba[..., :3].copy(), info
    return np.asarray(im.convert("RGB")).copy(), info


def save_png(path, rgb, info=None):
    info = info or {}
    grey = info.get("mode", "RGB") in ("L", "LA", "1") or str(info.get("mode", "")).startswith("I")
    alpha = info.get("alpha")
    if grey:
        im = Image.fromarray(np.ascontiguousarray(rgb[..., 0]))
        if alpha is not None:
            im.putalpha(Image.fromarray(alpha))
    elif alpha is not None:
        im = Image.fromarray(np.dstack([rgb, alpha]))
    else:
        im = Image.fromarray(rgb)
    kw = {}
    if info.get("dpi"):
        kw["dpi"] = info["dpi"]
    if info.get("icc"):
        kw["icc_profile"] = info["icc"]
    im.save(path, "PNG", **kw)


# --------------------------------------------------------------------------- helpers

def available_memory_gb():
    """Free physical memory in GB, or None if it cannot be found out."""
    try:
        if sys.platform.startswith("win"):
            import ctypes

            class Status(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong)] + \
                           [(n, ctypes.c_ulonglong) for n in ("ullTotalPhys", "ullAvailPhys", "ullTotalPageFile",
                                                               "ullAvailPageFile", "ullTotalVirtual",
                                                               "ullAvailVirtual", "ullAvailExtendedVirtual")]
            st = Status()
            st.dwLength = ctypes.sizeof(Status)
            if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(st)):
                return st.ullAvailPhys / 2 ** 30
            return None
        with open("/proc/meminfo") as fh:
            for line in fh:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) / 2 ** 20
    except Exception:
        pass
    return None


def sample_limit(width, height, wanted=30):
    """How many pages of this size to learn a watermark from without running out of memory.

    Learning holds all its sample pages in memory at once (twice, briefly). Big pages - a
    300 dpi scan is 25 MB each - get fewer samples; 8 or more is still plenty for the median."""
    free = available_memory_gb()
    budget = 600e6 if free is None else float(np.clip(free * 0.15, 0.15, 0.8)) * 2 ** 30
    return int(max(5, min(wanted, budget // (2 * width * height * 3))))


def _stack_median(stack, chunk=64, tol=6):
    """Per-pixel median, plus the fraction of pages that agree with it (within tol levels).

    Agreement separates truly static pixels from places where page content merely
    happens to overlap on about half the pages (the median there is a meaningless mix)."""
    n, h, w, c = stack.shape
    out = np.empty((h, w, c), np.uint8)
    agree = np.empty((h, w), np.float32)
    for y in range(0, h, chunk):
        part = stack[:, y:y + chunk]
        m = np.median(part, axis=0)
        out[y:y + chunk] = np.rint(m).astype(np.uint8)
        agree[y:y + chunk] = (np.abs(part - m).max(axis=3) <= tol).mean(axis=0)
    return out, agree


def _label_percentile(labels, values, n, q):
    """q-th percentile of values for each label 0..n-1 (0 where a label is empty)."""
    order = np.lexsort((values, labels))
    lab_s, val_s = labels[order], values[order]
    counts = np.bincount(lab_s, minlength=n)
    starts = np.concatenate([[0], np.cumsum(counts)[:-1]])
    idx = np.minimum(starts + (counts * q / 100.0).astype(np.int64), starts + np.maximum(counts - 1, 0))
    out = np.zeros(n, np.float32)
    ok = counts > 0
    out[ok] = val_s[idx[ok]]
    return out


def _estimate_background(med, bg_scale=0.15, tol=6):
    """Clean background under the median image. Returns (float32 HxWx3, 'uniform'|'local')."""
    q = med.astype(np.uint32) >> 3
    code = (q[..., 0] << 10) | (q[..., 1] << 5) | q[..., 2]
    top = np.bincount(code.ravel(), minlength=1 << 15).argmax()
    mode = np.median(med[code == top], axis=0)
    close = np.abs(med.astype(np.int16) - mode).max(axis=2) <= tol
    # Flat page colour? Judge by whether that colour shows up all over the page, not by how
    # much of the page it fills - a big watermark can cover a third of the area.
    h, w = close.shape
    gy, gx = np.linspace(0, h, 9).astype(int), np.linspace(0, w, 9).astype(int)
    tiles = np.array([close[gy[i]:gy[i + 1], gx[j]:gx[j + 1]].mean() for i in range(8) for j in range(8)])
    if close.mean() >= 0.85 or (close.mean() >= 0.35 and (tiles >= 0.05).mean() >= 0.9):
        bg = np.empty(med.shape, np.float32)
        bg[:] = mode
        return bg, "uniform"
    h, w = med.shape[:2]
    k = max(3, int(max(h, w) * bg_scale) | 1)
    rough = cv2.medianBlur(med, k)
    diff = np.abs(med.astype(np.int16) - rough).max(axis=2)
    hole = cv2.dilate((diff > 10).astype(np.uint8), np.ones((5, 5), np.uint8))
    bg = cv2.inpaint(med, hole, 5, cv2.INPAINT_TELEA)
    return bg.astype(np.float32), "local"


def _gamut_alpha(med, bg):
    """Smallest opacity a watermark could have at each pixel and still be a real colour."""
    delta = med.astype(np.float32) - bg
    up = np.where(delta > 0, delta / np.maximum(255.0 - bg, 1e-3), 0.0)
    down = np.where(delta < 0, -delta / np.maximum(bg, 1e-3), 0.0)
    return np.clip(np.maximum(up, down).max(axis=2), 0.0, 1.0).astype(np.float32)


def _smoothstep(x):
    x = np.clip(x, 0.0, 1.0)
    return x * x * (3.0 - 2.0 * x)


# --------------------------------------------------------------------------- model

@dataclass
class Group:
    id: int
    bbox: tuple            # x0, y0, x1, y1 (exclusive)
    area: int
    pieces: int
    kind: str              # 'translucent' | 'opaque' | 'mixed'
    core_alpha: float      # minimum-possible opacity at the group's core
    alpha_scale: float = 1.0
    fitted: bool = False
    selected: bool = False

    @property
    def alpha(self):
        return min(MAX_ALPHA, self.core_alpha * self.alpha_scale)


class WatermarkModel:
    def __init__(self, median, background, bg_mode, a_gamut, mask, grp_map, translucent_px, groups):
        self.median = median
        self.background = background
        self.bg_mode = bg_mode
        self.a_gamut = a_gamut
        self.mask = mask
        self.grp_map = grp_map
        self.translucent_px = translucent_px
        self.groups = groups
        self.selection = np.zeros(mask.shape, bool)
        self._plan = []

    @property
    def size(self):
        return self.median.shape[1], self.median.shape[0]

    # -- choosing what to remove
    def select(self, ids=None, exclude=None, include_opaque=False, regions=None,
               protect=None, alpha=None):
        """Choose what remove() erases. Default: every translucent piece.

        ids / exclude : group numbers to remove / leave alone. Naming a solid group
                        removes it; in a 'mixed' group only the translucent pieces go
                        unless include_opaque is set
        include_opaque: also take solid static elements (headers, logos!)
        regions       : [(x0,y0,x1,y1)] restrict removal to these boxes
        protect       : [(x0,y0,x1,y1)] never touch these boxes
        alpha         : override the fitted opacity (0-1) for selected groups
        """
        sel = self.mask.copy() if include_opaque else self.mask & self.translucent_px
        if ids is not None:
            ids = list(ids)
            solid = [g.id for g in self.groups if g.kind == "opaque" and g.id in ids]
            sel = (sel & np.isin(self.grp_map, ids)) | (self.mask & np.isin(self.grp_map, solid))
        if exclude:
            sel &= ~np.isin(self.grp_map, list(exclude))
        if regions:
            box = np.zeros_like(sel)
            for x0, y0, x1, y1 in regions:
                box[y0:y1, x0:x1] = True
            sel &= box
        for x0, y0, x1, y1 in (protect or []):
            sel[y0:y1, x0:x1] = False
        self.selection = sel
        self._plan = []
        for g in self.groups:
            x0, y0, x1, y1 = g.bbox
            sub = sel[y0:y1, x0:x1] & (self.grp_map[y0:y1, x0:x1] == g.id)
            ys, xs = np.nonzero(sub)
            g.selected = ys.size > 0
            if not g.selected:
                continue
            ys += y0
            xs += x0
            scale = g.alpha_scale if alpha is None else alpha / max(g.core_alpha, 1e-3)
            a = np.clip(self.a_gamut[ys, xs] * scale, 0.0, MAX_ALPHA)
            self._plan.append({
                "group": g, "ys": ys, "xs": xs,
                "med": self.median[ys, xs].astype(np.float32),
                "bg": self.background[ys, xs],
                "gain": (1.0 / (1.0 - a))[:, None],
                "core": self.a_gamut[ys, xs] >= 0.5 * g.core_alpha,
            })
        return self

    # -- applying it
    @staticmethod
    def _present(pix, med, bg):
        """Is the watermark actually on this page? (more pixels sit at 'median' than at 'background')"""
        t = 0.4 * np.abs(med - bg).max(axis=1)
        at_wm = np.abs(pix - med).max(axis=1) <= t
        at_bg = np.abs(pix - bg).max(axis=1) <= t
        return at_wm.sum() > at_bg.sum()

    def remove(self, rgb, tolerance=2.0):
        """Return (clean uint8 image, [ids of groups removed]). Unselected pixels are untouched."""
        if rgb.shape != self.median.shape:
            raise ValueError(f"image is {rgb.shape[1]}x{rgb.shape[0]}, model is {self.size[0]}x{self.size[1]}")
        out = rgb.copy()
        removed = []
        for p in self._plan:
            pix = rgb[p["ys"], p["xs"]].astype(np.float32)
            core = p["core"]
            if core.any() and not self._present(pix[core], p["med"][core], p["bg"][core]):
                continue                                   # page without this watermark
            d = pix - p["med"]
            if tolerance > 0:                              # don't amplify render noise
                dev = np.abs(d).max(axis=1)
                d *= _smoothstep((dev - tolerance) / tolerance)[:, None]
            clean = p["bg"] + d * p["gain"]
            out[p["ys"], p["xs"]] = np.clip(np.rint(clean), 0, 255).astype(np.uint8)
            removed.append(p["group"].id)
        return out, removed

    # -- reporting
    def preview(self):
        """Median image with selected pixels tinted and every group boxed and numbered."""
        img = self.median.copy()
        tint = np.array([255, 0, 255], np.float32)
        s = self.selection
        img[s] = (0.45 * img[s] + 0.55 * tint).astype(np.uint8)
        th = max(1, round(max(img.shape[:2]) / 900))
        fs = max(0.5, max(img.shape[:2]) / 1800)
        for g in self.groups:
            x0, y0, x1, y1 = g.bbox
            col = (0, 160, 0) if g.selected else (230, 130, 0)
            cv2.rectangle(img, (x0, y0), (x1 - 1, y1 - 1), col, th)
            cv2.putText(img, f"#{g.id}", (x0 + 3, max(y0 - 4, int(22 * fs))),
                        cv2.FONT_HERSHEY_SIMPLEX, fs, col, th + 1, cv2.LINE_AA)
        return img

    def summary(self):
        w, h = self.size
        lines = [f"  background: {self.bg_mode}   static groups found: {len(self.groups)}",
                 "    id  action   kind         opacity  pieces    area  box (x0,y0,x1,y1)"]
        for g in self.groups:
            act = "REMOVE" if g.selected else "keep"
            op = f"{g.alpha:5.2f}{'*' if g.fitted else ' '}"
            lines.append(f"   {g.id:3d}  {act:7s}  {g.kind:11s}  {op}  {g.pieces:6d}  {g.area:6d}  {g.bbox}")
        if any(g.fitted for g in self.groups):
            lines.append("    (* opacity fitted from text crossing the watermark)")
        return "\n".join(lines)


# --------------------------------------------------------------------------- learning

def learn_model(images, lo=2.0, hi=8.0, min_area=8, merge=0.015, opaque=0.6,
                bg_scale=0.15, fit_alpha=True, stable=0.45):
    """Learn the static watermark from >= 3 same-sized RGB uint8 pages.

    lo, hi   : hysteresis thresholds (grey levels) on |median - background|
    min_area : drop static specks smaller than this many pixels
    merge    : pieces closer than this fraction of the diagonal form one group
    opaque   : pieces whose core opacity reaches this are 'solid', not watermark
    bg_scale : (non-uniform pages) background filter size as fraction of long side
    stable   : a pixel is static only if at least this fraction of pages agree with the median
    """
    if len(images) < 3:
        raise ValueError("need at least 3 images to tell watermark from content")
    stack = np.stack(images)
    med, agree = _stack_median(stack)
    bg, bg_mode = _estimate_background(med, bg_scale)
    a_gamut = _gamut_alpha(med, bg)
    h, w = med.shape[:2]

    # static elements: hysteresis threshold on |median - background|
    diff = np.abs(med.astype(np.float32) - bg).max(axis=2)
    static = agree >= stable
    n, lab = cv2.connectedComponents(((diff >= lo) & static).astype(np.uint8), connectivity=8)
    keep = np.zeros(n, bool)
    keep[np.unique(lab[(diff >= hi) & static])] = True
    keep[0] = False
    mask = keep[lab]

    # pixels inside the watermark where page text overlapped too often for a stable
    # median: borrow the watermark colour from the stable pixels around them
    closed = cv2.morphologyEx(mask.astype(np.uint8), cv2.MORPH_CLOSE, np.ones((5, 5), np.uint8)).astype(bool)
    holes = closed & ~mask & ~static
    if holes.any():
        med = cv2.inpaint(med, holes.astype(np.uint8), 3, cv2.INPAINT_TELEA)
        a_gamut = _gamut_alpha(med, bg)
        mask |= holes

    # pieces -> translucent or opaque
    n, lab, stats, _ = cv2.connectedComponentsWithStats(mask.astype(np.uint8), connectivity=8)
    small = stats[:, cv2.CC_STAT_AREA] < min_area
    small[0] = False
    mask &= ~small[lab]
    piece_core = _label_percentile(lab[mask], a_gamut[mask], n, 90)   # robust "solid part" opacity
    piece_translucent = piece_core < opaque
    piece_translucent[0] = False
    translucent_px = piece_translucent[lab] & mask

    # nearby pieces -> groups (for reporting / selection)
    r = max(2, int(merge * math.hypot(h, w)))
    ker = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (2 * r + 1, 2 * r + 1))
    grown = cv2.dilate(mask.astype(np.uint8), ker)
    ng, glab = cv2.connectedComponents(grown, connectivity=8)
    glab_m = np.where(mask, glab, 0)
    areas = np.bincount(glab_m.ravel(), minlength=ng)
    areas[0] = 0
    order = [g for g in np.argsort(-areas) if areas[g] > 0]
    remap = np.zeros(ng, np.int32)
    for new, old in enumerate(order, 1):
        remap[old] = new
    grp_map = remap[glab_m]

    piece_ids = np.unique(lab[mask])
    piece_grp = np.zeros(n, np.int32)
    piece_grp[lab[mask]] = grp_map[mask]
    groups = []
    for gid in range(1, len(order) + 1):
        ps = piece_ids[piece_grp[piece_ids] == gid]
        st = stats[ps]
        x0 = int(st[:, cv2.CC_STAT_LEFT].min())
        y0 = int(st[:, cv2.CC_STAT_TOP].min())
        x1 = int((st[:, cv2.CC_STAT_LEFT] + st[:, cv2.CC_STAT_WIDTH]).max())
        y1 = int((st[:, cv2.CC_STAT_TOP] + st[:, cv2.CC_STAT_HEIGHT]).max())
        tr = piece_translucent[ps]
        kind = "translucent" if tr.all() else ("opaque" if not tr.any() else "mixed")
        gsel = (grp_map == gid) & (translucent_px if tr.any() else mask)
        core = float(np.percentile(a_gamut[gsel], 90))
        groups.append(Group(gid, (x0, y0, x1, y1), int(areas[order[gid - 1]]), len(ps), kind, core))

    model = WatermarkModel(med, bg, bg_mode, a_gamut, mask, grp_map, translucent_px, groups)
    if fit_alpha:
        _fit_alpha(model, stack, grown)
    model.select()
    return model


def _fit_alpha(model, stack, grown, max_px=150_000, seed=0):
    """Opacity from contrast: ink crossing a watermark of opacity a deviates from the
    median by (1-a) times what the same ink deviates from background elsewhere."""
    rng = np.random.default_rng(seed)
    step = 4
    outside = grown[::step, ::step] == 0
    bg_s = model.background[::step, ::step][outside]
    devs = []
    for img in stack:
        d = np.abs(img[::step, ::step][outside].astype(np.float32) - bg_s).max(axis=1)
        devs.append(d[d > INK_DEV])
    devs = np.concatenate(devs) if devs else np.empty(0)
    if devs.size < 200:
        return                                             # no reference ink on the pages
    ink_out = float(np.percentile(devs, 98))

    for g in model.groups:
        if g.kind == "opaque":
            continue
        x0, y0, x1, y1 = g.bbox
        sub = (model.grp_map[y0:y1, x0:x1] == g.id) & model.translucent_px[y0:y1, x0:x1] \
            & (model.a_gamut[y0:y1, x0:x1] >= 0.7 * g.core_alpha)
        ys, xs = np.nonzero(sub)
        if ys.size == 0:
            continue
        if ys.size > max_px:
            pick = rng.choice(ys.size, max_px, replace=False)
            ys, xs = ys[pick], xs[pick]
        ys += y0
        xs += x0
        med = model.median[ys, xs].astype(np.float32)
        bgv = model.background[ys, xs]
        inside, total = [], 0
        for img in stack:
            pix = img[ys, xs].astype(np.float32)
            if not WatermarkModel._present(pix, med, bgv):
                continue
            d = np.abs(pix - med).max(axis=1)
            inside.append(d[d > INK_DEV])
            total += d.size
        inside = np.concatenate(inside) if inside else np.empty(0)
        if inside.size < max(50, 0.002 * total):
            continue                                       # nothing ever crosses this watermark
        gain = np.clip(float(np.percentile(inside, 98)) / ink_out, 1.0 - MAX_ALPHA, 1.0)
        scale = (1.0 - gain) / max(g.core_alpha, 1e-3)
        g.alpha_scale = float(np.clip(scale, 1.0, MAX_ALPHA / max(g.core_alpha, 1e-3)))
        g.fitted = True


# --------------------------------------------------------------------------- searchable PDF (OCR)

_OCR = {"name": None, "rapid": None, "tesseract": None, "ps1": None}
OCR_LABELS = {"rapid": "RapidOCR", "tesseract": "Tesseract", "windows": "Windows built-in OCR"}

_WINOCR_PS1 = r"""
param([string]$Path)
$ErrorActionPreference = 'Stop'
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Add-Type -AssemblyName System.Runtime.WindowsRuntime
$null = [Windows.Media.Ocr.OcrEngine, Windows.Foundation, ContentType = WindowsRuntime]
$null = [Windows.Graphics.Imaging.BitmapDecoder, Windows.Foundation, ContentType = WindowsRuntime]
$null = [Windows.Storage.StorageFile, Windows.Storage, ContentType = WindowsRuntime]
$asTask = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and
    $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1' })[0]
function Await($op, $type) {
    $task = $asTask.MakeGenericMethod($type).Invoke($null, @($op))
    $task.Wait(-1) | Out-Null
    $task.Result
}
$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages()
if ($null -eq $engine) { throw 'Windows has no OCR language pack installed.' }
$file = Await ([Windows.Storage.StorageFile]::GetFileFromPathAsync($Path)) ([Windows.Storage.StorageFile])
$stream = Await ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream])
$decoder = Await ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
$bitmap = Await ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
$result = Await ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])
foreach ($line in $result.Lines) {
    $x0 = [double]::MaxValue; $y0 = [double]::MaxValue; $x1 = 0.0; $y1 = 0.0
    foreach ($w in $line.Words) {
        $r = $w.BoundingRect
        if ($r.X -lt $x0) { $x0 = $r.X }
        if ($r.Y -lt $y0) { $y0 = $r.Y }
        if (($r.X + $r.Width) -gt $x1) { $x1 = $r.X + $r.Width }
        if (($r.Y + $r.Height) -gt $y1) { $y1 = $r.Y + $r.Height }
    }
    $text = ($line.Text -replace "[\t\r\n]", ' ')
    [Console]::Out.WriteLine(('{0:F1}' -f $x0) + "`t" + ('{0:F1}' -f $y0) + "`t" + ('{0:F1}' -f $x1) + "`t" + ('{0:F1}' -f $y1) + "`t" + $text)
}
$stream.Dispose()
"""


def parse_pages(text, count):
    """'all', '3', '1-3, 7' ... -> sorted page numbers (starting at 0) out of `count` pages.

    Raises ValueError with a message for the user when the text makes no sense."""
    text = (text or "").strip().lower()
    if text in ("", "all", "*"):
        return list(range(count))
    chosen = set()
    for part in text.replace(";", ",").split(","):
        part = part.strip()
        if not part:
            continue
        try:
            if "-" in part:
                a, b = part.split("-", 1)
                a, b = int(a or 1), int(b or count)
            else:
                a = b = int(part)
        except ValueError:
            raise ValueError(f"'{part}' is not a page number. Use for example  1-3  or  2, 5, 9  or  all.")
        if a < 1 or b < a:
            raise ValueError(f"'{part}' is not a valid page range.")
        chosen.update(range(a - 1, min(b, count)))
    if not chosen:
        raise ValueError(f"None of those pages exist - there are {count} page(s).")
    return sorted(chosen)


def natural_key(path):
    """Sort key that puts page_2 before page_10."""
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", Path(path).name)]


def _ocr_upscale(rgb):
    """The page as the engine gets it: sizing is done by ocr_lines, which reads the page at several sizes."""
    return rgb, 1


def _temp_png(rgb):
    fd, name = tempfile.mkstemp(suffix=".png", prefix="ocr_")
    os.close(fd)
    Image.fromarray(rgb).save(name, "PNG")
    return name


def _rapid_device(engine):
    """What RapidOCR's models are really running on, asked of the loaded models themselves - not what
    was requested: "graphics card (DirectML)", "graphics card (CUDA)" or "processor"."""
    names = []
    for part in ("text_det", "text_rec"):
        try:
            names.append(getattr(getattr(engine, part).session, "session").get_providers()[0])
        except Exception:
            names.append("")
    label = {"CUDAExecutionProvider": "graphics card (CUDA)", "DmlExecutionProvider": "graphics card (DirectML)",
             "CPUExecutionProvider": "processor"}
    got = [label.get(n, n.replace("ExecutionProvider", "")) for n in names if n] or ["unknown"]
    if len(set(got)) == 1:
        return got[0]
    return f"{got[0]} for finding text, {got[1]} for reading it"


def _rapid_lines_big(rgb):
    """RapidOCR on the page at its full size. It normally shrinks a page to 2,000 pixels first, so this
    is a reading at another size - a second opinion of its own. Slow on a processor, quick on a card."""
    return _rapid_lines(rgb, side=4800)


def _rapid_words(crops):
    """Read small pictures of single words (no search for text: each picture is one line). A list of
    (text, confidence), ("", 0) where it failed."""
    out = []
    if _OCR.get("rapid") is None:
        return [("", 0.0)] * len(crops)
    for crop in crops:
        try:
            res = _rapid_run(np.ascontiguousarray(crop[..., ::-1]), use_det=False, use_cls=False)
            texts, scores = list(getattr(res, "txts", None) or []), list(getattr(res, "scores", None) or [])
            out.append((" ".join(t for t in texts if t).strip(), float(min(scores)) if scores else 0.0))
        except Exception:
            out.append(("", 0.0))
    return out


# ---- the graphics card can fail in the middle of a run -----------------------------------------
# (out of memory, or the driver resets it: "The GPU device instance has been suspended"). The run must
# carry on. Each fault steps the whole program - this process and its helpers - one level down:
#   0  everything: larger models, the second full-size reading, second looks
#   1  the card, but lightly: standard models, no full-size reading
#   2  the processor
# The level lasts until the program is closed; the next start tries the card again.
os.environ.setdefault("SNAPCLEAN_MAIN", str(os.getpid()))     # helper processes inherit it


def _gpu_file():
    return Path(tempfile.gettempdir()) / f"snapclean_gpu_{os.environ.get('SNAPCLEAN_MAIN', '0')}.txt"


def _short_error(e):
    """The line of an error that says what went wrong (onnxruntime's are many lines long)."""
    lines = [ln.strip() for ln in str(e).strip().splitlines() if ln.strip()]
    best = [ln for ln in lines if re.search(r"887A|ONNXRuntimeError|Error|error|not |cannot|failed", ln)]
    text = (best[-1] if best else lines[-1] if lines else "") or e.__class__.__name__
    text = re.sub(r"[A-Za-z]:\\[^ ]*\\", "", text)            # long build paths say nothing
    return f"{e.__class__.__name__}: {text}"[-320:] if e.__class__.__name__ not in text else text[-320:]


def _card_choice(save=None):
    """Which card the reader works on, found once per run of the program and shared with the helper
    processes: {"card": name or None (none works), "large": larger models loaded}. None if not known yet."""
    f = _gpu_file().with_suffix(".card")
    try:
        if save is not None:
            f.write_text(json.dumps(save))
            return save
        return json.loads(f.read_text())
    except Exception:
        return None


def _gpu_level():
    try:
        return max(int(_gpu_file().read_text().split()[0]), _OCR.get("min_level", 0))
    except Exception:
        return _OCR.get("min_level", 0)


def _gpu_fault():
    try:
        text = _gpu_file().read_text().split("\n", 1)
        return text[1].strip() if len(text) > 1 else ""
    except Exception:
        return ""


def _gpu_step_down(why="", to=None):
    level = min(2, _gpu_level() + 1) if to is None else to
    try:
        _gpu_file().write_text(f"{level}\n{why}")
    except Exception:
        pass
    return level


class _CardTurn:
    """One process at a time on the graphics card. Several helper processes each pushing a full page
    through it at once is what runs it out of memory; the rest of their work still runs side by side."""

    def __enter__(self):
        self.f = None
        try:
            self.f = open(_gpu_file().with_suffix(".lock"), "a+b")
            if sys.platform.startswith("win"):
                import msvcrt
                self.f.seek(0)
                while True:
                    try:
                        msvcrt.locking(self.f.fileno(), msvcrt.LK_LOCK, 1)     # waits up to 10 s, then raises
                        break
                    except OSError:
                        continue
            else:
                import fcntl
                fcntl.flock(self.f, fcntl.LOCK_EX)
        except Exception:
            self.f = None
        return self

    def __exit__(self, *a):
        try:
            if self.f is not None:
                if sys.platform.startswith("win"):
                    import msvcrt
                    self.f.seek(0)
                    msvcrt.locking(self.f.fileno(), msvcrt.LK_UNLCK, 1)
                self.f.close()
        except Exception:
            pass
        return False


def _rapid_run(image, **how):
    """Run RapidOCR; on the graphics card, one process at a time."""
    if _OCR.get("gpu"):
        with _CardTurn():
            return _OCR["rapid"](image, **how)
    return _OCR["rapid"](image, **how)


def _rapid_lines(rgb, side=0):
    level = _gpu_level()
    if _OCR.get("rapid") is not None and _OCR.get("rapid_level", 0) != level:
        _OCR["rapid"], _OCR["device"] = None, ""        # another process hit a fault: start again lower
    try:
        return _rapid_lines_at(rgb, side, level)
    except Exception as e:
        if not _OCR.get("gpu") or isinstance(e, MemoryError):
            raise
        # the card failed. Step down and read this page again.
        why = (str(e).strip().splitlines() or [e.__class__.__name__])[-1][-300:]
        if _gpu_level() <= level:                       # unless another process already stepped it down
            _gpu_step_down(why, to=min(2, level + 1))
            _OCR["min_level"] = min(2, level + 1)       # holds even if the note could not be written
        _OCR["rapid"], _OCR["device"] = None, ""
        return _rapid_lines(rgb, side)


def _rapid_lines_at(rgb, side, level):
    if _OCR["rapid"] is None:
        _OCR["rapid_level"] = level
        import logging
        logging.getLogger("RapidOCR").setLevel(logging.ERROR)
        from rapidocr import RapidOCR
        # the per-line "is it upside down?" classifier is off: on upright pages it
        # occasionally flips a good line and turns it into garbage
        params = {"Global.use_cls": False}
        if _WORKER.get("few_threads"):                 # several workers share the CPU
            params["EngineConfig.onnxruntime.intra_op_num_threads"] = 2
        # A graphics card, if onnxruntime on this computer can use one: NVIDIA through CUDA, any
        # modern card on Windows through DirectML (the onnxruntime-directml package).
        gpu, _OCR["gpu"] = (_graphics_card() if level < 2 else None) or ({}, "")
        _OCR["rapid"] = None
        _OCR["models"] = _OCR["which_card"] = ""
        want_large = os.environ.get("DEWATERMARK_MODELS", "") == "large" or \
            (bool(gpu) and level < 1 and os.environ.get("DEWATERMARK_MODELS", "") != "small")
        probe = np.full((80, 360, 3), 255, np.uint8)
        cv2.putText(probe, "TEST 123", (20, 55), cv2.FONT_HERSHEY_SIMPLEX, 1.4, (0, 0, 0), 3, cv2.LINE_AA)

        def build(card, large):
            """A reader that has really read something on the card asked for (or on the processor, card=None)."""
            p = dict(params)
            if card is not None:
                p.update(gpu)
                if card[1]:
                    # Not through RapidOCR's settings: it hands them on in its own settings type, which
                    # onnxruntime refuses ("'providers' values must be ... (string, dict) tuples").
                    from rapidocr.inference_engine.onnxruntime import provider_config as _pc
                    chosen = dict(card[1])
                    _pc.ProviderConfig.dml_ep_cfg = lambda self, _c=chosen: dict(_c)
            if large:
                from rapidocr.utils.typings import ModelType
                p.update({"Det.model_type": ModelType.MEDIUM, "Rec.model_type": ModelType.MEDIUM})
            engine = RapidOCR(params=p)
            with _CardTurn():
                engine(probe, use_det=True, use_cls=False, use_rec=True)     # loads (and first downloads) the models
            if card is not None and "graphics card" not in _rapid_device(engine):
                raise RuntimeError("the reader did not start on the graphics card")   # it quietly fell back
            return engine

        if gpu:
            # A laptop has two cards, and DirectML's first one is usually the weak one built into the
            # processor - which is also the one that hangs. So: the high-performance card first, then
            # each card by number. What works is noted for the helper processes, so only one of them searches.
            dml = "EngineConfig.onnxruntime.use_dml" in gpu
            cards = [("the high-performance card", {"performance_preference": "high_performance", "device_filter": "gpu"}),
                     ("card 1", {"device_id": "1"}), ("card 0", {"device_id": "0"})] if dml else [("", None)]
            if os.environ.get("DEWATERMARK_CARD", "").isdigit():
                n = os.environ["DEWATERMARK_CARD"]
                cards = [(f"card {n}", {"device_id": n})]
            known = _card_choice()
            if known is not None:
                cards = [c for c in cards if c[0] == known.get("card")] if known.get("card") is not None else []
                want_large = want_large and bool(known.get("large", True))
            found = False
            errors = []                                 # why each card would not do: said in the log, not swallowed
            for large in ([True] if want_large else []) + [False]:
                for card in cards:
                    for attempt in (1, 2):
                        try:
                            _OCR["rapid"] = build(card, large)
                            _OCR["models"], _OCR["which_card"] = ("larger models" if large else ""), card[0]
                            found = True
                            break
                        except BaseException as e:
                            if isinstance(e, KeyboardInterrupt):
                                raise
                            why = _short_error(e)
                            errors.append(f"{card[0] or 'the card'}{', larger models' if large else ''}: {why}")
                            # a card that was busy or asleep for a moment (the driver "suspends" it): once more
                            if attempt == 1 and re.search(r"887A000[567]|suspended|removed|not respond", why, re.I):
                                time.sleep(2.0)
                                continue
                            break
                    if found:
                        break
                if found:
                    break
            _OCR["card_errors"] = errors
            if known is None:
                _card_choice({"card": _OCR["which_card"] if found else None, "large": bool(_OCR["models"]), "errors": errors[-8:]})
            elif not found and not cards:
                _OCR["card_errors"] = list(known.get("errors") or [])
            if not found:
                gpu, _OCR["gpu"] = {}, ""
        if _OCR["rapid"] is None:
            if os.environ.get("DEWATERMARK_MODELS", "") == "large" and not gpu:
                try:
                    _OCR["rapid"], _OCR["models"] = build(None, True), "larger models"
                except BaseException as e:
                    if isinstance(e, KeyboardInterrupt):
                        raise
        if _OCR["rapid"] is None:
            try:
                _OCR["rapid"] = RapidOCR(params=params)
            except Exception:
                _OCR["rapid"] = RapidOCR(params={"Global.use_cls": False})
        for name in list(logging.root.manager.loggerDict):
            if "rapidocr" in name.lower():
                logging.getLogger(name).setLevel(logging.ERROR)
    usual = getattr(_OCR["rapid"], "max_side_len", None)
    try:
        if side and usual:
            _OCR["rapid"].max_side_len = max(side, usual)
        # said outright: a second look at single words (use_det=False) would otherwise stay in force
        res = _rapid_run(np.ascontiguousarray(rgb[..., ::-1]), use_det=True, use_cls=False, use_rec=True)
    finally:
        if side and usual:
            _OCR["rapid"].max_side_len = usual
    if not _OCR.get("device"):
        _OCR["device"] = _rapid_device(_OCR["rapid"])
        if _OCR.get("which_card") and "graphics card" in _OCR["device"]:
            _OCR["device"] = _OCR["device"].replace(")", ", " + _OCR["which_card"] + ")", 1)
        _OCR["device"] += ", " + _OCR["models"] if _OCR.get("models") else ""
        if level >= 2 and _graphics_card():
            _OCR["device"] = "processor (after a card fault)"
    boxes, texts = getattr(res, "boxes", None), getattr(res, "txts", None)
    if boxes is None or texts is None:
        return []
    scores = getattr(res, "scores", None)
    scores = list(scores) if scores is not None else [1.0] * len(texts)
    out = []
    for quad, text, score in zip(boxes, texts, scores):
        quad = np.asarray(quad, np.float32)
        out.append((text or "", float(quad[:, 0].min()), float(quad[:, 1].min()),
                    float(quad[:, 0].max()), float(quad[:, 1].max()), float(score)))
    return out


def _tesseract_lines(rgb):
    big, f = _ocr_upscale(rgb)
    png = _temp_png(big)
    try:
        done = subprocess.run([_OCR["tesseract"], png, "stdout", "tsv"], stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, creationflags=_NO_WINDOW)
    finally:
        os.unlink(png)
    if done.returncode != 0:
        raise RuntimeError("Tesseract failed: " + done.stderr.decode("utf-8", "replace")[-400:])
    words = {}
    for row in done.stdout.decode("utf-8", "replace").splitlines()[1:]:
        c = row.split("\t")
        if len(c) < 12 or c[0] != "5" or not c[11].strip():
            continue
        try:
            conf = float(c[10]) / 100.0
        except ValueError:
            conf = 0.0
        x, y, w, h = (int(v) for v in c[6:10])
        words.setdefault((c[2], c[3], c[4]), []).append((c[11].strip(), x, y, x + w, y + h, conf))
    out = []
    for line in words.values():
        height = float(np.median([w[4] - w[2] for w in line]))
        run = []
        for w in line + [None]:
            rule = w is not None and not w[0].strip("|_[]—-=~")          # a table rule read as a character
            far = w is not None and run and w[1] - run[-1][3] > 2.0 * max(height, 8)   # next table cell
            if w is None or rule or far:
                if run:
                    out.append((" ".join(t[0] for t in run), min(t[1] for t in run) / f, min(t[2] for t in run) / f,
                                max(t[3] for t in run) / f, max(t[4] for t in run) / f, [t[5] for t in run],
                                [(t[1] / f, t[3] / f) for t in run]))
                run = []
            if w is not None and not rule:
                run.append(w)
    return out


def _windows_lines(rgb):
    if _OCR["ps1"] is None:
        fd, name = tempfile.mkstemp(suffix=".ps1", prefix="winocr_")
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(_WINOCR_PS1)
        _OCR["ps1"] = name
    big, f = _ocr_upscale(rgb)
    png = _temp_png(big)
    try:
        done = subprocess.run(["powershell.exe", "-NoProfile", "-NonInteractive", "-ExecutionPolicy", "Bypass",
                               "-File", _OCR["ps1"], png], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              creationflags=_NO_WINDOW)
    finally:
        os.unlink(png)
    if done.returncode != 0:
        raise RuntimeError("Windows OCR failed: " + done.stderr.decode("utf-8", "replace")[-600:])
    out = []
    for row in done.stdout.decode("utf-8", "replace").splitlines():
        c = row.split("\t", 4)
        if len(c) == 5:
            try:
                x0, y0, x1, y1 = (float(v.replace(",", ".")) / f for v in c[:4])
            except ValueError:
                continue
            out.append((c[4], x0, y0, x1, y1, 1.0))
    return out


def _graphics_card():
    """(RapidOCR settings, description) if onnxruntime on this computer can use a graphics card, else None.
    NVIDIA cards through CUDA (the onnxruntime-gpu package), any modern card on Windows through DirectML
    (the onnxruntime-directml package). DEWATERMARK_GPU=0 turns it off."""
    if os.environ.get("DEWATERMARK_GPU", "1") == "0":
        return None
    try:
        import onnxruntime
        have = onnxruntime.get_available_providers()
    except Exception:
        return None
    if "CUDAExecutionProvider" in have:
        return {"EngineConfig.onnxruntime.use_cuda": True}, "graphics card (CUDA)"
    if "DmlExecutionProvider" in have:
        return {"EngineConfig.onnxruntime.use_dml": True}, "graphics card (DirectML)"
    return None


def graphics_card_test(say=None):
    """Try the graphics card step by step and say what happens at each: onnxruntime on its own first, then
    the text reader. Returns the report as text."""
    out = []

    def note(text=""):
        out.append(text)
        if say:
            say(text)

    import platform
    note(f"Graphics card test   {time.strftime('%Y-%m-%d %H:%M:%S')}")
    note(f"Python {platform.python_version()}   {platform.platform()}")
    try:
        import onnxruntime as ort
        note(f"onnxruntime {ort.__version__}   can run on: {', '.join(ort.get_available_providers())}")
    except Exception as e:
        note(f"onnxruntime could not be loaded: {e}")
        return "\n".join(out)
    try:
        from importlib import metadata
        for name in ("rapidocr", "onnxruntime", "onnxruntime-directml", "onnxruntime-gpu"):
            try:
                note(f"  installed: {name} {metadata.version(name)}")
            except Exception:
                pass
    except Exception:
        pass
    note(f"Fault level kept from this run: {_gpu_level()}  {_gpu_fault()}")
    note(f"Card chosen earlier in this run: {_card_choice()}")
    provider = "DmlExecutionProvider" if "DmlExecutionProvider" in ort.get_available_providers() else \
        "CUDAExecutionProvider" if "CUDAExecutionProvider" in ort.get_available_providers() else ""
    if not provider:
        note("This onnxruntime has no graphics card support (no DirectML, no CUDA): nothing to test.")
        return "\n".join(out)
    # the reader on the processor: that gives the model files to try
    model = None
    try:
        import logging
        logging.getLogger("RapidOCR").setLevel(logging.ERROR)
        from rapidocr import RapidOCR
        plain = RapidOCR(params={"Global.use_cls": False})
        first = np.full((80, 360, 3), 255, np.uint8)
        cv2.putText(first, "TEST 123", (20, 55), cv2.FONT_HERSHEY_SIMPLEX, 1.4, (0, 0, 0), 3, cv2.LINE_AA)
        plain(first, use_det=True, use_cls=False, use_rec=True)
        model = getattr(plain.text_det.session.session, "_model_path", None)
        note(f"Reader on the processor: started.  Model: {model}")
    except Exception as e:
        note(f"Reader on the processor: FAILED - {_short_error(e)}")
    tries = [("no options (the first card)", {}), ("the high-performance card", {"performance_preference": "high_performance", "device_filter": "gpu"}),
             ("high performance, no filter", {"performance_preference": "high_performance"}),
             ("card 0", {"device_id": "0"}), ("card 1", {"device_id": "1"})] if provider.startswith("Dml") else [("the card", {})]
    note("")
    note(f"1. onnxruntime on its own, {provider}:")
    if model:
        for name, opts in tries:
            for settings in ("as it comes", "memory pattern off, one at a time"):
                try:
                    so = ort.SessionOptions()
                    so.log_severity_level = 3
                    if settings != "as it comes":
                        so.enable_mem_pattern = False
                        so.execution_mode = ort.ExecutionMode.ORT_SEQUENTIAL
                    t0 = time.time()
                    sess = ort.InferenceSession(model, sess_options=so, providers=[(provider, dict(opts)), "CPUExecutionProvider"])
                    got = sess.get_providers()
                    inp = sess.get_inputs()[0]
                    x = np.zeros((1, 3, 320, 320), np.float32)
                    sess.run(None, {inp.name: x})
                    t1 = time.time()
                    for _ in range(3):
                        sess.run(None, {inp.name: x})
                    how = f"OK on {got[0]}" if got[0] == provider else f"NOT ON THE CARD - fell back to {got[0]} without an error"
                    note(f"   {name:28s} {settings:34s} {how}  (load+first {t1 - t0:.2f}s, then {(time.time() - t1) / 3:.3f}s each)")
                    del sess
                except BaseException as e:
                    if isinstance(e, KeyboardInterrupt):
                        raise
                    note(f"   {name:28s} {settings:34s} FAILED - {_short_error(e)}")
    else:
        note("   (no model file to try it with)")
    note("")
    note("2. the text reader (RapidOCR) on the card:")
    probe = np.full((80, 360, 3), 255, np.uint8)
    cv2.putText(probe, "TEST 123", (20, 55), cv2.FONT_HERSHEY_SIMPLEX, 1.4, (0, 0, 0), 3, cv2.LINE_AA)
    card = _graphics_card()
    note(f"   what the program found: {card}")
    if card:
        for name, opts in tries[1:] if len(tries) > 1 else tries:
            try:
                p = {"Global.use_cls": False}
                p.update(card[0])
                if opts:
                    from rapidocr.inference_engine.onnxruntime import provider_config as _pc
                    _pc.ProviderConfig.dml_ep_cfg = lambda self, _c=dict(opts): dict(_c)
                t0 = time.time()
                engine = RapidOCR(params=p)
                res = engine(probe, use_det=True, use_cls=False, use_rec=True)
                text = " ".join(getattr(res, "txts", None) or [])
                note(f"   {name:28s} started on: {_rapid_device(engine)};  read {text!r} in {time.time() - t0:.2f}s")
            except BaseException as e:
                if isinstance(e, KeyboardInterrupt):
                    raise
                note(f"   {name:28s} FAILED - {_short_error(e)}")
    note("")
    note("End of test.")
    return "\n".join(out)


def structure_lines(stats):
    """What the structured Word document was made of, for the log."""
    st = (stats or {}).get("structure")
    if not st:
        return []
    heads = st.get("h1", 0) + st.get("h2", 0) + st.get("h3", 0)
    return [f"  Structured Word document: {heads} heading(s), {st.get('list', 0)} list item(s), {st.get('caption', 0)} caption(s), "
            f"{st.get('body', 0)} paragraph(s); {st.get('joined', 0)} paragraph(s) joined where a column, a page or a picture had cut them; "
            f"{st.get('running', 0)} running head(s) and page number(s) taken out; "
            f"{st.get('centred', 0)} centred and {st.get('right', 0)} right-aligned paragraph(s).",
            "  It is a flowing document: it does not follow the original pages. Use Word's Navigation pane (View > "
            "Navigation Pane) to see the outline."]


def graphics_card_lines(stats=None):
    """Lines for the log about the graphics card. Before a run (no stats): whether one was detected.
    After a run: what the pages were really read on, counted page by page."""
    rapid = _OCR.get("name") == "rapid"
    card = _graphics_card() if rapid else None
    if stats is None:
        if not rapid:
            return ["Graphics card: not used - this text reader (Tesseract) only runs on the processor."]
        if card:
            lines = [f"Graphics card: DETECTED - {card[1]}. RapidOCR will read on it; Tesseract's second opinion "
                     "runs on the processor."]
            started = _OCR.get("device") or ""
            if started and "graphics card" not in started:
                lines.append("  But the reader could NOT start on any graphics card (tried the high-performance card, "
                             "card 1 and card 0) and is running on the processor.")
                reasons = list(_OCR.get("card_errors") or (_card_choice() or {}).get("errors") or [])
                if _gpu_level() >= 2 and _gpu_fault():
                    reasons.insert(0, "the card was given up after a fault earlier in this run: " + _gpu_fault())
                seen = []
                for r in reasons:
                    if r not in seen:
                        seen.append(r)
                for r in seen[:6]:
                    lines.append("    why - " + r)
                if not seen:
                    lines.append("    (no reason was recorded)")
                lines.append("    Setup > 'Test the graphics card...' tries each card on its own and saves a report.")
            elif started:
                extra = _extra_use()
                lines.append(f"  Running on: {started}.")
                lines.append("  With the graphics card: " + ", ".join(
                    [("larger reading models" if _OCR.get("models") else "standard reading models (the larger ones "
                      "could not be loaded)")] +
                    (["a second reading of each page at full size"] if extra["second"] else []) +
                    (["a second look at each doubtful word"] if extra["words"] else [])) + ".")
            return lines
        if os.environ.get("DEWATERMARK_GPU", "1") == "0":
            return ["Graphics card: switched off (DEWATERMARK_GPU=0). Reading on the processor."]
        return ["Graphics card: NOT detected by the reader (the installed onnxruntime has no graphics card "
                "support). Reading on the processor."]
    if not rapid:
        return []
    used = dict(stats.get("devices") or {})
    kept = used.pop("kept", 0)
    on_card = sum(k for d, k in used.items() if "graphics card" in d)
    fresh = sum(used.values())
    lines = []
    if on_card:
        which = ", ".join(sorted(d for d in used if "graphics card" in d)).replace(", larger models", " with the larger models")
        lines.append(f"Graphics card: USED - {on_card} of {fresh} page(s) read on the {which}.")
        if fresh > on_card:
            lines.append(f"  {fresh - on_card} page(s) were read on the processor instead.")
    elif fresh:
        lines.append(f"Graphics card: NOT used - {fresh} page(s) read on the processor" +
                     (f", although the {card[1]} was detected (the reader could not start on it)." if card else "."))
    level = _gpu_level()
    if level and card:
        lines.append("  The graphics card FAILED during the run" + (f" ({_gpu_fault()})" if _gpu_fault() else "") + ".")
        lines.append("  The program carried on " + ("on the card with the standard models and without the full-size reading."
                                                    if level == 1 else "on the processor.") +
                     " Nothing was lost; close and reopen the program to try the full card again.")
    if kept:
        lines.append(("Graphics card: not needed - " if not fresh else "  ") +
                     f"{kept} page(s) were not read again; their readings were kept from an earlier run.")
    return lines


def ensure_ocr_packages(status=None):
    """Get PyMuPDF and pick an OCR engine, installing what can be installed. Returns the engine's name.

    Engines, in order of preference: RapidOCR (pip; not yet available for the very newest
    Python releases), Tesseract (if installed on this computer), Windows' built-in OCR.
    Set the environment variable SNAPCLEAN_OCR to rapid / tesseract / windows to force one."""
    say = status or (lambda t: print(t, file=sys.stderr, flush=True))
    if not _have("pymupdf"):
        say("One-time setup: installing pymupdf...")
        ok, log = _pip(["pymupdf"]); exe = _python_exe()
        if not ok:
            raise RuntimeError("Could not install PyMuPDF, which writes the PDF.\n" + log[-800:] +
                               f'\nInstall it yourself with:\n    "{exe}" -m pip install pymupdf')
    if _OCR["name"]:
        return OCR_LABELS[_OCR["name"]]
    forced = os.environ.get("SNAPCLEAN_OCR", "").strip().lower()
    notes = []

    def try_rapid():
        if not _have("rapidocr", "onnxruntime"):
            if _setup_state().get("rapid_failed") == PYVER:      # already known not to install here
                notes.append(f"RapidOCR: its onnxruntime component has no build for Python {PYVER} yet.")
                return False
            say("One-time setup: installing the OCR engine (this can take a few minutes)...")
            # on Windows the DirectML build of onnxruntime, which can use the graphics card
            first = "onnxruntime-directml" if sys.platform.startswith("win") else "onnxruntime"
            ok, log, _ = _pip(["rapidocr", first])
            if (not ok or not _have("rapidocr", "onnxruntime")) and first != "onnxruntime":
                ok, log = _pip(["rapidocr", "onnxruntime"])
            if not ok or not _have("rapidocr", "onnxruntime"):
                v = f"{sys.version_info.major}.{sys.version_info.minor}"
                notes.append(f"RapidOCR: its onnxruntime component has no build for Python {v} yet.")
                return False
        if not _OCR.get("tesseract"):
            _OCR["tesseract"] = _find_tesseract()      # for the second opinion, if it is here
        if _OCR.get("rapid") is None and _graphics_card():
            say("Starting the text reader on the graphics card\n(the first time, its larger models are downloaded)...")
            try:
                _rapid_lines(np.full((64, 64, 3), 255, np.uint8))
            except Exception:
                _OCR["rapid"] = None
        return True

    def try_tesseract():
        _OCR["tesseract"] = _find_tesseract()
        if not _OCR["tesseract"]:
            notes.append("Tesseract: not installed.")
        return bool(_OCR["tesseract"])

    def try_windows():
        if not sys.platform.startswith("win"):
            return False
        say("Checking Windows' built-in OCR...")
        probe = np.full((80, 360, 3), 255, np.uint8)
        cv2.putText(probe, "TEST 123", (20, 55), cv2.FONT_HERSHEY_SIMPLEX, 1.4, (0, 0, 0), 3, cv2.LINE_AA)
        try:
            _windows_lines(probe)
            return True
        except Exception as e:
            notes.append(str(e).strip()[-400:])
            return False

    for name, attempt in (("rapid", try_rapid), ("tesseract", try_tesseract), ("windows", try_windows)):
        if forced and forced != name:
            continue
        if attempt():
            _OCR["name"] = name
            label = OCR_LABELS[name]
            if name == "rapid":
                if _OCR.get("tesseract"):
                    label += " with Tesseract as a second opinion"
                card, started = _graphics_card(), _OCR.get("device") or ""
                if card and started and "graphics card" not in started:
                    label += ", on the processor (it would not start on a graphics card)"
                else:
                    label += f", on the {started.split(', larger')[0] if card and started else card[1]}" if card else \
                        ", on the processor (no graphics card support installed)"
            return label
    raise RuntimeError(
        "No OCR engine is available on this computer.\n\n" + "\n".join(notes) +
        "\n\nFix: install Tesseract by running this in a Command Prompt, then try again:\n"
        "    winget install -e --id UB-Mannheim.TesseractOCR\n"
        "(Alternatively run this program with Python 3.13, where RapidOCR installs by itself.)")


def ocr_lines(rgb, conf=False):
    """Recognise text on an RGB uint8 page. Returns [(text, x0, y0, x1, y1)] in pixels, one per line.

    With conf=True each item gains the engine's confidence, 0-1: one number for the line, or a
    list with one number per word."""
    if not _OCR["name"]:
        ensure_ocr_packages()
    found = _read_several(rgb)
    return found if conf else [item[:5] for item in found]


# Line heights (pixels) at which the page is read. One reading makes mistakes that depend on the size of
# the letters - "NFPA" becomes "NEPA" at one size and is right at the next - so the page is read at a
# few sizes and the readings are compared word by word. A word counts as agreed when two readings give
# exactly the same thing; where the first reading stands alone and the others agree, theirs is taken.
# The second and fourth are read from a darkened copy: thin strokes thicken, and the engine makes
# different mistakes there - which is what makes comparing the readings worth while.
_READ_HEIGHTS = {"tesseract": ((30.0, ""), (40.0, "dark"), (52.0, ""), (34.0, "dark")),
                 "windows": ((30.0, ""), (40.0, "dark"), (52.0, ""), (34.0, "dark")), "rapid": ((0.0, ""),)}


def _read_once(rgb, scale, look="", engine=None):
    engine = {"rapid": _rapid_lines, "rapid_big": _rapid_lines_big, "tesseract": _tesseract_lines,
              "windows": _windows_lines}[engine or _OCR["name"]]
    if look == "dark":
        rgb = _DARK_TABLE[rgb]
    if abs(scale - 1.0) > 0.02:
        how = cv2.INTER_AREA if scale < 1 else cv2.INTER_CUBIC
        rgb = cv2.resize(rgb, None, fx=scale, fy=scale, interpolation=how)
    else:
        scale = 1.0
    out = []
    for item in engine(rgb):
        t, x0, y0, x1, y1, c = item[:6]
        if t and t.strip() and x1 > x0 and y1 > y0:
            spans = [(a / scale, b / scale) for a, b in item[6]] if len(item) > 6 else None
            out.append((t.strip(), x0 / scale, y0 / scale, x1 / scale, y1 / scale, c, spans))
    return out


def _span_key(item):
    return (int(round(item[1])), int(round(item[2])), int(round(item[3])))


def word_spans(item):
    """Where the OCR engine itself saw each word of this line (left and right edge), if it said."""
    return _OCR.get("spans", {}).get(_span_key(item))


_DARK_TABLE = np.rint(255.0 * (np.arange(256) / 255.0) ** 1.8).astype(np.uint8)


def _close_words(a, b):
    """Two readings of what is plainly the same word (one or two characters apart)."""
    import difflib
    return abs(len(a) - len(b)) <= 2 and difflib.SequenceMatcher(None, a.lower(), b.lower()).ratio() >= 0.7


def votes_of(c):
    """How many readings of the page agreed on a word (0 = it was read only once), from its confidence."""
    return int(c)


def conf_of(c):
    return float(c) - int(c)


def _same_place(a, b):
    """Could these be two readings of one word (not of two neighbouring words)?"""
    if a == b:
        return True
    ca, cb = _core(a)[1].lower() or a.lower(), _core(b)[1].lower() or b.lower()
    if ca == cb:
        return True
    if abs(len(ca) - len(cb)) > max(2, 0.4 * max(len(ca), len(cb))):
        return False
    if max(len(ca), len(cb)) <= 3:                      # short: letters and digits swap ("I0" / "10", "of" / "ot")
        return len(ca) == len(cb) and sum(x != y for x, y in zip(ca, cb)) <= max(1, len(ca) - 1)
    import difflib
    return difflib.SequenceMatcher(None, ca, cb, autojunk=False).ratio() >= 0.5


def _read_several(rgb):
    """Read the page at several sizes and combine. Each word's confidence comes back as
    (number of readings that agree) + (the engine's own confidence, below 1)."""
    heights = _READ_HEIGHTS.get(_OCR["name"], ((0.0, ""),))
    first_scale = 2.0 if max(rgb.shape[:2]) < 1500 else 1.0
    first = _read_once(rgb, first_scale)
    _OCR["spans"] = {}
    # RapidOCR reads far better than Tesseract, but gives no second opinion of its own. Where Tesseract
    # is on the computer too, it reads the page twice as well: two engines that fail in different ways
    # agreeing on a word is the best confirmation there is, and Tesseract also says where each word is.
    hybrid = _OCR["name"] == "rapid" and bool(_OCR.get("tesseract")) and os.environ.get("DEWATERMARK_READINGS") != "1"
    if hybrid:
        heights = _READ_HEIGHTS["tesseract"]

    def remember(items):
        for item in items:
            if item[6] and len(item[6]) == len(item[0].split()):
                _OCR["spans"][_span_key(item)] = item[6]

    tall = [item[4] - item[2] for item in first if len(item[0]) >= 6]
    if len(heights) < 2 or len(tall) < 3 or os.environ.get("DEWATERMARK_READINGS") == "1":
        remember(first)
        return [(t, x0, y0, x1, y1, [min(v, 0.99) for v in c] if isinstance(c, list) else min(float(c), 0.99))
                for t, x0, y0, x1, y1, c, _ in first]
    line = float(np.median(tall))
    biggest = 7000.0 / max(rgb.shape[:2])
    readings, used = [], []
    for h, look in heights:
        scale = float(np.clip(h / line, 0.3, min(4.0, biggest)))
        if any(abs(scale / u - 1) < 0.08 and look == v for u, v in used):
            continue
        used.append((scale, look))
        if hybrid:
            try:
                readings.append(_read_once(rgb, scale, look, engine="tesseract"))
            except Exception:
                pass
        else:
            readings.append(first if abs(scale / first_scale - 1) < 0.08 and not look else _read_once(rgb, scale, look))
    trust = {id(r): 1.0 for r in readings}
    extra = _extra_use()
    if hybrid and readings:
        readings.append(first)
        trust[id(first)] = 1.6                          # RapidOCR's word outweighs one Tesseract reading, not two
        if extra["second"] and max(rgb.shape[:2]) > 2200:
            try:                                        # the page at full size: RapidOCR's own second reading
                big = _read_once(rgb, 1.0, "", engine="rapid_big")
                readings.append(big)
                trust[id(big)] = 1.2
            except Exception:
                pass
    if len(readings) < 2:
        remember(first)
        return [item[:6] for item in first]
    words = lambda item: item[0].split()
    doubts, boxes = [], []

    def sureness(item, n):
        c = item[5]
        return [float(v) for v in c] if isinstance(c, list) and len(c) == n else \
            [float(min(c) if isinstance(c, list) and c else (c if not isinstance(c, list) else 0.0))] * n

    def mean_conf(reading):
        got = [v for item in reading for v in sureness(item, len(words(item)))]
        return float(np.mean(got)) if got else 0.0

    import difflib
    # the reading the result is built on: with two engines, Tesseract's (it knows where each word is)
    base = max([r for r in readings if trust.get(id(r), 1.0) == 1.0] if hybrid else readings, key=mean_conf)
    remember(base)
    others = [r for r in readings if r is not base]
    out = []
    for item in base:
        toks = words(item)
        x0, y0, x1, y1 = item[1:5]
        alts = []
        for other in others:
            near = []
            for o in other:
                overlap = min(y1, o[4]) - max(y0, o[2])
                if overlap >= 0.5 * min(y1 - y0, o[4] - o[2]) and min(x1, o[3]) - max(x0, o[1]) > 0:
                    near.append(o)
            theirs = [t for o in sorted(near, key=lambda o: o[1]) for t in words(o)]
            alt = [None] * len(toks)
            for tag, a0, a1, b0, b1 in difflib.SequenceMatcher(None, toks, theirs, autojunk=False).get_opcodes():
                if tag == "equal":
                    alt[a0:a1] = theirs[b0:b1]
                elif tag == "replace" and a1 - a0 == b1 - b0:
                    # the same number of words differ - but are they the same words? Where one reading
                    # dropped a word and gained another, the rest sit one place along, and a neighbour
                    # would be taken for this word's other reading. Only look-alikes are paired.
                    for k in range(a1 - a0):
                        if _same_place(toks[a0 + k], theirs[b0 + k]):
                            alt[a0 + k] = theirs[b0 + k]
            alts.append(alt)
        conf, final = sureness(item, len(toks)), []
        for i, tok in enumerate(toks):
            seen = [a[i] for a in alts if a[i] is not None]
            cands = [tok] + seen
            weight = {}
            for t, r in [(tok, base)] + [(a[i], r) for a, r in zip(alts, others) if a[i] is not None]:
                weight[t] = weight.get(t, 0.0) + trust.get(id(r), 1.0)
            # the reading with most behind it; between equals, a real word, then this reading's own
            top = max(dict.fromkeys(cands), key=lambda t: (weight[t], known_word(t), t == tok))
            if hybrid and not known_word(top):
                # two engines: a real word from one beats a near-identical non-word from the other,
                # however many times the other said it (Tesseract repeats its own mistakes)
                real = [t for t in dict.fromkeys(cands) if known_word(t) and _close_words(t, top)]
                if real:
                    top = max(real, key=lambda t: weight[t])
            tok, votes = top, cands.count(top)
            rest = [a for a in cands if a != tok]
            if votes == 1 and known_word(tok) and all(not known_word(a) and _close_words(a, tok) for a in rest) \
                    and (len(rest) >= 2 and len(_core(tok)[1]) >= 4 or len(rest) >= 1 and len(_core(tok)[1]) >= 6):
                votes = 2                               # every other reading is a non-word a letter or two away
                                                        # from this real word: they were all looking at it
            final.append(tok)
            conf[i] = votes + min(conf[i], 0.99)
            if hybrid and extra["words"] and votes < 3 and sum(ch.isalnum() for ch in tok) >= 2:
                doubts.append((len(out), i, cands))
        out.append((" ".join(final), x0, y0, x1, y1, conf))
        boxes.append(word_spans(item))
    if doubts:
        _second_look(rgb, out, boxes, doubts)
    return out


def _extra_use():
    """What the graphics card is used for beyond the plain reading: {"second": RapidOCR reads the page a
    second time at full size, "words": it looks again at each doubtful word on its own}. Both are on with
    a graphics card and off without (far too slow); DEWATERMARK_EXTRA=1 / 0 forces them on / off."""
    forced = os.environ.get("DEWATERMARK_EXTRA", "")
    on = forced == "1" or (forced != "0" and "graphics card" in (_OCR.get("device") or ""))
    return {"second": on and _gpu_level() < 1 and os.environ.get("DEWATERMARK_EXTRA_SECOND", "1") != "0",
            "words": on and os.environ.get("DEWATERMARK_EXTRA_WORDS", "1") != "0"}


def _second_look(rgb, out, boxes, doubts):
    """Look again at each word the readings did not agree on: cut it out of the page, enlarge it and have
    RapidOCR read just that. A single word, big and alone, is an easier job than a page; what it reads
    counts as one more vote for a reading already on the table - it never brings in a new one."""
    H, W = rgb.shape[:2]
    crops, where = [], []
    for li, i, cands in doubts[:400]:
        t, x0, y0, x1, y1, conf = out[li]
        span = boxes[li]
        if not span or len(span) != len(t.split()):
            continue
        a, b = span[i]
        pad_x, pad_y = 0.25 * (y1 - y0), 0.12 * (y1 - y0)
        xa, xb = int(max(0, a - pad_x)), int(min(W, b + pad_x))
        ya, yb = int(max(0, y0 - pad_y)), int(min(H, y1 + pad_y))
        if xb - xa < 6 or yb - ya < 6:
            continue
        k = float(np.clip(64.0 / (yb - ya), 1.0, 4.0))
        crop = rgb[ya:yb, xa:xb]
        if k > 1.05:
            crop = cv2.resize(crop, None, fx=k, fy=k, interpolation=cv2.INTER_CUBIC)
        crops.append(np.ascontiguousarray(crop))
        where.append((li, i, cands))
    if not crops:
        return
    for (li, i, cands), (seen, sure) in zip(where, _rapid_words(crops)):
        seen = seen.strip()
        if os.environ.get("SNAPCLEAN_DEBUG_LOOKS"):
            print("LOOK", repr(out[li][0].split()[i]), "->", repr(seen), round(sure, 2), cands, flush=True)
        if not seen or " " in seen or sure < 0.6:
            continue
        t, x0, y0, x1, y1, conf = out[li]
        toks = t.split()
        tok = toks[i]
        if seen == tok:
            conf[i] = conf[i] + 1                       # one more reading that says the same
        elif seen in cands and known_word(seen) and not known_word(tok) and _close_words(seen, tok):
            toks[i] = seen                              # a real word that some reading already gave
            conf[i] = cands.count(seen) + 1 + (conf[i] - int(conf[i]))
            out[li] = (" ".join(toks), x0, y0, x1, y1, conf)


def enhance_page(rgb, info=None, scale=2, amount=0.8):
    """Enlarge a page `scale` times and sharpen the text edges. Returns (rgb, info).

    This makes small screen-captured text look crisper and read better by OCR; it cannot
    add detail that was never captured. The DPI is scaled too, so the page keeps its size."""
    info = dict(info or {})
    scale = int(scale)
    if scale > 1:
        rgb = cv2.resize(rgb, None, fx=scale, fy=scale, interpolation=cv2.INTER_CUBIC)
        if info.get("alpha") is not None:
            info["alpha"] = cv2.resize(info["alpha"], (rgb.shape[1], rgb.shape[0]), interpolation=cv2.INTER_CUBIC)
        try:
            if info.get("dpi"):
                info["dpi"] = (float(info["dpi"][0]) * scale, float(info["dpi"][1]) * scale)
        except (TypeError, ValueError, IndexError):
            info["dpi"] = None
    blur = cv2.GaussianBlur(rgb, (0, 0), 0.6 * max(scale, 1) + 0.4)
    rgb = cv2.addWeighted(rgb, 1.0 + amount, blur, -amount, 0)
    return rgb, info


def _letter_height(rgb):
    """The usual height, in pixels, of a letter on this page (0 if it cannot be told)."""
    grey = cv2.cvtColor(rgb, cv2.COLOR_RGB2GRAY) if rgb.ndim == 3 else rgb
    step = max(1, min(grey.shape[:2]) // 300)
    paper = float(np.median(grey[::step, ::step]))
    ink = (np.abs(grey.astype(np.int16) - paper) > 70).astype(np.uint8)
    n, _, stats, _ = cv2.connectedComponentsWithStats(ink, connectivity=8)
    if n < 60:
        return 0.0
    hgt, wid = stats[1:, cv2.CC_STAT_HEIGHT], stats[1:, cv2.CC_STAT_WIDTH]
    letters = hgt[(hgt >= 3) & (hgt <= 0.05 * grey.shape[0]) & (wid >= 2) & (wid <= 4 * hgt)]
    return float(np.median(letters)) if letters.size >= 40 else 0.0


def _auto_enlarge(rgb):
    """How many times to enlarge a page before its text is read and measured: 1, 2 or 3.

    Reading small type is not the trouble - the readers manage. Measuring it is: fitting a font to a
    word and checking the redrawn word against the picture needs more pixels than a letter six pixels
    high has, and on such pages four words in ten failed the checks and stayed pictures. Enlarged three
    times (nothing more than a smooth resize) the same pages pass like any other. Letters about 16
    pixels high are enough. DEWATERMARK_ENLARGE=0 turns this off, =2 or =3 forces a size."""
    forced = os.environ.get("DEWATERMARK_ENLARGE", "")
    if forced in ("0", "1"):
        return 1
    if forced in ("2", "3"):
        return int(forced)
    longest = max(rgb.shape[:2])
    if longest * 2 > 4400:
        return 1                                        # already a large picture
    tall = _letter_height(rgb)
    if tall <= 0:
        return 1
    return int(np.clip(math.ceil(16.0 / tall - 0.15), 1, 3 if longest * 3 <= 4400 else 2))


def _flatten_paper(rgb):
    """A photograph or a grey scan of a page, with its paper made white: (rgb, changed).

    Everything after this - finding the ink of a word, fitting a font to it, telling text from pictures -
    takes the paper to be white. On a photographed page the paper is grey and unevenly lit, and then no
    line of it could be fitted with a font and the whole page was taken for one picture. Each colour is
    divided by what the paper is at that spot (found by wiping the text away and smoothing), so the paper
    comes out white and evenly lit and the ink keeps its colour. A page that is white already, or dark
    (light text on a dark ground, a photograph) is left alone. DEWATERMARK_PAPER=0 turns this off."""
    if os.environ.get("DEWATERMARK_PAPER", "") != "1":  # not on yet: see the typewritten test page (n5/t14)
        return rgb, False
    grey = rgb.mean(axis=2)
    small = grey[::4, ::4]
    paper = float(np.median(small))
    if paper >= 238 and float(np.percentile(small, 25)) >= 228:
        return rgb, False                               # white paper
    if paper < 110 or float((small < 0.6 * paper).mean()) > 0.35:
        return rgb, False                               # not ink on paper
    h, w = grey.shape
    f = max(1, int(round(max(h, w) / 700.0)))           # worked out on a small copy: the paper changes slowly
    low = cv2.resize(rgb, (max(1, w // f), max(1, h // f)), interpolation=cv2.INTER_AREA)
    k = max(9, int(round(0.03 * max(low.shape[:2]))) | 1)
    ground = cv2.morphologyEx(low, cv2.MORPH_CLOSE, cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (k, k)))   # the text wiped away
    ground = cv2.GaussianBlur(ground, (0, 0), 0.6 * k)
    ground = cv2.resize(ground, (w, h), interpolation=cv2.INTER_LINEAR).astype(np.float32)
    flat = rgb.astype(np.float32) / np.maximum(ground, 1.0)
    # the paper's own grain (a little under 1) goes to white; ink that never was black is made darker
    dark = float(np.clip(np.percentile(flat.mean(axis=2)[::4, ::4], 0.5), 0.0, 0.32))
    flat = np.clip((flat - dark) / (float(os.environ.get("DW_WHITE", "0.93")) - dark), 0.0, 1.0)
    return np.rint(flat * 255.0).astype(np.uint8), True


def _load_page(path):
    """A page picture ready for reading and re-typesetting: loaded, its paper made white if it was a
    photograph, and enlarged if its type is small. Returns (rgb, info, how many times it was enlarged)."""
    rgb, info = load_png(path)
    rgb, flattened = _flatten_paper(rgb)
    if flattened and isinstance(info, dict):
        info["flattened"] = True
    times = _auto_enlarge(rgb)
    if times > 1:
        rgb, info = enhance_page(rgb, info, times)
    return rgb, info, times


def _page_dpi(info, w, h):
    dpi = (info or {}).get("dpi")
    try:
        d = float(dpi[0]) if dpi else 0.0
    except (TypeError, ValueError, IndexError):
        d = 0.0
    return d if d >= 50 else max(w, h) / 11.0          # no DPI in the file: assume an 11-inch long side


# ---- re-typesetting: swap the picture of each word for real text in a matching font ----------

_FONT_FAMILIES = (
    "arial", "helvetica", "times new roman", "calibri", "segoe ui", "verdana", "tahoma", "georgia",
    "courier new", "consolas", "trebuchet ms", "garamond", "palatino linotype", "book antiqua",
    "century gothic", "candara", "corbel", "constantia", "franklin gothic", "lucida sans", "aptos",
    "roboto", "open sans", "lato", "inter", "source sans", "noto sans", "noto serif", "dejavu sans",
    "dejavu serif", "liberation sans", "liberation serif", "liberation mono", "ubuntu", "cantarell",
    "cambria", "baskerville old face", "bookman old style", "century schoolbook", "century", "sitka text",
    "perpetua", "goudy old style", "californian fb", "bell mt", "calisto mt", "high tower text", "gill sans mt",
    "rockwell", "libre baskerville", "baskervville", "gfs baskerville", "c059", "p052", "bitstream charter",
    "caladea", "carlito", "freeserif", "freesans", "nimbus roman", "nimbus sans", "tex gyre termes",
    "tex gyre pagella", "tex gyre bonum", "tex gyre schola")
_SANS_WORDS = ("arial", "helvetica", "calibri", "segoe", "verdana", "tahoma", "trebuchet", "gothic", "candara", "corbel",
               "franklin", "sans", "aptos", "roboto", "lato", "inter", "ubuntu", "cantarell", "carlito")
_MONO_WORDS = ("courier", "consolas", "mono", "console", "typewriter")


def _font_class(family):
    low = family.lower()
    if any(k in low for k in _MONO_WORDS):
        return "mono"
    return "sans" if any(k in low for k in _SANS_WORDS) else "serif"
_FONT_STYLES = {"regular", "book", "roman", "normal", "bold", "italic", "oblique", "bold italic",
                "bold oblique", "semibold", "medium", "semibold italic", "medium italic"}
_BASE14 = {"helv": "Helvetica", "hebo": "Helvetica Bold", "heit": "Helvetica Italic", "hebi": "Helvetica Bold Italic",
           "tiro": "Times", "tibo": "Times Bold", "tiit": "Times Italic", "tibi": "Times Bold Italic",
           "cour": "Courier", "cobo": "Courier Bold"}
_REF = 64                       # pixel size the comparison glyphs are rendered at
LETTER_MATCH = 0.78             # how closely every letter-sized stretch of a redrawn word must match the picture
OCR_CONFIDENCE = 0.40           # ... and the least the OCR engine's own confidence in a word may be


class _Face:
    """One candidate font: renders words for comparison (Pillow) and for the PDF (PyMuPDF)."""

    def __init__(self, name, path=None, code=None):
        import io
        import pymupdf as fitz
        from PIL import ImageFont
        self.name, self.path, self.code = name, path, code
        self.key = ("file", path) if path else ("code", code)
        self._fitz = None
        if path:
            self.pil = ImageFont.truetype(path, _REF)
        else:
            self._fitz = fitz.Font(code)
            self.pil = ImageFont.truetype(io.BytesIO(self._fitz.buffer), _REF)
        self.cache = {}
        # what a word processor needs to know to use the same font
        if path:
            family, style = self.pil.getname()
            style = (style or "").lower()
        else:
            family = {"he": "Arial", "ti": "Times New Roman", "co": "Courier New"}[code[:2]]
            style = name.lower()
        self.family = family or "Arial"
        self.bold = any(k in style for k in ("bold", "black", "heavy"))
        self.italic = "italic" in style or "oblique" in style
        ascent, descent = self.pil.getmetrics()
        self.ascent, self.descent = ascent / _REF, descent / _REF

    @property
    def fitz(self):
        if self._fitz is None:
            import pymupdf as fitz
            self._fitz = fitz.Font(fontfile=self.path)
        return self._fitz

    def word(self, text, keep=True):
        """(ink picture, left, top, right, bottom) with the extents in em units from the baseline.

        Drawings are remembered, since the same words recur - but only a few hundred per font, and
        not at all with keep=False (the look-alike spellings tried once and never again): unbounded,
        this cache is what fills the memory on long documents."""
        hit = self.cache.get(text)
        if hit is None:
            from PIL import ImageDraw
            hit = False
            try:
                l, t, r, b = self.pil.getbbox(text, anchor="ls")
                m = _REF // 2                                   # margin: glyphs may overhang the nominal box
                im = Image.new("L", (int(r - l) + 2 * m, int(b - t) + 2 * m), 0)
                ImageDraw.Draw(im).text((m - l, m - t), text, font=self.pil, fill=255, anchor="ls")
                a = np.asarray(im, np.float32) / 255.0
                ys, xs = np.flatnonzero((a > 0.3).any(axis=1)), np.flatnonzero((a > 0.3).any(axis=0))
                if len(ys) and len(xs):                         # tight ink box, measured like the picture is
                    x0, x1, y0, y1 = xs[0], xs[-1] + 1, ys[0], ys[-1] + 1
                    hit = (a[y0:y1, x0:x1], (x0 - m + l) / _REF, (y0 - m + t) / _REF,
                           (x1 - m + l) / _REF, (y1 - m + t) / _REF)
            except Exception:
                hit = False
            if keep:
                if len(self.cache) >= 300:
                    self.cache.clear()
                self.cache[text] = hit
        return hit or None


FONTS_FOLDER = "snapclean_fonts"        # beside the program: free fonts fetched for it (see get_free_fonts)
_FREE_FONTS = {
    # family: [(file to fetch from the Google Fonts collection, {style name: weight})]
    "Libre Baskerville": [("ofl/librebaskerville/LibreBaskerville%5Bwght%5D.ttf", {"Regular": 400, "Bold": 700}),
                          ("ofl/librebaskerville/LibreBaskerville-Italic%5Bwght%5D.ttf", {"Italic": 400, "Bold Italic": 700})],
}


def fonts_folder():
    return Path(__file__).resolve().parent / FONTS_FOLDER


def get_free_fonts(say=lambda text: None):
    """Fetch free typefaces that stand in well for ones a document is set in but this computer does not
    have (Libre Baskerville for the Baskerville family), and keep them in a folder beside the program.
    They are published under the SIL Open Font License, which allows using and embedding them.
    Each arrives as one file holding every weight; plain Regular / Bold / Italic / Bold Italic files are
    cut from it, because that is what the PDF and Word writers can use. Returns the files made."""
    import urllib.request
    try:
        from fontTools.ttLib import TTFont
        from fontTools.varLib import instancer
    except ImportError:
        say("Installing a font tool (fonttools)...")
        subprocess.run([sys.executable, "-m", "pip", "install", "fonttools"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        importlib.invalidate_caches()
        from fontTools.ttLib import TTFont
        from fontTools.varLib import instancer
    folder = fonts_folder()
    folder.mkdir(parents=True, exist_ok=True)
    made = []
    for family, sources in _FREE_FONTS.items():
        for remote, styles in sources:
            wanted = {style: folder / f"{family.replace(' ', '')}-{style.replace(' ', '')}.ttf" for style in styles}
            if all(p.exists() and p.stat().st_size > 20000 for p in wanted.values()):
                made += list(wanted.values())
                continue
            say(f"Fetching {family}...")
            raw = folder / ("_" + remote.rsplit("/", 1)[-1].replace("%5B", "[").replace("%5D", "]"))
            with urllib.request.urlopen("https://raw.githubusercontent.com/google/fonts/main/" + remote, timeout=120) as r:
                raw.write_bytes(r.read())
            for style, weight in styles.items():
                font = instancer.instantiateVariableFont(TTFont(str(raw)), {"wght": weight}, inplace=False)
                for rec in font["name"].names:          # so that every program lists it as "<family>" / "<style>"
                    if rec.nameID in (1, 16):
                        rec.string = family
                    elif rec.nameID in (2, 17):
                        rec.string = style
                    elif rec.nameID == 4:
                        rec.string = f"{family} {style}"
                    elif rec.nameID == 6:
                        rec.string = f"{family.replace(' ', '')}-{style.replace(' ', '')}"
                if "OS/2" in font:
                    font["OS/2"].usWeightClass = weight
                    sel = font["OS/2"].fsSelection & ~0x61
                    font["OS/2"].fsSelection = sel | (0x20 if weight >= 600 else 0) | (0x01 if "Italic" in style else 0) | \
                        (0x40 if style == "Regular" else 0)
                if "head" in font:
                    font["head"].macStyle = (1 if weight >= 600 else 0) | (2 if "Italic" in style else 0)
                font.save(str(wanted[style]))
                made.append(wanted[style])
            try:
                raw.unlink()
            except OSError:
                pass
    return made


def _font_candidates(limit=200):
    """Fonts to try: common document/web fonts found on this computer plus the PDF standard ones."""
    from PIL import ImageFont
    home = Path.home()
    if sys.platform.startswith("win"):
        dirs = [Path(os.environ.get("WINDIR", r"C:\Windows")) / "Fonts",
                Path(os.environ.get("LOCALAPPDATA", "")) / "Microsoft" / "Windows" / "Fonts"]
    elif sys.platform == "darwin":
        dirs = [Path("/System/Library/Fonts"), Path("/Library/Fonts"), home / "Library" / "Fonts"]
    else:
        dirs = [Path("/usr/share/fonts"), Path("/usr/local/share/fonts"), home / ".fonts", home / ".local/share/fonts"]
    dirs.insert(0, fonts_folder())                      # the program's own fetched fonts come first
    faces, seen = [], set()
    for d in dirs:
        if not d.is_dir():
            continue
        for f in sorted(d.rglob("*")):
            if f.suffix.lower() not in (".ttf", ".otf") or len(faces) >= limit:
                continue
            try:
                family, style = ImageFont.truetype(str(f), 12).getname()
            except Exception:
                continue
            fam, sty = (family or "").lower().strip(), (style or "").lower().strip()
            if sty not in _FONT_STYLES or (fam, sty) in seen:
                continue
            if not any(fam == k or fam.startswith(k + " ") for k in _FONT_FAMILIES) or "cjk" in fam:
                continue
            try:
                faces.append(_Face(f"{family} {style}", path=str(f)))
                seen.add((fam, sty))
            except Exception:
                pass
    for code, name in _BASE14.items():
        try:
            faces.append(_Face(name, code=code))
        except Exception:
            pass
    return faces


def _runs(flags):
    """[(start, end)] of the True runs in a 1-D boolean array."""
    d = np.diff(np.concatenate([[0], flags.astype(np.int8), [0]]))
    return list(zip(np.flatnonzero(d == 1), np.flatnonzero(d == -1)))


_EDGE_LEVEL = float(os.environ.get("DEWATERMARK_EDGE", "0.45"))


def _line_obs(rgb, text, box, pad=2, spans=None):
    """Measure one OCR line in the picture: where each word's ink is. None if it cannot be trusted."""
    tokens = text.split()
    h, w = rgb.shape[:2]
    x0, y0 = max(0, int(math.floor(box[0])) - pad), max(0, int(math.floor(box[1])) - pad)
    x1, y1 = min(w, int(math.ceil(box[2])) + pad), min(h, int(math.ceil(box[3])) + pad)
    if not tokens or x1 - x0 < 4 or y1 - y0 < 5:
        return None
    # OCR boxes are sometimes a little tight: grow the crop until its edges are clear of ink, so that
    # no sliver of a letter is left outside (it would survive the erasing as a stray speck)
    base = np.median(rgb[y0:y1, x0:x1].reshape(-1, 3).astype(np.float32), axis=0)
    inky = lambda block: (np.abs(block.astype(np.float32) - base).max(axis=-1) > 60).any()
    reach = max(3, (y1 - y0) // 2)
    for _ in range(reach):
        if x0 > 0 and inky(rgb[y0:y1, x0:x0 + 2]):
            x0 -= 1
        if x1 < w and inky(rgb[y0:y1, x1 - 2:x1]):
            x1 += 1
    for _ in range(3):
        if y0 > 0 and inky(rgb[y0:y0 + 1, x0:x1]):
            y0 -= 1
        if y1 < h and inky(rgb[y1 - 1:y1, x0:x1]):
            y1 += 1
    for _ in range(2):
        crop = rgb[y0:y1, x0:x1].astype(np.float32)
        rim = np.concatenate([crop[0], crop[-1], crop[:, 0], crop[:, -1]])
        bg = np.median(rim, axis=0)                    # the paper: what the edge of the crop mostly is
        diff = np.abs(crop - bg).max(axis=2)
        peak = float(np.percentile(diff, 99))
        if peak < 60:
            return None                                # too faint to measure
        D = np.clip(diff / peak, 0.0, 1.0)
        # Table rules and box edges caught in the crop are not text. Step inside them, so that
        # what lies beyond (the next cell, the page outside a shaded cell) is not measured or erased.
        dark = D > 0.3
        rr, rc = np.flatnonzero(dark.mean(axis=1) > 0.85), np.flatnonzero(dark.mean(axis=0) > 0.85)
        hh, ww = dark.shape
        top, bot = rr[rr < hh / 3], rr[rr > 2 * hh / 3]
        lef, rig = rc[rc < ww / 3], rc[rc > 2 * ww / 3]
        if not (len(top) or len(bot) or len(lef) or len(rig)):
            break
        # (one pixel further in than the rule itself, to clear its soft edge)
        y0, y1 = y0 + (top.max() + 2 if len(top) else 0), y0 + (bot.min() - 1 if len(bot) else hh)
        x0, x1 = x0 + (lef.max() + 2 if len(lef) else 0), x0 + (rig.min() - 1 if len(rig) else ww)
        if x1 - x0 < 4 or y1 - y0 < 5:
            return None
    dark = D > 0.3
    D[dark.mean(axis=1) > 0.85, :] = 0.0
    D[:, dark.mean(axis=0) > 0.85] = 0.0
    quiet = np.ones(D.shape, bool)
    quiet[1:-1, 1:-1] = False
    if np.percentile(diff[quiet & (D < 0.3)], 60) > 10:
        return None                                    # not a flat background: leave the picture alone
    u = int(np.clip(round(48.0 / (y1 - y0)), 1, 4))    # work enlarged, for sub-pixel accuracy
    Du = np.clip(cv2.resize(D, None, fx=u, fy=u, interpolation=cv2.INTER_CUBIC), 0.0, 1.0) if u > 1 else D
    ink = Du > 0.3
    rows = _runs(ink.any(axis=1))
    if not rows:
        return None
    main = max(rows, key=lambda r: ink[r[0]:r[1]].sum())
    rows = [r for r in rows if r == main or not (r[0] == 0 or r[1] == ink.shape[0])]   # drop neighbours' intrusions
    r0, r1 = min(r[0] for r in rows), max(r[1] for r in rows)
    cols = _runs(ink[r0:r1].any(axis=0))
    if len(cols) < len(tokens):
        return None
    gaps = [(cols[i + 1][0] - cols[i][1], i) for i in range(len(cols) - 1)]
    cuts = sorted(i for _, i in sorted(gaps, reverse=True)[:len(tokens) - 1])
    # Is it clear which gaps are between words? The narrowest gap used must stand out from the widest left over.
    used = [g for g, i in gaps if i in cuts]
    rest = [g for g, i in gaps if i not in cuts]
    split = "gaps" if not used or not rest or min(used) >= 1.35 * max(rest) else "unsure"
    if spans and len(spans) == len(tokens) and len(tokens) > 1:
        # the OCR engine said where each word is: cut at the gap nearest each of its word boundaries
        mine, last = [], -1
        for k in range(len(tokens) - 1):
            mid = ((spans[k][1] + spans[k + 1][0]) / 2.0 - x0) * u
            choice = min(range(last + 1, len(cols) - 1), default=None,
                         key=lambda i: abs((cols[i][1] + cols[i + 1][0]) / 2.0 - mid))
            if choice is None or abs((cols[choice][1] + cols[choice + 1][0]) / 2.0 - mid) > 1.2 * (r1 - r0):
                mine = None
                break
            mine.append(choice)
            last = choice
        if mine is not None:
            cuts, split = mine, "boxes"
    words, start = [], 0
    for c in cuts + [len(cols) - 1]:
        c0, c1 = cols[start][0], cols[c][1]
        rr = _runs(ink[r0:r1, c0:c1].any(axis=1))
        top, bottom = r0 + rr[0][0], r0 + rr[-1][1]
        # How tall the word is decides the size it is set in, so its top and bottom are taken where the
        # ink is half dark - the true edge of a letter. Taken at the faint outer fringe (which is where
        # the word is *found*), a soft picture measures every word a few percent too tall, and the
        # re-typeset word then stands bigger and blacker than the original ones beside it.
        firm = _runs((Du[r0:r1, c0:c1] > _EDGE_LEVEL).any(axis=1))
        if firm and firm[-1][1] - firm[0][0] >= 0.7 * (bottom - top):
            top, bottom = r0 + firm[0][0], r0 + firm[-1][1]
        words.append((c0, c1, top, bottom))                            # upsampled px: x0, x1, top, bottom
        start = c + 1
    return {"tokens": tokens, "words": words, "u": u, "Du": Du, "D": D, "crop": crop, "bg": bg, "org": (x0, y0),
            "split": split}


def _pearson(a, b):
    if a.shape != b.shape or a.size == 0:
        return -1.0
    a = a - a.mean()
    b = b - b.mean()
    d = math.sqrt(float((a * a).sum()) * float((b * b).sum()))
    return float((a * b).sum()) / d if d > 1e-6 else 0.0


def _fit_line(face, L, size=None, local=False, base=None):
    """Lay the line's words out in `face` over the picture. Returns size, baseline, per-word fit, score.

    Per word: (match 0-1, sideways stretch needed, left bearing, worst letter-sized match, ink ratio).
    The letter-sized match is only worked out with local=True (it is the slow part)."""
    u, Du = L["u"], L["Du"]
    glyphs = [face.word(t) for t in L["tokens"]]
    if any(g is None for g in glyphs):
        return None
    tops = np.array([g[2] for g in glyphs])
    bots = np.array([g[4] for g in glyphs])
    T = np.array([w[2] for w in L["words"]], np.float64) / u
    B = np.array([w[3] for w in L["words"]], np.float64) / u
    if size is None:
        A = np.concatenate([np.stack([np.ones_like(tops), tops], 1), np.stack([np.ones_like(bots), bots], 1)])
        y = np.concatenate([T, B])
        keep = np.ones(len(y), bool)
        for _ in range(2):
            (yb, s), *_ = np.linalg.lstsq(A[keep], y[keep], rcond=None)
            res = np.abs(A @ np.array([yb, s]) - y)
            keep = res <= max(1.0, 0.12 * s)
            if keep.sum() < 2:
                break
    else:
        s = size
        yb = float(np.median(np.concatenate([T - s * tops, B - s * bots]))) if base is None else float(base)
    if not np.isfinite(s) or s < 4:
        return None
    P = np.zeros_like(Du)
    boxes = []
    for (c0, c1, r0, r1), (pic, l, t, r, b) in zip(L["words"], glyphs):
        wpx, hpx = max(1, c1 - c0), max(1, int(round(s * (b - t) * u)))
        top = int(round((yb + s * t) * u))
        patch = cv2.resize(pic, (wpx, hpx), interpolation=cv2.INTER_AREA)
        ya, yz = max(0, top), min(P.shape[0], top + hpx)
        if yz > ya:
            P[ya:yz, c0:c1] = patch[ya - top:yz - top, :c1 - c0]
        boxes.append((max(0, min(top, r0) - u), min(P.shape[0], max(top + hpx, r1) + u),
                      max(0, c0 - u), min(P.shape[1], c1 + u)))
    if u > 1:                # put the drawing through what the picture went through: screen pixels, then enlarged
        small = cv2.resize(P, (L["D"].shape[1], L["D"].shape[0]), interpolation=cv2.INTER_AREA)
        P = np.clip(cv2.resize(small, (P.shape[1], P.shape[0]), interpolation=cv2.INTER_CUBIC), 0.0, 1.0)
    inked = P[P > 0.02]                 # scale by the ink itself, so one word and a whole line come out alike
    P = np.clip(P / max(float(np.percentile(inked, 93)) if inked.size else 1.0, 0.2), 0.0, 1.0)
    out = []
    for (c0, c1, r0, r1), (pic, l, t, r, b), (ra, rz, ca, cz) in zip(L["words"], glyphs, boxes):
        p, d = P[ra:rz, ca:cz], Du[ra:rz, ca:cz]
        out.append([_pearson(p, d), (c1 - c0) / u / max(s * (r - l), 1e-3), l, 0.0,
                    float(p.sum()) / max(float(d.sum()), 1e-3)])
    if local:
        # the whole-word match barely notices one wrong letter, so also find each word's worst
        # letter-sized stretch: a misread letter shows up there
        k = max(3, int(0.05 * s * u) * 2 + 1)
        Pb, Db = cv2.GaussianBlur(P, (k, k), 0), cv2.GaussianBlur(Du, (k, k), 0)
        win = max(4, int(round(0.55 * s * u)))
        slip = max(1, int(round(0.07 * s * u)))
        for o, (ra, rz, ca, cz) in zip(out, boxes):
            worst = 1.0
            starts = list(range(ca, max(ca + 1, cz - win + 1), max(1, win // 3)))
            if starts[-1] != max(ca, cz - win):
                starts.append(max(ca, cz - win))
            for c in starts:             # letters drift a little along a word: allow a small sideways slip
                z = min(c + win, Db.shape[1])          # a word at the right edge can be narrower than the window
                d = Db[ra:rz, c:z]
                best = -1.0
                for dx in range(-slip, slip + 1):
                    if 0 <= c + dx and z + dx <= Pb.shape[1]:
                        best = max(best, _pearson(Pb[ra:rz, c + dx:z + dx], d))
                worst = min(worst, best)
            o[3] = worst
    lens = np.array([len(t) for t in L["tokens"]], np.float64)
    mean = lambda j: float((np.array([o[j] for o in out]) * lens).sum() / lens.sum())
    stretch = float(np.median([o[1] for o in out]))
    mass = float(np.median([o[4] for o in out]))
    score = mean(0) - 1.0 * abs(math.log(max(stretch, 1e-3))) - 0.5 * abs(math.log(max(mass, 1e-3)))
    if local:
        score += 0.5 * mean(3)
    return {"face": face, "size": float(s), "base": float(yb), "words": [tuple(o) for o in out], "score": score}


def _word_quality(w):
    return w[0] - 1.0 * abs(math.log(max(w[1], 1e-3))) - 0.5 * abs(math.log(max(w[4], 1e-3)))


def _style_words(setter, L, fit):
    """Give each word of a line its own font where it differs from the line's: a bold or italic word,
    or a word in another typeface (a code in a fixed-width font, say).

    A word that the line's font already fits well is left alone. Otherwise the other styles of the same
    family (at the line's size and baseline) and the document's other fonts are tried, and the word
    switches only if another one fits clearly better. Adds "faces", "sizes" and "bases" to the fit."""
    face0, s0, n = fit["face"], fit["size"], len(L["tokens"])
    faces, sizes, bases, words = [face0] * n, [s0] * n, [fit["base"]] * n, list(fit["words"])
    unsure = [False] * n
    siblings = [f for f in setter.all if f.family == face0.family and f is not face0]
    others = [f for f in (setter.short or []) if f.family != face0.family]
    for i, (tok, w) in enumerate(zip(L["tokens"], words)):
        if sum(ch.isalnum() for ch in tok) < 2:
            continue
        if w[3] >= 0.9 and 0.9 <= w[4] <= 1.12 and 0.95 <= w[1] <= 1.05:
            continue                                # fits as it is
        one = dict(L, tokens=[tok], words=[L["words"][i]])
        short = sum(ch.isalnum() for ch in tok) <= 3
        own = _fit_line(face0, one, size=s0, base=fit["base"])      # the line's font, measured the same way
        mine = _word_quality(own["words"][0]) if own else _word_quality(w)
        best, best_q = None, mine + 0.04

        def consider(candidates):
            nonlocal best, best_q
            for f in candidates:
                trial = _fit_line(f, one, size=s0, base=fit["base"]) if f.family == face0.family else _fit_line(f, one)
                if trial and _word_quality(trial["words"][0]) > best_q:
                    best, best_q = trial, _word_quality(trial["words"][0])

        consider(siblings + others + setter.strays)
        if best_q < 0.80 and len(tok) >= 3:
            # still a poor fit: a typeface this document has not shown before (a code in a fixed-width
            # font inside a sentence). Look through every font, and remember what turns up.
            tried = {id(f) for f in siblings + others + setter.strays} | {id(face0)}
            consider([f for f in setter.all if id(f) not in tried])
            if best is not None and best["face"] not in setter.strays and best["face"].family != face0.family:
                setter.strays.append(best["face"])
        if best is not None and short and best_q < mine + 0.12:
            # Two or three letters at this size cannot show whether they are bold or italic: with no
            # clear winner the word is left as its picture instead of being drawn in a guessed style.
            unsure[i] = True
        elif best is not None:
            full = _fit_line(best["face"], one, size=best["size"], local=True, base=best["base"])
            if full and full["words"][0][3] >= w[3] - 0.01:
                faces[i], sizes[i], bases[i], words[i] = full["face"], full["size"], full["base"], full["words"][0]
    return dict(fit, words=words, faces=faces, sizes=sizes, bases=bases, unsure=unsure)


def _stem_width(mask):
    """Thickness of a word's main strokes in pixels (what makes bold bold), or 0 if there is too little ink."""
    if mask.sum() < 12:
        return 0.0
    dt = cv2.distanceTransform(np.pad(mask, 1).astype(np.uint8), cv2.DIST_L2, 3)
    return 2.0 * float(np.percentile(dt[dt > 0], 88))


def _stem(ink):
    """How thick a word's strokes are, in pixels of its picture: twice the usual distance from the middle
    of a stroke to its edge. Read off the picture itself, so it does not depend on which font the word
    is compared with. 0 if it cannot be told."""
    solid = (np.asarray(ink) > 0.45).astype(np.uint8)
    if solid.sum() < 30:
        return 0.0
    far = cv2.distanceTransform(np.pad(solid, 1), cv2.DIST_L2, 3)[1:-1, 1:-1]
    # the spine of each stroke: points no neighbour is further inside than
    spine = (far >= cv2.dilate(far, np.ones((3, 3), np.uint8)) - 1e-6) & (solid > 0)
    vals = far[spine]
    if vals.size < 8:
        return 0.0
    return 2.0 * float(np.percentile(vals, 70))         # the thick strokes (stems), not hairlines and serifs


def _slant(ink):
    """How far a word's upright strokes lean to the right, in degrees (about 0 for upright type, 8-20 for italic).

    The word is leaned back by one angle after another; at the right one its strokes stand up straight and
    stack into the tallest, narrowest columns."""
    h, w = ink.shape
    if h < 8 or w < 8:
        return 0.0
    src = np.clip(ink.astype(np.float32), 0.0, 1.0)
    if h < 40:                                      # small type: enlarge, so that a lean of a pixel or two shows
        f = int(math.ceil(40.0 / h))
        src = cv2.resize(src, None, fx=f, fy=f, interpolation=cv2.INTER_CUBIC)
        h, w = src.shape
    scores = {}
    for a in range(-4, 25, 2):
        k = math.tan(math.radians(a))
        M = np.float32([[1, k, -k * h / 2.0 + abs(k) * h], [0, 1, 0]])
        col = cv2.warpAffine(src, M, (w + int(2 * abs(k) * h) + 1, h), flags=cv2.INTER_LINEAR).sum(axis=0)
        scores[a] = float((col * col).sum())
    best = max(scores, key=scores.get)
    return float(best) if scores[best] > 1.03 * scores[0] else 0.0


def _quote_doubt(L, fit, i):
    """True when a word is read with a quotation mark at its edge but the picture has no small raised
    mark there (a registered-trademark sign read as a quote, a speck read as an opening quote)."""
    head, core, tail = _core(L["tokens"][i])
    quotes = "\"'‘’“”`"
    front, back = any(ch in quotes for ch in head), any(ch in quotes for ch in tail) and core[-1:] != "s"
    if not (front or back) or not core:
        return False
    em, floor = fit["sizes"][i] * L["u"], fit["bases"][i] * L["u"]
    c0, c1, r0, r1 = L["words"][i]
    ink = L["Du"][r0:r1, c0:c1] > 0.3
    runs = _runs(ink.any(axis=0))
    if len(runs) < 2:
        return True

    def is_quote(run):
        rows = _runs(ink[:, run[0]:run[1]].any(axis=1))
        return run[1] - run[0] <= 0.26 * em and r0 + rows[-1][1] <= floor - 0.25 * em

    def raised(a, b):                                   # a strip of the word with ink only well above the line
        rows = _runs(ink[:, max(0, a):b].any(axis=1))
        return bool(rows) and r0 + rows[-1][1] <= floor - 0.25 * em

    strip = max(2, int(0.12 * em))
    if front and raised(0, strip):                      # a quote touching its letter is still a quote
        front = False
    if back and raised(ink.shape[1] - strip, ink.shape[1]):
        back = False
    if not (front or back):
        return False

    # closing punctuation after the quote (”, or ”.) sits last: look at the last two runs
    return (front and not is_quote(runs[0])) or (back and not any(is_quote(r) for r in runs[-2:]))


def _foot_mark(L, fit, i):
    """(height, depth below the line) of the comma or full stop that ends word i, in ems - or None."""
    tok = L["tokens"][i]
    em, floor = fit["size"] * L["u"], fit["base"] * L["u"]
    if len(tok) < 2 or tok[-1] not in ".," or not (tok[-2].isalnum() or tok[-2] in ")]") or em < 24:
        return None
    c0, c1, r0, r1 = L["words"][i]
    ink = L["Du"][r0:r1, c0:c1] > 0.3
    runs = _runs(ink.any(axis=0))
    if len(runs) < 2:
        return None
    rr = _runs(ink[:, runs[-1][0]:runs[-1][1]].any(axis=1))
    top, bottom = r0 + rr[0][0], r0 + rr[-1][1]
    if bottom - top > 0.3 * em or top < floor - 0.22 * em or runs[-1][1] - runs[-1][0] > 0.2 * em:
        return None                                     # not a lone dot or comma at the foot of the line
    return (bottom - top) / em, (bottom - floor) / em


def _case_doubt(L, fit, i):
    """True when a word's first letter is one whose capital and small forms look alike (W w, C c, S s...)
    and its height in the picture says the other one."""
    tok = L["tokens"][i]
    head, core, tail = _core(tok)
    if not core or core[0].lower() not in "cosvwxz" or not core[0].isalpha():
        return False
    face, em, floor = fit["faces"][i], fit["sizes"][i] * L["u"], fit["bases"][i] * L["u"]
    big, small = face.word("H"), face.word("x")
    if not big or not small:
        return False
    c0, c1, r0, r1 = L["words"][i]
    ink = L["Du"][r0:r1, c0:c1] > 0.3
    runs = _runs(ink.any(axis=0))
    # skip opening quotes and brackets: the first run of ink wide enough to be a letter
    first = next((r for r in runs[len(head):] or runs if r[1] - r[0] >= 0.15 * em), None)
    if first is None:
        return False
    # only the first letter's own width: joined to the next letter ("of"), the run would reach up to the f
    glyph = face.word(core[0])
    letter = (glyph[3] - glyph[1]) * em * fit["words"][i][1] if glyph else 0.4 * em
    first = (first[0], min(first[1], first[0] + max(3, int(0.75 * letter))))
    rows = _runs(ink[:, first[0]:first[1]].any(axis=1))
    if not rows:
        return False
    height = (floor - (r0 + rows[0][0])) / em
    middle = (-big[2] - small[2]) / 2.0
    return height < middle - 0.03 if core[0].isupper() else height > middle + 0.03


class Retypesetter:
    """Finds, per line, the installed font that best matches the picture and decides word by word
    whether the redrawn text is close enough to replace the picture."""

    def __init__(self):
        self.all = _font_candidates()
        self.short = None            # the few fonts this document actually uses
        self.tally = {}
        self.seen = 0
        self.wasted = 0
        self.strays = []             # fonts found for odd words inside lines
        # "matched": the document's own fonts are on this computer and are matched letter for letter.
        # "substitute": they are not (a book typeface, say). Then one installed family stands in for the
        # whole document, and bold / italic are measured from the picture instead of guessed from the fit.
        self.mode = None
        self.subs = {}               # class (serif / sans / mono) -> {(bold, italic): font}
        self.body = None
        self.stems = []              # stroke thickness / size of the words seen so far
        self.readings = 0

    def state(self):
        """What the helper processes need to carry on in the same fonts."""
        return {"mode": self.mode, "body": self.body, "force": STRICTNESS.get("fonts", "auto"),
                "subs": {c: {k: f.name for k, f in v.items()} for c, v in self.subs.items()},
                "short": [f.name for f in self.short] if self.short else None, "stems": self.stems[-600:]}

    def adopt(self, state):
        by_name = {f.name: f for f in self.all}
        STRICTNESS["fonts"] = state.get("force", "auto")
        if state.get("short"):
            self.short = [by_name[n] for n in state["short"] if n in by_name]
        if state.get("mode"):
            self.mode, self.body = state["mode"], state.get("body")
            self.subs = {c: {tuple(k): by_name[n] for k, n in v.items() if n in by_name} for c, v in state["subs"].items()}
            self.stems = list(state.get("stems") or [])

    def _decide(self, lines):
        """Look at a page's longer lines: are the document's fonts installed here, or must one stand in?"""
        sample = sorted((L for L in lines if L and len(L["tokens"]) >= 4 and sum(map(len, L["tokens"])) >= 20),
                        key=lambda L: -sum(map(len, L["tokens"])))[:12]
        if len(sample) < 5:
            return
        good, total, tops, firsts = 0, {}, {}, []
        inks = {}                                       # family -> how much ink its regular style has against the page's, line by line
        for L in sample:
            quick = [fit for fit in (_fit_line(f, L) for f in self.all) if fit]
            quick.sort(key=lambda fit: fit["score"], reverse=True)
            fam = {}
            for fit in quick:
                fam[fit["face"].family] = max(fam.get(fit["face"].family, -9.0), fit["score"])
                if not fit["face"].bold and not fit["face"].italic:
                    inks.setdefault(fit["face"].family, []).append(float(np.median([w[4] for w in fit["words"]])))
            for name, score in fam.items():
                total[name] = total.get(name, 0.0) + score
            for fit in quick[:2]:
                full = _fit_line(fit["face"], L, local=True)
                if full and fit is quick[0]:
                    firsts.append((float(np.median([w[3] for w in full["words"]])),
                                   float(np.median([w[1] for w in full["words"]]))))
                if full and os.environ.get("SNAPCLEAN_DEBUG") and fit is quick[0]:
                    ws = sorted(w[3] for w in full["words"])
                    print("      sample:", full["face"].name, "mean", round(float(np.mean(ws)), 2), "median", round(float(np.median(ws)), 2),
                          "top-quarter", round(float(np.mean(ws[-max(1, len(ws) // 4):])), 2), "stretch", round(float(np.median([w[1] for w in full["words"]])), 2))
                if full and self._plausible(full) and float(np.mean([w[3] for w in full["words"]])) >= 0.88:
                    good += 1
                    tops[full["face"].family] = tops.get(full["face"].family, 0) + 1
                    break
        if os.environ.get("SNAPCLEAN_DEBUG"):
            print(f"    fonts: {sum(1 for m, t in firsts if m >= 0.86 and 0.9 <= t <= 1.1)} of {len(sample)} sample lines match an installed font letter for letter")
        # the document's own font, when it is here, wins line after line; look-alikes take turns
        # A font that really is the document's fits letter for letter, line after line; a look-alike does not.
        close = sum(1 for match, stretch in firsts if match >= 0.86 and 0.9 <= stretch <= 1.1)
        force = os.environ.get("DEWATERMARK_FONTS") or STRICTNESS.get("fonts", "auto")
        if force == "match" or (force != "one" and close >= 0.5 * len(sample)):
            self.mode = "matched"
            return
        styles = {}
        for f in self.all:
            styles.setdefault(f.family, {}).setdefault((f.bold, f.italic), f)
        whole = {name: v for name, v in styles.items() if (False, False) in v and (True, False) in v and (False, True) in v}
        ranked = sorted((name for name in total if name in whole), key=lambda name: -total[name])
        if not ranked:
            self.mode = "matched"
            return
        for name in ranked:
            self.subs.setdefault(_font_class(name), whole[name])
        self.body = _font_class(ranked[0])
        self.mode = "substitute"
        if os.environ.get("SNAPCLEAN_DEBUG"):
            print("    fonts: standing in -", {c: v[(False, False)].family for c, v in self.subs.items()}, "body:", self.body)

    def _plan_substitute(self, lines):
        """One family for the whole document; each word's weight and slant measured from its picture."""
        plans = [None] * len(lines)
        rows = {}
        # What is this page set in? Usually the document's main kind of type - but a form or a table page
        # may be all sans-serif in a serif document, and its lines are too short to say so one by one.
        # So the page is asked as a whole: every line of some length is fitted in each kind, and the page
        # takes another kind only if most lines fit it better, and better by a real margin.
        tried = {}
        for i, L in enumerate(lines):
            if L and sum(ch.isalnum() for tok in L["tokens"] for ch in tok) >= 6:
                tried[i] = {c: _fit_line(faces[(False, False)], L) for c, faces in self.subs.items()}
        page = self.body
        judged = [t for t in tried.values() if t.get(self.body)]
        if len(judged) >= 6:
            for other in self.subs:
                if other == self.body:
                    continue
                gains = [t[other]["score"] - t[self.body]["score"] for t in judged if t.get(other)]
                if len(gains) >= 0.8 * len(judged) and float(np.median(gains)) >= 0.05 and \
                        sum(g > 0.01 for g in gains) >= 0.7 * len(gains):
                    page = other
                    if os.environ.get("SNAPCLEAN_DEBUG"):
                        print(f"    fonts: this page is {other} (median gain {np.median(gains):.3f} over {len(gains)} lines)")
        for i, L in enumerate(lines):
            if not L:
                continue
            fits = tried.get(i) or {}
            cls, fit = page, fits.get(page) if page in fits else _fit_line(self.subs[page][(False, False)], L)
            for other, faces in self.subs.items():
                # another kind of type (sans, typewriter) only where it is plainly that: a short line
                # or a near tie stays in the page's main font, so the page does not look patched
                if other != page and sum(map(len, L["tokens"])) >= 12:
                    trial = fits.get(other) if other in fits else _fit_line(faces[(False, False)], L)
                    # (on a page that voted itself into another kind of type, a line needs more to leave it)
                    if trial and (fit is None or trial["score"] > fit["score"] + (0.25 if page == self.body else 0.4)):
                        cls, fit = other, trial
            if fit is None:
                continue
            slants = []
            for tok, (c0, c1, r0, r1) in zip(L["tokens"], L["words"]):
                enough = sum(ch.isalnum() for ch in tok) >= 3 and sum(ch.isalpha() for ch in tok) >= 3
                slants.append(_slant(L["Du"][r0:r1, c0:c1]) if enough else None)
            rows[i] = [cls, fit, None, slants]
        # A line set in another kind of type than the page (a line of sans-serif on a serif page) is
        # believed only if a line next to it says the same: one such line alone, among lines of the
        # page's own type, is a misjudgement, and it shows.
        def place(L):
            x0, y0 = L["org"]
            return x0, y0, x0 + L["crop"].shape[1], y0 + L["crop"].shape[0]

        def beside(i):
            x0, y0, x1, y1 = place(lines[i])
            tall = max(1.0, y1 - y0)
            near = []
            for j in rows:
                if j == i:
                    continue
                a0, b0, a1, b1 = place(lines[j])
                if min(x1, a1) - max(x0, a0) > 0 and (-0.3 * tall <= b0 - y1 <= 1.6 * tall or -0.3 * tall <= y0 - b1 <= 1.6 * tall):
                    near.append(j)
            return near

        for i in list(rows):
            if rows[i][0] != page:
                near = beside(i)
                if near and not any(rows[j][0] == rows[i][0] for j in near):
                    back = (tried.get(i) or {}).get(page) or _fit_line(self.subs[page][(False, False)], lines[i])
                    if back is not None:
                        rows[i][0], rows[i][1] = page, back
        # lines of about the same size share one size
        order = sorted(rows, key=lambda i: rows[i][1]["size"])
        cur = []
        for i in order + [None]:
            if i is None or (cur and rows[i][1]["size"] > rows[cur[0]][1]["size"] * 1.07):
                size = float(np.median([rows[j][1]["size"] for j in cur])) if cur else 0.0
                for j in cur:
                    fit = rows[j][1]
                    if abs(fit["size"] / size - 1) < 0.06:
                        rows[j][1] = _fit_line(fit["face"], lines[j], size=size) or fit
                cur = []
            if i is not None:
                cur.append(i)
        # Weight: how much ink a word has, against the same word drawn in the regular style. Fonts differ,
        # so what counts is how a word compares with the rest of the document, most of which is regular.
        by_stroke = os.environ.get("DEWATERMARK_BOLD", "ink") == "stroke"      # (tried: too coarse on small type)
        for i, row in rows.items():
            if by_stroke:
                # ... or, better, how thick its strokes are for its size - read off the picture alone
                L, size_px = lines[i], max(row[1]["size"] * lines[i]["u"], 1.0)
                row[2] = []
                for tok, (c0, c1, r0, r1) in zip(L["tokens"], L["words"]):
                    stem = _stem(L["Du"][r0:r1, c0:c1]) if sum(ch.isalnum() for ch in tok) >= 3 else 0.0
                    row[2].append(math.log(stem / size_px) if stem > 0 else None)
                continue
            row[2] = [math.log(1.0 / max(w[4], 1e-3)) if sum(ch.isalnum() for ch in tok) >= 3 else None
                      for tok, w in zip(lines[i]["tokens"], row[1]["words"])]
        self.stems = (self.stems + [v for row in rows.values() for v in row[2] if v is not None])[-6000:]
        if len(self.stems) >= 8:
            normal = float(np.median(self.stems))
            spread = 1.4826 * float(np.median(np.abs(np.array(self.stems) - normal)))
        else:
            normal, spread = 0.0, 9.0
        heavy = max(math.log(1.19), 3.3 * spread)       # a regular word is this much darker than usual almost never
        # Better, when the document shows it: bold words form a second heap of their own, well above the
        # regular ones, with next to nothing between. Where that empty stretch can be seen, its middle is
        # the dividing line - it does not move with how noisy the regular words are.
        valley = False
        if len(self.stems) >= 60:
            rel = np.array(self.stems) - normal
            edges = np.arange(0.05, 0.47, 0.02)
            counts, _ = np.histogram(rel, bins=edges)
            best = None
            for a in range(len(counts) - 3):
                for b in range(a + 2, len(counts)):         # an empty stretch from bin a to bin b-1, a heap after it
                    empty, beyond = int(counts[a:b].sum()), int((rel >= edges[b]).sum())
                    if empty <= max(1, 0.06 * beyond) and beyond >= max(4, 0.012 * rel.size) and edges[b] - edges[a] >= 0.06:
                        if best is None or (b - a) > (best[1] - best[0]):
                            best = (a, b)
            if best:
                heavy, valley = float((edges[best[0]] + edges[best[1]]) / 2), True
        if os.environ.get("SNAPCLEAN_DEBUG_BOLD"):
            vals = sorted(v - normal for row in rows.values() for v in row[2] if v is not None)
            print("    bold: normal %.3f spread %.3f heavy %.3f | this page's words, relative: " % (normal, spread, heavy) +
                  " ".join("%.2f" % vals[int(q * (len(vals) - 1))] for q in (0.05, 0.25, 0.5, 0.75, 0.8, 0.85, 0.9, 0.95, 0.99)) if vals else "")
        for i, (cls, anchor, inks, slants) in rows.items():
            L, n = lines[i], len(lines[i]["tokens"])
            bold = [None if v is None else v - normal >= heavy for v in inks]
            ital = [None if a is None else a >= 6.0 for a in slants]

            for j in range(n):                          # one darker word among regular ones must be clearly darker
                if bold[j] and inks[j] - normal < heavy + 0.05 and not valley:
                    beside = [bold[k] for k in (j - 1, j + 1) if 0 <= k < n and bold[k] is not None]
                    if beside and not any(beside):
                        bold[j] = False

            def settle(flags, weights):
                known = [(j, f) for j, f in enumerate(flags) if f is not None]
                if not known:
                    return [False] * n
                share = sum(weights[j] for j, f in known if f) / max(sum(weights[j] for j, f in known), 1)
                if share >= 0.85:                       # nearly the whole line: the whole line
                    return [True] * n
                out = []
                for j, f in enumerate(flags):
                    if f is None:                       # too short to measure: as its neighbours, if they agree
                        left = next((g for k, g in reversed(known) if k < j), None)
                        right = next((g for k, g in known if k > j), None)
                        f = bool((left if left is not None else right) and (right if right is not None else left))
                    out.append(bool(f))
                return out

            weights = [len(t) for t in L["tokens"]]
            bold, ital = settle(bold, weights), settle(ital, weights)
            family = self.subs[cls]
            faces, words = [], []
            for j, tok in enumerate(L["tokens"]):
                face = family.get((bold[j], ital[j])) or family.get((bold[j], False)) or family[(False, False)]
                one = _fit_line(face, dict(L, tokens=[tok], words=[L["words"][j]]), size=anchor["size"], base=anchor["base"])
                if one is None:
                    face, one = family[(False, False)], {"words": [anchor["words"][j]]}
                faces.append(face)
                words.append(one["words"][0])
            main = max(set(faces), key=lambda f: sum(len(t) for t, g in zip(L["tokens"], faces) if g is f))
            plans[i] = (L, {"face": main, "size": anchor["size"], "base": anchor["base"], "words": words, "faces": faces,
                            "sizes": [anchor["size"]] * n, "bases": [anchor["base"]] * n, "unsure": [False] * n,
                            "score": anchor["score"], "sub": True})
        return plans

    @staticmethod
    def _plausible(fit):
        stretch = float(np.median([w[1] for w in fit["words"]]))
        mass = float(np.median([w[4] for w in fit["words"]]))
        return 0.93 <= stretch <= 1.07 and 0.8 <= mass <= 1.25 and fit["score"] >= 0.6

    def _choose(self, lines):
        """Per line: {font name: fit} for the best few fonts, the letter-level check included."""
        fits = []
        for L in lines:
            def best3(faces):
                quick = sorted((fit for fit in (_fit_line(f, L) for f in faces) if fit),
                               key=lambda fit: fit["score"], reverse=True)
                per = {}
                for fit in quick[:3]:
                    full = _fit_line(fit["face"], L, local=True)
                    if full:
                        per[full["face"].name] = full
                return per

            def good(per):
                if not per:
                    return False
                top = max(per.values(), key=lambda fit: fit["score"])
                return self._plausible(top) and float(np.mean([w[3] for w in top["words"]])) >= 0.88

            per = best3(self.short or self.all)
            if self.short is not None and not good(per) and self.wasted < 8:
                # none of the document's usual fonts fits well (a heading, a caption...): try them all
                wider = best3(self.all)
                if wider and (not per or max(f["score"] for f in wider.values()) > max(f["score"] for f in per.values()) + 0.01):
                    per, self.wasted = wider, 0
                else:
                    self.wasted += 1          # stop looking once it keeps finding nothing better
            if self.short is None and good(per):
                top = max(per.values(), key=lambda fit: fit["score"])
                self.tally[top["face"].name] = self.tally.get(top["face"].name, 0) + len(L["tokens"])
                self.seen += 1
            fits.append(per)
        if self.short is None and self.seen >= 25:
            best = sorted(self.tally, key=self.tally.get, reverse=True)[:12]
            self.short = [f for f in self.all if f.name in best]
        return fits

    def plan(self, rgb, ocr):
        """ocr: [(text, x0, y0, x1, y1, ...)]. Returns per-line (measurements, fit), None for lines to leave alone."""
        lines = [_line_obs(rgb, item[0], item[1:5], spans=word_spans(item)) for item in ocr]
        if self.mode is None:
            self._decide(lines)
        if self.mode == "substitute":
            return self._plan_substitute(lines)
        idx = [i for i, L in enumerate(lines) if L]
        fits = dict(zip(idx, self._choose([lines[i] for i in idx])))
        best = {i: max(per.values(), key=lambda f: f["score"]) for i, per in fits.items() if per}
        # lines of about the same size share one size and - when it is a toss-up - one font
        order = sorted(best, key=lambda i: best[i]["size"])
        groups, cur = [], []
        for i in order:
            if cur and best[i]["size"] > best[cur[0]]["size"] * 1.08:
                groups.append(cur)
                cur = []
            cur.append(i)
        if cur:
            groups.append(cur)
        plans = [None] * len(ocr)
        for g in groups:
            votes = {}
            for i in g:
                votes[best[i]["face"].name] = votes.get(best[i]["face"].name, 0) + len(lines[i]["tokens"])
            common = max(votes, key=votes.get)
            same_font = [i for i in g if best[i]["face"].name == common]
            size = float(np.median([best[i]["size"] for i in same_font]))
            for i in g:
                fit = best[i]
                if common in fits[i] and fit["score"] - fits[i][common]["score"] < 0.015:
                    fit = fits[i][common]
                if fit["face"].name == common and abs(fit["size"] / size - 1) < 0.06:
                    same = _fit_line(fit["face"], lines[i], size=size, local=True)
                    if same and same["score"] >= fit["score"] - 0.05:
                        fit = same
                plans[i] = (lines[i], fit)
        return plans


# ---- dictionary: knowing which readings are real words ------------------------------------------

_TECH_WORDS = """
loadability misoperation misoperations recloser reclosers reclosing reclose autoreclose overreach overreaches
overreaching underreach underreaches underreaching overcurrent undervoltage overvoltage underfrequency overfrequency
overexcitation undercurrent switchgear switchyard busbar busbars subtransmission interconnection interconnections
synchrophasor synchrophasors phasor phasors setpoint setpoints teleprotection intertrip intertripping
directional nondirectional pilot weak infeed outfeed backfeed islanding ferroresonance subharmonic
inrush energization energize energized deenergized deenergize microprocessor electromechanical
autotransformer autotransformers transformer transformers reactor reactors capacitor capacitors arrester arresters
breaker breakers relay relays relaying pickup dropout timer timers trip trips tripped tripping reach reaches
impedance impedances reactance admittance susceptance conductance megawatt megawatts megavar megavars kilovolt
ampere amperes ampacity ohm ohms siemens secondary primary tertiary burden saturation unsaturated polarizing
polarization memory mho quadrilateral lenticular blinder blinders coordination miscoordination selectivity
dependability commissioning recommissioning setting settings firmware oscillography oscillographic sequence
zero negative positive symmetrical unsymmetrical unbalance unbalanced grounding ungrounded grounded neutral
feeder feeders sectionalizer sectionalizers fuse fuses tap taps tapped radial looped mesh contingency
generator generators governor exciter stator rotor turbine inverter inverters photovoltaic curtailment
substation substations transmission distribution subtransmission telemetry supervisory
""".split()
_DICT = {"words": None, "extra": [], "freq": None, "exact": set()}
WORDS_FILE = "snapclean_words.txt"
_TWO_LETTER = set("of to in is it on at by an as be or we he if no so up do my me us am go".split())
_CONFUSED_PAIRS = (("rn", "m"), ("m", "rn"), ("cl", "d"), ("d", "cl"), ("vv", "w"), ("w", "vv"), ("li", "h"),
                   ("h", "li"), ("ri", "n"), ("nn", "m"), ("ii", "n"), ("lt", "h"), ("u", "ti"), ("u", "tr"),
                   ("n", "ti"), ("un", "tm"), ("tl", "tt"), ("d", "tl"), ("k", "tt"), ("d", "ti"), ("w", "tr"),
                   ("w", "tio"), ("dh", "th"), ("g", "ti"), ("a", "ti"), ("ll", "ti"), ("li", "ti"), ("u", "tt"),
                   ("t", "ti"), ("t", "tt"), ("l", "ti"), ("ct", "d"), ("in", "m"), ("m", "in"), ("ni", "m"),
                   ("tw", "tio"), ("n", "ri"), ("uw", "tw"), ("c", "e"))


def dictionary():
    """The set of known words (lower case), or an empty set if no word list is available.

    English comes from the pyspellchecker package when it is installed. Added to it: a list of power
    engineering terms, and any words in snapclean_words.txt / dewatermark_words.txt (one per line) next
    to this program or in the home folder - the place for names and jargon of your own."""
    if _DICT["words"] is None:
        words = set()
        try:
            from spellchecker import SpellChecker
            _DICT["freq"] = SpellChecker().word_frequency
            words.update(_DICT["freq"].dictionary)
        except Exception:
            pass
        if words:
            words.update(_TECH_WORDS)
        for folder in (Path(__file__).resolve().parent, Path.home()):
            for name in ("snapclean_words.txt", "dewatermark_words.txt"):
                try:
                    listed = [w.strip() for w in (folder / name).read_text(encoding="utf-8").split() if w.strip()]
                    mine = [w.lower() for w in listed]
                    words.update(mine)
                    _DICT["extra"] += mine
                    _DICT["exact"].update(listed)       # as written: NEC, kV, 70E count exactly so
                except Exception:
                    pass
        _DICT["words"] = words
    return _DICT["words"]


def user_words_file():
    """Where the user's own dictionary words are kept: snapclean_words.txt beside the program."""
    return Path(__file__).resolve().parent / WORDS_FILE


def add_user_words(new_words):
    """Add words to the user's own dictionary - now, and (written to their word list) for every later run.
    Returns the file they were written to, or None if it could not be written."""
    dictionary()
    fresh = [w for w in dict.fromkeys(w.strip() for w in new_words) if w and " " not in w and w not in _DICT["exact"]]
    if not fresh:
        return user_words_file()
    for w in fresh:
        _DICT["exact"].add(w)
        _DICT["extra"].append(w.lower())
        if _DICT["words"] is not None:
            _DICT["words"].add(w.lower())
    for target in (user_words_file(), Path.home() / WORDS_FILE):
        try:
            old = target.read_text(encoding="utf-8") if target.exists() else ""
            target.write_text(old + ("" if not old or old.endswith("\n") else "\n") + "\n".join(fresh) + "\n", encoding="utf-8")
            return target
        except Exception:
            continue
    return None


_UNITS = set("ft in mm cm km kV kA mA kW MW kVA MVA kVAR MVAR Hz kHz MHz AC DC ac dc rms lb psi kPa cal J kJ mJ ms hr min sec dB VA Wh kWh pu".split())


def new_word_candidates(review):
    """From the words a run left as pictures: the ones that look like real words the dictionary simply
    does not have - acronyms and abbreviations above all (NEC, PPE, kV, TIAs).

    One entry per word (punctuation round it aside), most frequent first:
    {"word", "count", "suggest", "note", "png", "draw"}. "suggest" is the program's opinion - True for a
    run of capitals or anything seen more than once that is not one slip away from a real word."""
    found = {}
    for r in review or []:
        core = _core(r["reading"])[1]
        if core.endswith(("'s", "’s")):
            core = core[:-2]
        letters = sum(ch.isalpha() for ch in core)
        if len(core) < 2 or len(core) > 24 or letters < 1 or (letters < 2 and not any(ch.isdigit() for ch in core)):
            continue
        if not all(ch.isalnum() or ch in "-/&." for ch in core) or core.replace(".", "").replace("-", "").isdigit():
            continue
        if known_word(core):
            continue                                # a real word, left out for some other reason
        got = found.get(core)
        if got is None:
            found[core] = {"word": core, "count": r.get("count", 1), "png": r.get("png"), "draw": r.get("draw"),
                           "reading": r["reading"], "page": r.get("page", "")}
        else:
            got["count"] += r.get("count", 1)
    out = []
    for core, c in found.items():
        slip = _best_repair(core) if core.isalpha() else None
        capitals = core.isalpha() and core.isupper() and 2 <= len(core) <= 6
        if slip:
            c["suggest"], c["note"] = False, f"probably a misreading of '{slip}'"
        elif core in _UNITS:
            c["suggest"], c["note"] = True, "a unit of measurement"
        elif capitals:
            c["suggest"], c["note"] = c["count"] >= 2, "capitals: an abbreviation" + ("" if c["count"] >= 2 else ", seen once")
        elif any(ch.isdigit() for ch in core):
            c["suggest"], c["note"] = False, "a code with digits - tick only if it is read exactly right"
        elif core.isalpha() and not core.islower() and not core.istitle() and len(core) <= 6 and c["count"] >= 2:
            c["suggest"], c["note"] = True, "mixed capitals: an abbreviation"       # TIAs, kVA, PhD
        else:
            c["suggest"], c["note"] = False, ("appears more than once" if c["count"] >= 2 else "seen once") + " - tick it if it is right"
        out.append(c)
    return sorted(out, key=lambda c: (not c["suggest"], -c["count"], c["word"].lower()))


def _core(token):
    """Split a token into (leading punctuation, the word itself, trailing punctuation)."""
    a, b = 0, len(token)
    while a < b and not token[a].isalnum():
        a += 1
    while b > a and not token[b - 1].isalnum():
        b -= 1
    return token[:a], token[a:b], token[b:]


def _all_readings():
    """How many readings a page gets with the readers in use (a word all of them agree on has this many votes)."""
    if _OCR.get("name") == "rapid":
        return (len(_READ_HEIGHTS["tesseract"]) + 1) if _OCR.get("tesseract") else 1
    return len(_READ_HEIGHTS.get(_OCR.get("name") or "", ((0.0, ""),)))


def _plain_code(tok):
    """A number or code that can be taken on the readers' word when all of them agree: "130.8(H)", "70E-42",
    "2.5MVA", "600". Not one made only of the characters readers mix up among themselves (0 O o, 1 l I |) -
    "I0", "0O0" and "l1" look the same to every reader, so their agreeing proves nothing - and nothing
    with stray symbols in it."""
    core = _core(tok)[1] or tok
    if not core or any(ch in "{}|~`\\^_<>=+*'\"“”‘’" for ch in tok):
        return False
    if not all(ch.isalnum() or ch in ".,-–/()[]%:#&°" for ch in tok):
        return False
    return any(ch.isalnum() and ch not in "0Oo1lI" for ch in core) and sum(ch.isalnum() for ch in tok) >= 1


def _common_number(core):
    """Numbers that count as dictionary words: 1 to 100, and the years 1600 to 3000, written plainly
    (no leading zero, nothing attached - "70E", "1.5" and "007" are codes, not these)."""
    if not (core.isascii() and core.isdigit()) or core[0] == "0":
        return False
    return (len(core) <= 3 and 1 <= int(core) <= 100) or (len(core) == 4 and 1600 <= int(core) <= 3000)


def known_word(token):
    """True when the token is an ordinary word the dictionary has (case and edge punctuation aside;
    hyphenated words count when every part is known). Anything with a digit in it is never 'known'."""
    words = dictionary() if STRICTNESS.get("dictionary", True) else None
    if not words:
        return False
    core = _core(token)[1]
    if core in _DICT["exact"] or (core.endswith(("'s", "’s")) and core[:-2] in _DICT["exact"]):
        return True                                 # a word the user put in their own list, exactly as written
    if len(core) < 2 or not all(ch.isalpha() or ch in "-'’" for ch in core):
        return core in ("a", "A", "I")
    # Short runs of capitals are codes and abbreviations (SS, IO, CT, PTR), whatever a word list says,
    # and word lists hold odd two-letter entries: only everyday two-letter words count.
    if core.isupper() and len(core) <= 3:
        return False
    if len(core) == 2 and core.lower() not in _TWO_LETTER:
        return False
    if not (core.islower() or core.istitle() or core.isupper() or "-" in core or "'" in core or "’" in core):
        return False                                # mixed capitals (kV, pH, McX): not for the dictionary
    parts = [p for p in core.lower().replace("’", "'").split("-") if p]
    return bool(parts) and all(p in words or (p.endswith("'s") and p[:-2] in words) for p in parts)


def _word_neighbours(token):
    """Other real words one confusion away from this one: a single letter changed, or a pair such as
    rn / m swapped. These are the readings a dictionary word still has to beat on the page."""
    words = dictionary()
    head, core, tail = _core(token)
    low = core.lower()
    out = set()

    def shaped(new):                                # give the new word the capitals of the old
        if core.isupper():
            new = new.upper()
        elif core[:1].isupper():
            new = new[:1].upper() + new[1:]
        return head + new + tail

    if not all(ch.isalpha() for ch in low):
        return out
    if len(low) == 1:                               # "a" and "I" only rival each other
        return {shaped(w) for w in ("a", "i") if w != low} - {token}
    for j in range(len(low)):
        for ch in "abcdefghijklmnopqrstuvwxyz":
            if ch != low[j]:
                new = low[:j] + ch + low[j + 1:]
                if new in words:
                    out.add(shaped(new))
    for a, b in _CONFUSED_PAIRS:
        start = low.find(a)
        while start >= 0:
            new = low[:start] + b + low[start + len(a):]
            if new in words:
                out.add(shaped(new))
            start = low.find(a, start + 1)
    out.discard(token)
    return out


def _lookalike_words(token):
    """Real words this word turns into when one letter is swapped for a look-alike (he / be, cat / eat)."""
    words = dictionary()
    head, core, tail = _core(token)
    low, out = core.lower(), set()
    for j, ch in enumerate(low):
        for g in _LOOKALIKE_GROUPS:
            if ch in g:
                for alt in g:
                    new = low[:j] + alt.lower() + low[j + 1:]
                    if alt.lower() != ch and new.isalpha() and new in words and (len(new) != 2 or new in _TWO_LETTER):
                        out.add(new)
    for a, b in _CONFUSED_PAIRS:
        if a in low and low.replace(a, b, 1) in words:
            out.add(low.replace(a, b, 1))
    return out


def _derived_word(core):
    """True for a word no dictionary lists that is plainly made from ones it does: a plural or a tense,
    a re- / un- / non- form, or two ordinary words run together (benchtop, currentlimiting)."""
    low, words, freq = core.lower(), dictionary(), _DICT.get("freq")
    if not words or not low.isalpha():
        return False
    for end in ("s", "es", "ed", "d", "ing", "ly", "er", "ers", "ness", "able"):
        if low.endswith(end) and len(low) - len(end) >= 4 and low[:-len(end)] in words:
            return True
    for start in ("re", "un", "non", "pre", "de", "sub", "over", "under", "inter", "multi", "micro"):
        if low.startswith(start) and len(low) - len(start) >= 4 and low[len(start):] in words:
            return True
    if freq is not None:
        for cut in range(3, len(low) - 2):
            a, b = low[:cut], low[cut:]
            if a in words and b in words and float(freq[a]) >= 1000 and float(freq[b]) >= 1000:
                return True
    return False


def _best_repair(token, extra=()):
    """The one real word an unknown token most likely is, or None when there is none or no clear favourite."""
    options = list(dict.fromkeys(_repairs(token) + list(extra)))
    if len(options) <= 1:
        return options[0] if options else None
    freq = _DICT.get("freq")
    if freq is None:
        return None
    ranked = sorted(options, key=lambda o: -float(freq[_core(o)[1].lower()]))
    first, second = (float(freq[_core(o)[1].lower()]) for o in ranked[:2])
    return ranked[0] if first >= 10.0 * max(second, 1.0) else None


def _join_split_words(ocr):
    """Words broken over two lines with a hyphen ("connec-" / "tions") are judged whole.

    Returns the lines (a half is corrected where the whole word shows what it must be), and for each
    half - keyed (line number, word number) - True if the joined word is a real one, False if not."""
    ocr = [list(item) for item in ocr]
    toks = [item[0].split() for item in ocr]
    halves = {}
    for a, item in enumerate(ocr):
        if not toks[a] or not toks[a][-1].endswith(("-", "\u2010", "\u00ad")) or len(toks[a]) < 2:
            continue
        head, first, _ = _core(toks[a][-1][:-1] + "x")
        first = first[:-1]
        if len(first) < 2 or not first.isalpha():
            continue
        x0, y0, x1, y1 = item[1:5]
        below = [b for b, o in enumerate(ocr) if b != a and toks[b] and 0 < o[2] - y0 < 2.6 * (y1 - y0)
                 and min(x1, o[3]) - max(x0, o[1]) > 0.3 * min(x1 - x0, o[3] - o[1])]
        if not below:
            continue
        b = min(below, key=lambda k: ocr[k][2])
        _, second, tail = _core(toks[b][0])
        if not second.isalpha():
            continue
        whole = first + second
        if known_word(whole) or known_word(first + "-" + second):
            halves[(a, len(toks[a]) - 1)] = halves[(b, 0)] = True
            continue
        halves[(a, len(toks[a]) - 1)] = halves[(b, 0)] = False
        fixed = _best_repair(whole)
        if fixed:                                       # one half was misread: the whole word says which
            if fixed.lower().startswith(first.lower()) and len(fixed) > len(first):
                new = fixed[len(first):]
                toks[b][0] = toks[b][0].replace(second, new, 1)
            elif fixed.lower().endswith(second.lower()) and len(fixed) > len(second):
                new = fixed[:len(fixed) - len(second)]
                new = new.capitalize() if first[:1].isupper() else new
                toks[a][-1] = toks[a][-1].replace(first, new, 1)
            else:
                continue
            ocr[a][0], ocr[b][0] = " ".join(toks[a]), " ".join(toks[b])
            halves[(a, len(toks[a]) - 1)] = halves[(b, 0)] = None      # corrected: as good as a repaired word
    return [tuple(item) for item in ocr], halves


def _rarer_than_lookalike(token, times=20.0, counts=None):
    """True for a real word that has a far more common look-alike ("sate" beside "safe", "tor" beside
    "for"): when the OCR engine gives the rare one, it has more likely misread the common one."""
    freq = _DICT.get("freq")
    core = _core(token)[1].lower()
    if freq is None or core in _TECH_WORDS or core in _DICT["extra"]:
        return False
    mine = max(float(freq[core]), 1.0)
    counts = counts or {}
    here = counts.get(core, 0)
    for r in _lookalike_words(token):
        if float(freq[r]) >= times * mine:
            # ... unless this document itself uses the word freely ("arc" in an electrical standard)
            if here >= 3 and here >= 0.02 * counts.get(r, 0):
                continue
            return True
    return False


def _why_not(L, fit, i, c, usual, wide, common, seen, level, counts=None, half=None):
    """Why a word that its shape could not confirm is not accepted on the strength of the readings
    agreeing - or "" if it is accepted. `half`: for half of a word split over two lines, whether the
    whole word is a real one."""
    tok, w = L["tokens"][i], fit["words"][i]
    short = len(tok) <= 3 and L.get("split") == "boxes"     # a short word: a pixel either way is a lot
    lo, hi = (0.5, 1.9) if short else wide
    if not lo <= w[1] <= hi:
        return "word boundary unclear"
    if fit.get("sub") and (L.get("split") == "unsure" or not (0.55 if short else 0.8) <= w[1] / usual <= (1.7 if short else 1.25)):
        return "word boundary unclear"                  # not certain which ink belongs to this word
    if not all(fit["faces"][i].fitz.has_glyph(ord(ch)) for ch in tok):
        return "a character the font does not have"
    if not any(ch.isalnum() for ch in tok) and not (tok == "&" and votes_of(c) >= 2 and fit.get("sub")):
        return "punctuation on its own"
    core = _core(tok)[1]
    if core.endswith(("'s", "’s")):
        core = core[:-2]
    votes = votes_of(c)
    if half is False:
        return "split word not recognised"              # "conned-" / "lions": neither half is to be trusted
    real = half is True or known_word(tok) or core in common or tok == "&" or _common_number(core)
    if not real and votes >= 3 and 2 <= len(core) <= 3 and core.isalpha() and core.isupper() \
            and core.lower() in dictionary() and float((_DICT.get("freq") or {core.lower(): 0})[core.lower()]) >= 100000:
        real = True                                     # THE, AND, FOR, IN in a heading: common words in capitals
    whole = half is not True and known_word(tok)        # a word in its own right, to be tested as one
    if votes == 2 and whole and _lookalike_words(tok) and counts is not None and counts.get(core.lower(), 0) < 3:
        return "readings disagree"                      # "he" / "be": two readings are not enough
    if _quote_doubt(L, fit, i):
        return "quotation mark unclear"                 # no quotation mark where one was read
    if _case_doubt(L, fit, i):
        return "capital or small letter unclear"        # "Without" read where the letter is as low as a small w
    if whole and _rarer_than_lookalike(tok, counts=counts):
        return "rare word with a common look-alike"     # "sate": far more likely a misread "safe"
    if whole and votes < 3 and fit.get("sub") and _lost_to_rival(L, fit, i):
        return "another word fits the picture better"   # "tide" where the picture is closer to "title"
    if not real and level == "balanced" and votes >= 3:
        # An unknown word every reading agreed on. A name or an abbreviation is taken; an ordinary-looking
        # small-letter word that no dictionary has is far more often a misreading ("tenuonal"), and so is
        # anything one letter away from a word this page keeps using ("NEPA").
        near = [x for x, k in seen.items() if k >= 2 and k > seen.get(core, 0) and len(x) == len(core)
                and sum(a != b for a, b in zip(x, core)) == 1]
        if near or (core.isalpha() and len(core) >= 3 and (core.islower() or _repairs(tok))):
            return "not a word, and close to a real one" if near or _repairs(tok) else "not in the dictionary"
        if any(ch in "{}|~`\\^_<>" for ch in tok):
            return "not in the dictionary"
        if core.isalpha() and core.islower():
            # a unit or a list letter (mm, ft, b) if every reading has it; a longer word only if it is
            # plainly built from real ones (relocations, benchtop)
            if votes < 4 or (len(core) >= 4 and not _derived_word(core)):
                return "not in the dictionary"
    if conf_of(c) < OCR_CONFIDENCE and not (real and (votes >= 3 or len(core) >= 6)):
        return "the reader was not confident"
    if votes >= 2 and real and not (votes < 3 and _common_number(core)):
        return ""                                       # (a bare number needs three readings: "I0" is easily "10")
    if level == "balanced" and votes >= 3:
        return ""
    if votes < 2:
        return "readings disagree"
    if votes >= 3 and _common_number(core):
        return ""
    if votes >= _all_readings() >= 4 and any(ch.isdigit() for ch in tok) and _plain_code(tok):
        return ""                                       # a number or code that every reading gave the same way
    if votes >= _all_readings() >= 4 and re.match(r"^(\([A-Za-z]{1,2}\)|[A-Za-z]\.|[A-HJ-Z])$", tok):
        return ""                                       # a list letter - "(b)", "b.", "(B)" - or a lone capital, likewise
    return "number or code" if any(ch.isdigit() for ch in tok) else "not in the dictionary"


def _lost_to_rival(L, fit, i):
    """True if another real word, one letter-group confusion away (rn / m, tl / d, ti / u), fits this
    word's picture better. Such words differ by a whole letter, which shows even in a stand-in font."""
    tok = L["tokens"][i]
    head, core, tail = _core(tok)
    low, words, rivals = core.lower(), dictionary(), set()
    for a, b in _CONFUSED_PAIRS:
        start = low.find(a)
        while start >= 0:
            new = low[:start] + b + low[start + len(a):]
            if new in words and len(new) != len(low):
                rivals.add(new)
            start = low.find(a, start + 1)
    if not rivals:
        return False
    face, size, base = fit["faces"][i], fit["sizes"][i], fit["bases"][i]

    def match(text):
        one = _fit_line(face, dict(L, tokens=[text], words=[L["words"][i]]), size=size, base=base)
        return one["words"][0][0] if one else -1.0

    shaped = lambda new: head + (new.upper() if core.isupper() else new.capitalize() if core[:1].isupper() else new) + tail
    mine = match(tok)
    return any(match(shaped(r)) > mine for r in rivals)


def _repairs(token):
    """Dictionary words that an unknown token becomes when one look-alike character is swapped
    (reIay -> relay, c1ose -> close, modem <- rnodem). The page decides whether to use one."""
    words = dictionary()
    head, core, tail = _core(token)
    if not words or len(core) < 3 or sum(ch.isalpha() for ch in core) < len(core) - 1:
        return []
    found = set()
    for j, ch in enumerate(core):
        alts = set()
        for g in _LOOKALIKE_GROUPS:
            if ch in g:
                alts.update(g)
        for alt in alts - {ch}:
            new = core[:j] + alt + core[j + 1:]
            if new.isalpha() and (new.lower() in words) and (new.islower() or new.istitle() or new.isupper()):
                found.add(head + new + tail)
    for a, b in _CONFUSED_PAIRS:
        start = core.lower().find(a)
        while start >= 0:
            new = core[:start] + b + core[start + len(a):]
            if new.isalpha() and new.lower() in words:
                found.add(head + new + tail)
            start = core.lower().find(a, start + 1)
    return sorted(found)


# How sure the program must be before it redraws a word.
#   strict   - every letter is tested against its look-alikes; a number or code must beat every other
#              letter and digit clearly. Nothing wrong got through in testing; some words stay pictures.
#   balanced - looser match, look-alikes tested only where they are known to be confused. More words
#              are redrawn; a rare wrong character is possible, mostly in codes such as l1 / I1.
#   all      - whatever the OCR engine read is redrawn if it roughly fits. Nearly everything becomes
#              sharp text, and any OCR mistake is drawn as if it were right.
STRICTNESS = {"level": "strict"}
_LEVELS = {"strict": {"letter": 0.78, "line": 0.5}, "balanced": {"letter": 0.68, "line": 0.3},
           "all": {"letter": 0.40, "line": 0.0}}


FONT_CHOICES = ("auto", "one", "match")


def set_fonts(choice="auto"):
    """How fonts are chosen when text is redrawn.
      auto  - look at the first full page and decide (the default)
      one   - one installed family stands in for the whole document, bold and italic measured from the
              picture. For documents set in a typeface this computer does not have.
      match - match every line to the closest installed font, letter for letter. For documents made
              with ordinary fonts (Arial, Times New Roman, Calibri...)."""
    choice = (choice or "auto").lower()
    if choice not in FONT_CHOICES:
        raise ValueError(f"fonts must be one of {', '.join(FONT_CHOICES)}")
    STRICTNESS["fonts"] = choice
    return choice


def set_strictness(level, use_dictionary=True):
    level = (level or "strict").lower()
    if level not in _LEVELS:
        raise ValueError(f"strictness must be one of {', '.join(_LEVELS)}")
    STRICTNESS["level"], STRICTNESS["dictionary"] = level, bool(use_dictionary)
    return level


def _accept(L, fit, sure):
    """Per word: is the redrawn word close enough to the picture? One True / False each.

    A word passes when the OCR engine is sure of it, the font needs little stretch, the ink weight is
    similar, and every letter-sized stretch of it matches the picture."""
    level = STRICTNESS["level"]
    need = _LEVELS[level]["letter"]
    easy = {"strict": 0.66, "balanced": 0.58, "all": 0.40}[level]      # for words the dictionary knows
    lo, hi, light, heavy, conf = (0.75, 1.35, 0.4, 2.2, 0.0) if level == "all" else (0.85, 1.18, 0.6, 1.6, OCR_CONFIDENCE)
    sure = [conf_of(c) for c in sure]
    faces = fit.get("faces") or [fit["face"]] * len(L["tokens"])
    unsure = fit.get("unsure") or [False] * len(L["tokens"])
    if level == "all":
        unsure = [False] * len(L["tokens"])
    return [bool(worst >= (easy if known_word(tok) else need) and c >= conf and lo <= sx <= hi and light <= mass <= heavy
                 and not doubt and all(f.fitz.has_glyph(ord(ch)) for ch in tok))
            for tok, (ncc, sx, _, worst, mass), c, f, doubt in zip(L["tokens"], fit["words"], sure, faces, unsure)]


_LOOKALIKE_GROUPS = ("0OoQD", "1lI|!i", "ij", "2Zz", "5Ss", "6b", "8B3", "9gq", "ceo", "ao", "ae", "nhr", "nu", "uv", "vy",
                     "tf", "tl", "rt", "mn", "bh", "pq", "dcl", "kh", "CG", "PF", "PR", "EF", "EB", "UV", "cC", "vV", "wW",
                     "xX", "pb", "se", "sa", "S$", "8&", "([{", ")]}", "/|", ".,", ":;", "-_", "'`", "7T", "71", "4A", "DO", "HN", "KX")


_ALNUM = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz$&%#@"


def _lookalikes(ch, numeric=False):
    """Characters to test in place of ch. In a token with digits in it (a setting, a part number, a
    device code) nothing can be guessed from context, so every letter and digit is tried."""
    alts = set(_ALNUM) if numeric and ch.isalnum() else (set("0123456789") if ch.isdigit() else set())
    for g in _LOOKALIKE_GROUPS:
        if ch in g:
            alts.update(g)
    alts.discard(ch)
    return alts


def _second_opinion(L, fit, only=None, stop_early=False):
    """Check every letter against its look-alikes by drawing them in the matched font.

    For each letter of each word, the word is redrawn with that letter swapped for each look-alike
    (every other digit, for a digit) and compared with the picture around that letter. If any swap
    fits the picture at least as well as what the OCR engine read, the reading is not safe and the
    line is left as a picture.

    Returns one True / False per word. `only` limits the work to the words flagged True in it."""
    level = STRICTNESS["level"]
    if level == "all":                              # no second opinion: the OCR reading is taken as it is
        return [True] * len(L["tokens"]) if only is None else [bool(v) for v in only]
    face, s, yb, u, Du = fit["face"], fit["size"], fit["base"], L["u"], L["Du"]
    k = max(3, int(0.05 * s * u) * 2 + 1)
    slip = max(1, int(round(0.07 * s * u)))
    margin = int(round(0.3 * s * u))
    Db = cv2.GaussianBlur(Du, (k, k), 0)
    n = len(L["tokens"])
    per_word = list(zip(fit.get("faces") or [face] * n, fit.get("sizes") or [s] * n, fit.get("bases") or [yb] * n))
    current = [(face, s, yb)]                       # the font of the word being checked

    def drawn(text, c0, c1, ra, rz, keep=True):
        face, s, yb = current[0]
        g = face.word(text, keep)
        if g is None:
            return None
        pic, l, t, r, b = g
        hpx, top = max(1, int(round(s * (b - t) * u))), int(round((yb + s * t) * u))
        P = np.zeros((rz - ra, Du.shape[1]), np.float32)
        patch = cv2.resize(pic, (max(1, c1 - c0), hpx), interpolation=cv2.INTER_AREA)
        ya, yz = max(ra, top), min(rz, top + hpx)
        if yz > ya:
            P[ya - ra:yz - ra, c0:c1] = patch[ya - top:yz - top, :c1 - c0]
        if u > 1:
            small = cv2.resize(P, (max(1, P.shape[1] // u), max(1, P.shape[0] // u)), interpolation=cv2.INTER_AREA)
            P = np.clip(cv2.resize(small, (P.shape[1], P.shape[0]), interpolation=cv2.INTER_CUBIC), 0.0, 1.0)
        return cv2.GaussianBlur(P, (k, k), 0)

    def window_score(Pb, ra, rz, a, z):
        d = Db[ra:rz, a:z]
        best = -1.0
        for dx in range(-slip, slip + 1):
            if 0 <= a + dx and z + dx <= Pb.shape[1]:
                best = max(best, _pearson(Pb[:, a + dx:z + dx], d))
        return best

    def word_ok(tok, c0, c1, r0, r1):
        face, s, yb = current[0]
        ra, rz = max(0, r0 - int(0.45 * s * u)), min(Du.shape[0], r1 + int(0.45 * s * u))
        base = drawn(tok, c0, c1, ra, rz)
        if base is None:
            return False
        try:
            total = max(face.pil.getlength(tok), 1e-3)
            edges = [face.pil.getlength(tok[:j]) / total for j in range(len(tok) + 1)]
        except Exception:
            return False
        numeric = any(c.isdigit() for c in tok)
        if known_word(tok):
            # A real word. A non-word such as "reIay" is no rival to "relay"; what it must beat is every
            # other real word one confusion away ("form" / "farm", "modern" / "modem"), over the whole word.
            a, z = max(0, c0 - margin), min(Du.shape[1], c1 + margin)
            mine = window_score(base, ra, rz, a, z)
            for rival in _word_neighbours(tok):
                other = drawn(rival, c0, c1, ra, rz, keep=False)
                if other is not None and window_score(other, ra, rz, a, z) >= mine:
                    if os.environ.get("SNAPCLEAN_DEBUG"):
                        print(f"      second opinion: '{tok}' could be the word '{rival}' in {face.name}")
                    return False
            return True
        for j, ch in enumerate(tok):
            a = max(0, int(c0 + edges[j] * (c1 - c0)) - margin)
            z = min(Du.shape[1], int(math.ceil(c0 + edges[j + 1] * (c1 - c0))) + margin)
            if z - a < 3:
                continue
            mine = window_score(base, ra, rz, a, z)
            for alt in _lookalikes(ch, numeric and level == "strict"):
                other = drawn(tok[:j] + alt + tok[j + 1:], c0, c1, ra, rz, keep=False)
                # l, I, i, ! and | can be pixel-identical on screen. Inside an ordinary word the OCR
                # engine's reading is trusted unless the other letter fits clearly better. In a token
                # with digits (part numbers, settings) the reading must beat every other letter and
                # digit by a clear margin, or the token stays a picture.
                slack = -0.02 if numeric else (0.03 if ch in "lIi" and alt in "lIi!|1" else 0.0)
                if level == "balanced":
                    slack = 0.03 if ch in "lIi" and alt in "lIi!|1" and not numeric else 0.0
                if other is not None and window_score(other, ra, rz, a, z) >= mine + slack:
                    if os.environ.get("SNAPCLEAN_DEBUG"):
                        print(f"      second opinion: '{tok}' could be '{tok[:j] + alt + tok[j + 1:]}' in {face.name}")
                    return False
        return True

    out = []
    for i, (tok, (c0, c1, r0, r1)) in enumerate(zip(L["tokens"], L["words"])):
        if only is not None and not only[i]:
            out.append(False)                       # already failed the first checks: no need to look closer
            continue
        current[0] = per_word[i]                    # this word's own font (a bold or italic word, say)
        out.append(word_ok(tok, c0, c1, r0, r1))
        if stop_early and not out[-1]:
            return out + [False] * (len(L["tokens"]) - len(out))
    return out


def _guess_size(text, height):
    """Font size in pixels of a line known only by its text and the height of its ink."""
    tall = any(ch.isupper() or ch.isdigit() or ch in "bdfhklt()[]/|" for ch in text)
    deep = bool(set(text) & set("gjpqy()[]|"))
    return height / ((0.72 if tall else 0.52) + (0.21 if deep else 0.0))


def _size_unfitted(flines, fitted):
    """Lines the font fit could not measure at all are known only by their text and the box of their ink.
    Their size used to be guessed from the height of that box - some 8% too big on small print, enough to
    make every such line wrap in the Word file and the page run over. They are body text like the lines
    round them: they take the page's commonest font, the size of fitted lines whose ink is as tall, and
    their width as typed in that font (which lets the Word file fit each to its place)."""
    if not fitted:
        return
    keys = [(f.family, f.bold, f.italic) for f, _, _ in fitted]
    body = max(set(keys), key=keys.count)
    faces = [(f, s, hgt) for f, s, hgt in fitted if (f.family, f.bold, f.italic) == body]
    face = faces[0][0]
    typical = float(np.median([s for _, s, _ in faces]))
    for fl in flines:
        if fl.get("family") or not fl["text"].strip():
            continue
        hgt = fl["box"][3] - fl["box"][1]
        like = [s for _, s, h2 in faces if abs(h2 - hgt) <= 0.18 * max(hgt, 1.0)]
        size = float(np.median(like)) if len(like) >= 2 else float(np.clip(fl["size"], 0.8 * typical, 1.25 * typical))
        try:
            natural = float(face.fitz.text_length(fl["text"], fontsize=size))
        except Exception:
            continue
        wide = fl["box"][2] - fl["box"][0]
        if natural > 0 and 0.7 <= wide / natural < 0.97:
            # narrower than the body font would set it: smaller type (a note, italics) - sized by its width
            size, natural = size * wide / natural, wide
        if natural <= 0 or not 0.7 <= wide / natural <= 1.4:
            # typed in the body font it would be far wider or narrower than its ink: not body text
            # (a heading, small print) - the size that makes it fit, if that is a believable size
            fit_size = size * wide / max(natural, 1e-3)
            if not 0.55 * typical <= fit_size <= 2.6 * typical:
                continue
            size, natural = fit_size, wide
        fl.update(family=face.family, bold=False, italic=False, size=size, natural=natural, nsize=size, guessed=True)
        fl["base"] = float(fl["box"][3]) - (0.22 * size if set(fl["text"]) & set("gjpqy") else 0.0)


def _plan_page(rgb, ocr, setter, word_level=False):
    """Decide what to re-typeset on one page.

    Returns (picture with those words erased, jobs, hidden, words, replaced, lines for an exact-copy Word
    page, every line described for a flowing Word page).

    jobs: (text, font key, size px, sideways stretch, x px, baseline y px, (r, g, b)) per word to draw.
    hidden: (text, x0, y0, x1, y1) per piece of text that stays a picture and gets invisible text."""
    out = rgb.copy()
    total = replaced = repaired = 0
    jobs, hidden, dlines, flines = [], [], [], []
    fitted_faces = []
    # words the page itself keeps repeating (NFPA, a company name): as good as dictionary words
    seen = {}
    for item in ocr:
        cs = item[5] if isinstance(item[5], list) else [item[5]] * len(item[0].split())
        for tok, c in zip(item[0].split(), cs):
            core = _core(tok)[1]
            if votes_of(c) >= 2 and len(core) >= 3 and core.isalpha():
                seen[core] = seen.get(core, 0) + 1
    common = {core for core, k in seen.items() if k >= 3} | set(_WORKER.get("terms") or ())
    counts = dict(_WORKER.get("counts") or {})          # how often the document uses each word
    if not counts:
        for core, k in seen.items():
            counts[core.lower()] = counts.get(core.lower(), 0) + k
    as_read = [item[0].split() for item in ocr]         # before anything is corrected: what answers are filed under
    ocr, halves = _join_split_words(ocr) if dictionary() and STRICTNESS.get("dictionary", True) else (ocr, {})
    plans = list(setter.plan(rgb, ocr))
    # What this page's full stops and commas look like (height, depth below the line): most are read
    # right, so the usual shape of each is known, and a doubtful one can be put with its own kind.
    shapes = {".": [], ",": []}
    for plan in plans:
        if plan is not None and plan[1].get("sub"):
            for i, tok in enumerate(plan[0]["tokens"]):
                got = _foot_mark(plan[0], plan[1], i)
                if got:
                    shapes[tok[-1]].append(got)
    marks = None
    if len(shapes["."]) >= 6 and len(shapes[","]) >= 6:
        dot = tuple(float(np.median([m[j] for m in shapes["."]])) for j in (0, 1))
        com = tuple(float(np.median([m[j] for m in shapes[","]])) for j in (0, 1))
        if com[0] >= dot[0] + 0.03 and com[1] >= dot[1] + 0.02:
            marks = (dot, com)
    _WORKER["why"] = {}
    opts = _WORKER.get("options") or {}
    tints = []                                          # words to highlight in the page picture
    for li, ((text, x0, y0, x1, y1, conf), plan) in enumerate(zip(ocr, plans)):
        tokens = text.split()
        total += len(tokens)
        fl = {"text": " ".join(tokens), "box": (float(x0), float(y0), float(x1), float(y1)), "ok": False, "oks": None,
              "styles": None,
              "family": None, "bold": False, "italic": False, "size": _guess_size(text, float(y1 - y0)),
              "base": float(y1) - (0.22 * _guess_size(text, float(y1 - y0)) if set(text) & set("gjpqy") else 0.0),
              "colour": (0.0, 0.0, 0.0)}
        flines.append(fl)
        sure = conf if isinstance(conf, list) and len(conf) == len(tokens) else \
            [min(conf) if isinstance(conf, list) and conf else (conf if not isinstance(conf, list) else 0.0)] * len(tokens)
        if plan is None or not any(ch.isalnum() for ch in text):      # stray dots and dashes are left alone
            if os.environ.get("SNAPCLEAN_DEBUG"):
                print("    ?? ", "could not measure:", text)
            if opts.get("highlight_pdf") and any(ch.isalnum() for ch in text):
                tints.append((float(x0), float(y0), float(x1), float(y1)))
            hidden.append((text, x0, y0, x1, y1))
            continue
        L, fit = plan
        strong = L["D"] >= 0.9                          # the line's full-strength ink
        line_ink = np.median(L["crop"][strong], axis=0) if strong.sum() >= 3 else L["crop"][L["D"] >= L["D"].max() * 0.95].mean(axis=0)
        if fit["words"] and 0.8 <= float(np.median([w[1] for w in fit["words"]])) <= 1.25:      # a believable font match
            fitted_faces.append((fit["face"], float(fit["size"]), float(y1 - y0)))
            fl.update(family=fit["face"].family, bold=fit["face"].bold, italic=fit["face"].italic, size=float(fit["size"]),
                      base=float(L["org"][1] + fit["base"]),
                      box=(float(L["org"][0] + L["words"][0][0] / L["u"]), float(L["org"][1] + min(w[2] for w in L["words"]) / L["u"]),
                           float(L["org"][0] + L["words"][-1][1] / L["u"]), float(L["org"][1] + max(w[3] for w in L["words"]) / L["u"])))
        fl["colour"] = tuple(float(c) for c in np.clip(np.rint(line_ink / 4.0) * 4.0, 0, 255))
        # An unknown word one look-alike away from a real one ("reIay"): try the real word, and keep it
        # if it fits the picture at least as well.
        level = STRICTNESS["level"]
        fixed_here = set()
        for i in range(len(L["tokens"])):               # halves of split words put right by the whole word
            if halves.get((li, i), 0) is None:
                fixed_here.add(i)
                sure[i] = conf_of(sure[i]) + (2 if level == "balanced" and votes_of(sure[i]) >= 3 else 0)
        if dictionary() and STRICTNESS.get("dictionary", True):
            for i, tok in enumerate(L["tokens"]):
                if known_word(tok) or any(ch.isdigit() for ch in tok) or (li, i) in halves or votes_of(sure[i]) >= USER_VOTES:
                    continue
                head_, core_, tail_ = _core(tok)
                if core_ in common:
                    continue
                # a real word one confusion away - or one of the document's own terms one letter away
                # ("NEPA" in a document full of "NFPA")
                choice = _best_repair(tok, [head_ + w + tail_ for w in sorted(common) if len(w) == len(core_)
                                            and len(w) >= 4 and sum(a != b for a, b in zip(w, core_)) == 1])
                if not choice:
                    continue
                options = [choice]
                L2 = dict(L, tokens=L["tokens"][:i] + [options[0]] + L["tokens"][i + 1:])
                if fit.get("sub"):
                    # No matching font to judge by. The one real word it could be is used for the text. It
                    # is redrawn only in the balanced setting, and only if every reading gave the same
                    # misreading - one consistent slip, not a blur nobody could read.
                    L = L2
                    fixed_here.add(i)
                    sure[i] = conf_of(sure[i]) + (2 if level == "balanced" and votes_of(sure[i]) >= 3 else 0)
                    repaired += 1
                    continue
                fit2 = _fit_line(fit["face"], L2, size=fit["size"], local=True)
                if fit2 and fit2["words"][i][3] >= fit["words"][i][3] - 0.01:
                    if os.environ.get("SNAPCLEAN_DEBUG"):
                        print(f"      dictionary: '{tok}' read as '{options[0]}'")
                    L, fit = L2, fit2
                    repaired += 1
            fl["text"] = " ".join(L["tokens"])
        level = STRICTNESS["level"]
        if fit.get("sub"):
            # A comma hangs below the line and a full stop sits on it, whatever the typeface: where the
            # picture is clear about it, the picture wins over the reading.
            toks = list(L["tokens"])
            for i, tok in enumerate(toks):
                got = _foot_mark(L, fit, i) if marks else None
                if got is None:
                    continue
                tall, below = got
                (dot_t, dot_b), (com_t, com_b) = marks
                # clearly on the other side: nearer than a quarter of the way from the other kind's usual shape
                is_dot = tall <= dot_t + 0.25 * (com_t - dot_t) and below <= dot_b + 0.25 * (com_b - dot_b)
                is_com = tall >= com_t - 0.25 * (com_t - dot_t) and below >= com_b - 0.25 * (com_b - dot_b)
                mark = "." if is_dot else ("," if is_com else tok[-1])
                if mark != tok[-1]:
                    if os.environ.get("SNAPCLEAN_DEBUG"):
                        print(f"      punctuation: '{tok}' is '{tok[:-1] + mark}' by its shape")
                    toks[i] = tok[:-1] + mark
            if toks != L["tokens"]:
                L = dict(L, tokens=toks)
                fl["text"] = " ".join(toks)
            # A stand-in font cannot confirm letters by their shape. What counts instead: the readings
            # of the page agree, and the word is a real one (or one this page keeps using).
            checks = [level == "all"] * len(L["tokens"])
        else:
            fit = _style_words(setter, L, fit)      # bold / italic / other-font words inside the line
            # Word by word: does the redrawn word match the picture, and does no look-alike match as well?
            first = _accept(L, fit, sure)
            checks = _second_opinion(L, fit, only=first)
        wide = (0.72, 1.4) if fit.get("sub") else (0.8, 1.25)
        usual = float(np.median([w[1] for w in fit["words"]]))
        # one word read as two ("re lay"): the gap between them is far narrower than the line's other gaps
        between = [L["words"][k + 1][0] - L["words"][k][1] for k in range(len(L["words"]) - 1)]
        tight = set()
        if len(between) >= 3:
            for k, g in enumerate(between):
                if g < 0.7 * float(np.median(between)) and \
                        known_word(_core(L["tokens"][k])[1] + _core(L["tokens"][k + 1])[1]):
                    tight.update((k, k + 1))
        why = [""] * len(L["tokens"])
        for i, (tok, w, c) in enumerate(zip(L["tokens"], fit["words"], sure)):
            if votes_of(c) >= USER_VOTES:               # the user typed this word in: it is what it is
                # ... unless the program cannot tell where the word is: drawn into the wrong space it
                # would come out squeezed or stretched, so there the picture stays
                fits = 0.5 <= w[1] <= 1.9
                checks[i] = fits and all(fit["faces"][i].fitz.has_glyph(ord(ch)) for ch in tok)
                why[i] = "" if checks[i] else ("word boundary unclear" if not fits else "a character the font does not have")
                continue
            if i in tight:
                checks[i] = False
                why[i] = "word boundary unclear"
                continue
            if checks[i] or level == "all":
                continue
            why[i] = _why_not(L, fit, i, c, usual, wide, common, seen, level, counts,
                              True if i in fixed_here else halves.get((li, i)))
            if not why[i]:
                checks[i] = True
        for i, reason in enumerate(why):
            if not checks[i]:
                raw = as_read[li][i] if li < len(as_read) and len(as_read[li]) == len(L["tokens"]) else L["tokens"][i]
                if len(_WORKER.setdefault("review", [])) < 600 and reason != "a character the font does not have" \
                        and votes_of(sure[i]) < USER_VOTES:
                    entry = _review_entry(rgb, L, i, raw, L["tokens"][i], reason or "shape did not match", fit)
                    # Is the box on this word? Drawn at the line's size the word should be about as wide
                    # as its box; when it is far off, the box is on something else (part of the word, two
                    # words, a neighbour) and what the user typed would be filed under the wrong reading.
                    rel = fit["words"][i][1] / max(usual, 1e-3)
                    entry["loose"] = bool(reason == "word boundary unclear" or not 0.62 <= rel <= 1.6)
                    _WORKER["review"].append(entry)
                _WORKER.setdefault("why", {})
                _WORKER["why"][reason or "shape did not match"] = _WORKER["why"].get(reason or "shape did not match", 0) + 1
        if os.environ.get("SNAPCLEAN_DEBUG"):
            print("   ", "OK " if all(checks) else "-- ", fit["face"].name, round(fit["size"], 1),
                  [(t, round(float(w[1]), 2), round(w[3], 2), round(w[4], 2), round(float(c), 2), ok or y)
                   for t, w, c, ok, y in zip(L["tokens"], fit["words"], sure, checks, why)])
        if len(checks) == len(tokens) and fl["family"]:
            fl["oks"] = [bool(c) for c in checks]
        if len(checks) == len(tokens) and fl["family"]:
            # where each word starts, and how wide the line is when typed in its font: the Word file
            # uses these to keep the original's line breaks and to fit each line to its place
            fl["xs"] = [float(L["org"][0] + w[0] / L["u"]) for w in L["words"]]
            try:
                gap = float(fit["face"].fitz.text_length(" ", fontsize=fit["size"]))
                fl["natural"] = float(sum(f.fitz.text_length(t, fontsize=fs) for t, f, fs in
                                          zip(L["tokens"], fit["faces"], fit["sizes"])) + gap * (len(L["tokens"]) - 1))
                fl["nsize"] = float(fit["size"])
            except Exception:
                pass
        if (opts.get("word_pictures") or opts.get("highlight_pdf")) and len(checks) == len(L["tokens"]):
            for i, good in enumerate(checks):
                if good:
                    continue
                c0, c1, r0, r1 = L["words"][i]
                if opts.get("highlight_pdf"):
                    tints.append((L["org"][0] + c0 / L["u"], L["org"][1] + r0 / L["u"],
                                  L["org"][0] + c1 / L["u"], L["org"][1] + r1 / L["u"]))
                if opts.get("word_pictures") and word_level and fl["oks"] and 0.5 <= fit["words"][i][1] <= 1.9:
                    pic = _word_picture(rgb, L, fit, i, tint=bool(opts.get("highlight")))
                    if pic:
                        fl.setdefault("pics", {})[i] = pic
        # Confirmed words are redrawn; a word that is not confirmed (often a number or a code, where
        # nothing may be guessed) stays as its original picture, in place. A line with little
        # confirmed in it is left alone altogether.
        chars = sum(len(t) for t in L["tokens"])
        enough = max(1.0, _LEVELS[STRICTNESS["level"]]["line"] * chars)
        if len(checks) != len(L["tokens"]) or sum(len(t) for t, c in zip(L["tokens"], checks) if c) < enough:
            hidden.append((text, x0, y0, x1, y1))
            continue
        ok = checks
        fl["ok"] = all(checks)
        ox, oy = L["org"]
        u, s = L["u"], fit["size"]
        face, sentence = fit["face"], " ".join(L["tokens"])
        mixed = any(f is not face for f in fit["faces"])
        fl["styles"] = [(f.family, f.bold, f.italic) for f in fit["faces"]] if mixed else None
        try:
            natural = float(face.pil.getlength(sentence)) / _REF * s
        except Exception:
            natural = 0.0
        shade = tuple(float(c) for c in np.clip(np.rint(line_ink / 4.0) * 4.0, 0, 255))

        def box_font(f, size, base):
            return {"family": f.family, "bold": f.bold, "italic": f.italic, "size": float(size),
                    "base": float(oy + base), "ascent": f.ascent, "descent": f.descent, "colour": shade}

        if all(checks) and not mixed:                   # exact-copy Word page: the whole line as one text box
            dlines.append(dict(box_font(face, s, fit["base"]), text=sentence, natural=natural,
                               x=float(ox + L["words"][0][0] / u - s * fit["words"][0][2]),
                               width=float((L["words"][-1][1] - L["words"][0][0]) / u)))
        else:                                           # ... or one small box per confirmed word
            for tok, (c0, c1, r0, r1), wfit, good, f, fs, fb in zip(L["tokens"], L["words"], fit["words"], checks,
                                                                   fit["faces"], fit["sizes"], fit["bases"]):
                if good:
                    try:
                        wide = float(f.pil.getlength(tok)) / _REF * fs
                    except Exception:
                        wide = 0.0
                    dlines.append(dict(box_font(f, fs, fb), text=tok, natural=wide,
                                       x=float(ox + c0 / u - fs * wfit[2] * wfit[1]), width=float((c1 - c0) / u)))
        for tok, (c0, c1, r0, r1), (ncc, sx, left, _, _), good, wface, wsize, wbase in zip(
                L["tokens"], L["words"], fit["words"], ok, fit["faces"], fit["sizes"], fit["bases"]):
            wx0, wx1, wy0, wy1 = c0 / u, c1 / u, r0 / u, r1 / u
            if not good:
                hidden.append((tok, ox + wx0, oy + wy0, ox + wx1, oy + wy1))
                continue
            xa, xb = max(0, int(math.floor(wx0)) - 2), min(L["D"].shape[1], int(math.ceil(wx1)) + 2)   # incl. soft edges
            ya, yb = max(0, int(math.floor(wy0)) - 2), min(L["D"].shape[0], int(math.ceil(wy1)) + 2)
            d = L["D"][ya:yb, xa:xb]
            # Thin strokes never reach full darkness on screen, so a word's own pixels read too pale.
            # Keep the word's hue but give it the full strength of the line's ink.
            own = np.median(L["crop"][ya:yb, xa:xb][d >= max(0.3, d.max() * 0.8)], axis=0) - L["bg"]
            full = line_ink - L["bg"]
            cos = float(own @ full) / max(float(np.linalg.norm(own) * np.linalg.norm(full)), 1e-6)
            colour = line_ink if cos > 0.97 else L["bg"] + own * (np.abs(full).max() / max(np.abs(own).max(), 1e-3))
            colour = np.clip(np.rint(colour / 4.0) * 4.0, 0, 255)
            mask = cv2.dilate((d > 0.08).astype(np.uint8), np.ones((3, 3), np.uint8)).astype(bool)
            out[oy + ya:oy + yb, ox + xa:ox + xb][mask] = np.rint(L["bg"]).astype(np.uint8)
            spaced = tok if (c0, c1) == L["words"][-1][:2] else tok + " "     # so copied text keeps its spaces
            if not all(checks):
                spaced = tok                              # next to a hidden-text word: that one brings the space
            try:        # the word was measured with letter pairs tucked together (kerning); the PDF draws it without
                sx = sx * float(wface.pil.getlength(tok)) / _REF / max(float(wface.fitz.text_length(tok, fontsize=1.0)), 1e-3)
            except Exception:
                pass
            jobs.append((spaced, wface.key, float(wsize), float(sx), float(ox + wx0 - wsize * left * sx),
                         float(oy + wbase), tuple(float(c) for c in colour)))
            replaced += 1
    _WORKER["repaired"] = repaired                  # read by _page_result straight after
    _size_unfitted(flines, fitted_faces)
    for x0, y0, x1, y1 in tints:                        # a highlighter stroke over each unidentified word
        ya, yb = max(0, int(y0) - 3), min(out.shape[0], int(math.ceil(y1)) + 3)
        xa, xb = max(0, int(x0) - 3), min(out.shape[1], int(math.ceil(x1)) + 3)
        patch = out[ya:yb, xa:xb].astype(np.float32)
        patch[:, :, 2] *= 0.45                          # white paper -> yellow; black ink stays black
        out[ya:yb, xa:xb] = np.rint(patch).astype(np.uint8)
    return (out, jobs, [(t, float(a), float(b), float(c), float(d)) for t, a, b, c, d in hidden], total, replaced,
            dlines, flines)


def _draw_page(page, k, jobs, hidden, fonts):
    """Put one page's real text and hidden text into the PDF."""
    import pymupdf as fitz
    for tok, key, s, sx, x, y, colour in jobs:
        font = fonts.get(key)
        if font is None:
            font = fonts[key] = fitz.Font(fontfile=key[1]) if key[0] == "file" else fitz.Font(key[1])
        pt = fitz.Point(x * k, y * k)
        tw = fitz.TextWriter(page.rect, color=tuple(c / 255.0 for c in colour))
        tw.append(pt, tok, font=font, fontsize=s * k)
        tw.write_text(page, morph=(pt, fitz.Matrix(sx, 1.0)))
    for item in hidden:
        _hidden_text(page, fonts, item, k)


def _hidden_text(page, fonts, item, k):
    """Invisible, searchable text stretched over its place in the picture."""
    import pymupdf as fitz
    text, x0, y0, x1, y1 = item
    font = fonts["latin"]
    if not all(font.has_glyph(ord(ch)) for ch in text):
        fonts["wide"] = fonts.get("wide") or fitz.Font("cjk")     # built-in fallback with wide Unicode coverage
        font = fonts["wide"]
    size = max(2.0, (y1 - y0) * k * 0.78)
    length = font.text_length(text, fontsize=size)
    if length <= 0:
        return False
    origin = fitz.Point(x0 * k, y1 * k - 0.22 * (y1 - y0) * k)
    tw = fitz.TextWriter(page.rect)
    tw.append(origin, text, font=font, fontsize=size)
    tw.write_text(page, render_mode=3, morph=(origin, fitz.Matrix((x1 - x0) * k / length, 1.0)))   # 3 = invisible
    return True


# ---- flowing Word layout: paragraphs, tables and pictures instead of one text box per line --------

def _clusters(values, gap):
    """Group sorted numbers that lie within `gap` of each other; returns the group means."""
    out, cur = [], []
    for v in sorted(values):
        if cur and v - cur[-1] > gap:
            out.append(float(np.mean(cur)))
            cur = []
        cur.append(v)
    if cur:
        out.append(float(np.mean(cur)))
    return out


def _unsure_share(fl):
    """How much of a line (by letters) could not be confirmed: 0 to 1."""
    toks = fl["text"].split()
    oks = fl.get("oks")
    if oks and len(oks) == len(toks):
        return sum(len(t) for t, ok in zip(toks, oks) if not ok) / max(1, sum(len(t) for t in toks))
    return 0.0 if fl.get("ok") else 1.0


def _looks_like_formula(fl):
    text = fl["text"]
    toks = text.split()
    if not toks or len(text) > 70:
        return False
    oks = fl.get("oks")
    if oks and len(oks) == len(toks):
        unsure = sum(len(t) for t, ok in zip(toks, oks) if not ok) / max(1, sum(len(t) for t in toks))
    else:
        unsure = 0.0 if fl.get("ok") else 1.0
    symbols = sum(ch in "=+×÷*^<>[]{}|√∑±≤≥" for ch in text)
    return (unsure >= 0.35 and "=" in text) or (unsure >= 0.6 and symbols >= 2)


_CAPTION = re.compile(r"^\s*(FIGURE|Figure|Fig\.|TABLE|Table|Exhibit|EXHIBIT)\s+[A-Z0-9]")


def _is_caption(fl):
    return bool(_CAPTION.match(fl["text"]))


def _framed_table(hline, vline, hk, vk):
    """A table with a frame round it, whose cells may run across several columns or rows (a form).
    hline / vline: the straight ink of one connected piece of line work. Returns {"xs", "ys", "span":
    {(row, col): (rows, cols)} for each real cell, "covered": {(row, col): (row, col) of the cell it is
    part of}}, None if this is not a framed table, or "drawing" when the lines make boxes that do not
    fit a table (a flowchart)."""
    ch, cw = hline.shape
    def edges(hits):
        """Positions of the lines; a thick run (a shaded band, solid ink) counts as its two edges."""
        out, run = [], []
        for v in list(hits) + [None]:
            if v is not None and (not run or v - run[-1] <= 3):
                run.append(int(v))
                continue
            if run:
                out += [run[0], run[-1]] if run[-1] - run[0] > 6 else [float(np.mean(run))]
            run = [int(v)] if v is not None else []
        return out

    xs = edges(np.flatnonzero(vline.sum(axis=0) >= 0.9 * vk))
    ys = edges(np.flatnonzero(hline.sum(axis=1) >= 0.9 * hk))
    if len(xs) < 2 or len(ys) < 2:
        return None
    xs, ys = [int(round(v)) for v in xs], [int(round(v)) for v in ys]
    # the rules across run from the table's left edge to its right: where the frame's own upright line
    # is too faint to have been found, the edge is still there
    if xs[0] > 6:
        xs.insert(0, 0)
    if xs[-1] < cw - 7:
        xs.append(cw - 1)
    implied = {xs[0], xs[-1]}                           # (found or not: a faint line may be found only in part)

    def inked(mask, a0, a1, at, upright):
        if upright and at in implied:
            return True
        """Is there a line along this stretch of boundary?"""
        lo, hi = max(0, at - 3), at + 4
        whole = mask[:, lo:hi].any(axis=1) if upright else mask[lo:hi, :].any(axis=0)
        if whole.size and float(whole.mean()) >= 0.93:
            return True                                 # a line right across: a nick in it is not a way through
        run = whole[a0:a1]
        return run.size > 0 and float(run.mean()) >= 0.6

    def grid(xs, ys):
        H = [[inked(hline, xs[c], xs[c + 1], ys[r], False) for c in range(len(xs) - 1)] for r in range(len(ys))]
        V = [[inked(vline, ys[r], ys[r + 1], xs[c], True) for c in range(len(xs))] for r in range(len(ys) - 1)]
        return H, V

    for _ in range(6):                                  # lines that bound nothing (a rule to write on) are no grid lines
        H, V = grid(xs, ys)
        keep_y = [r for r in range(len(ys)) if r in (0, len(ys) - 1) or any(H[r])]
        keep_x = [c for c in range(len(xs)) if c in (0, len(xs) - 1) or any(V[r][c] for r in range(len(ys) - 1))]
        if len(keep_y) == len(ys) and len(keep_x) == len(xs):
            break
        xs, ys = [xs[c] for c in keep_x], [ys[r] for r in keep_y]
        if len(xs) < 2 or len(ys) < 2:
            return None
    R, C = len(ys) - 1, len(xs) - 1
    if not (all(H[0]) and all(H[R]) and all(V[r][0] for r in range(R)) and all(V[r][C] for r in range(R))):
        return None                                     # no frame all the way round
    if R * C < 2:
        return "box"
    parent = {(r, c): (r, c) for r in range(R) for c in range(C)}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for r in range(R):
        for c in range(C):
            if c + 1 < C and not V[r][c + 1]:
                parent[find((r, c + 1))] = find((r, c))
            if r + 1 < R and not H[r + 1][c]:
                parent[find((r + 1, c))] = find((r, c))
    groups = {}
    for cell in parent:
        groups.setdefault(find(cell), []).append(cell)
    span, covered = {}, {}
    for cells in groups.values():
        r0, r1 = min(r for r, _ in cells), max(r for r, _ in cells)
        c0, c1 = min(c for _, c in cells), max(c for _, c in cells)
        if (r1 - r0 + 1) * (c1 - c0 + 1) != len(cells):
            if os.environ.get("SNAPCLEAN_DEBUG_TABLE"):
                print("not a table: cell", sorted(cells), "xs", xs, "ys", ys)
            return "drawing"                            # an L-shaped "cell": boxes joined by lines, not a table
        span[(r0, c0)] = (r1 - r0 + 1, c1 - c0 + 1)
        for cell in cells:
            if cell != (r0, c0):
                covered[cell] = (r0, c0)
    if len(span) < 2:
        return "box"                                    # a frame with one space in it
    return {"xs": xs, "ys": ys, "span": span, "covered": covered}


# "(8)", "a.", "12.", "[3]", a bullet - with its bracket or full stop: "The" and "If" are not list markers
_MARKER = re.compile(r"^(\(?[0-9A-Za-z]{1,3}\)|\[[0-9A-Za-z]{1,3}\]|[0-9]{1,3}\.|[A-Za-z]\.|[•▪■□❑◦*-])$")


def _starts_item(fl):
    """Does this line open a list item - a marker, then its text set off from it?"""
    words = fl["text"].split()
    if len(words) < 2 or not _MARKER.match(words[0]):
        return False
    xs = fl.get("xs")
    if xs and len(xs) == len(words):
        return xs[1] - xs[0] >= (0.45 * len(words[0]) + 0.7) * fl["size"]      # more than a word space after it
    return words[0][:1] in "([" or words[0][-1:] in ")]"


def _join_same_row(lines, mh):
    """The reader sometimes hands one printed line over in two pieces - a list number and its text,
    "INFORMATIVE" and "ANNEX I". Each piece would become a paragraph of its own, the second pushed down
    a line (and everything under it with it). Pieces on one baseline that all but touch are joined; a
    list marker is joined to the text a little further off."""
    out = []
    # the pieces row by row, left to right. Rows are gathered by where the pieces' middles are (a marker's
    # baseline can sit a little off its text's), each piece joining the row it is level with - not by
    # rounding heights into bins, which parts two pieces that happen to straddle a bin's edge.
    rows = []
    for fl in sorted(lines, key=lambda fl: (fl["box"][1] + fl["box"][3]) / 2):
        mid = (fl["box"][1] + fl["box"][3]) / 2
        if rows and abs(mid - rows[-1][0]) <= 0.45 * mh:
            rows[-1][1].append(fl)
            rows[-1][0] += (mid - rows[-1][0]) / len(rows[-1][1])
        else:
            rows.append([mid, [fl]])
    ordered = [fl for _, row in rows for fl in sorted(row, key=lambda fl: fl["box"][0])]
    for fl in ordered:
        a = out[-1] if out else None
        if a is not None and not a.get("pics") and not fl.get("pics"):
            gap = fl["box"][0] - a["box"][2]
            marker = bool(_MARKER.match(a["text"].strip()))
            shared = min(a["box"][3], fl["box"][3]) - max(a["box"][1], fl["box"][1])
            level = abs(fl["base"] - a["base"]) <= 0.22 * mh or \
                shared >= 0.6 * min(a["box"][3] - a["box"][1], fl["box"][3] - fl["box"][1])
            alike = marker or 0.75 <= fl["size"] / max(a["size"], 1e-3) <= 1.33     # (a marker's own size is a guess)
            # ... and so is a symbol being defined: "t" "=" "time of arc exposure in seconds."
            defines = (a["text"].strip().endswith(("=", ":")) or fl["text"].strip().startswith("=")) and \
                len(a["text"].split()) <= 3 and len(a["text"].strip()) <= 12
            # ... or a short label on its own with its text beside it ("MVA", then what it stands for) -
            # but not the tail of a sentence or of a divided word ("ing.", "tion-"), which may only
            # happen to be level with a line in the next column
            label = bool(re.match(r"^[A-Za-z0-9_%°]{1,5}[,:=]?$", a["text"].strip()))
            alike = alike or defines or label
            reach = 2.4 * mh if (marker or defines or label) else 0.8 * mh
            if level and alike and -0.4 * mh <= gap <= reach:
                na, nb = len(a["text"].split()), len(fl["text"].split())
                main = a if len(a["text"]) >= len(fl["text"]) else fl

                def per_word(x, n, key, fill):
                    v = x.get(key)
                    return list(v) if v and len(v) == n else [fill(x)] * n

                merged = dict(main)
                merged["text"] = a["text"].strip() + " " + fl["text"].strip()
                merged["box"] = (min(a["box"][0], fl["box"][0]), min(a["box"][1], fl["box"][1]),
                                 max(a["box"][2], fl["box"][2]), max(a["box"][3], fl["box"][3]))
                merged["ok"] = bool(a.get("ok") and fl.get("ok"))
                merged["oks"] = per_word(a, na, "oks", lambda x: bool(x.get("ok"))) + per_word(fl, nb, "oks", lambda x: bool(x.get("ok")))
                look = lambda x: (x["family"], x["bold"], x["italic"]) if x.get("family") else None
                styles = per_word(a, na, "styles", look) + per_word(fl, nb, "styles", look)
                merged["styles"] = styles if len(set(styles)) > 1 and all(styles) else None
                def starts(x, n):
                    """Where each word of a piece begins: as measured, or spread along it by length."""
                    if x.get("xs") and len(x["xs"]) == n:
                        return list(x["xs"])
                    words, x0, x1 = x["text"].split(), x["box"][0], x["box"][2]
                    total = max(1, sum(len(w) + 1 for w in words) - 1)
                    out, run = [], 0
                    for w in words:
                        out.append(x0 + (x1 - x0) * run / total)
                        run += len(w) + 1
                    return out

                if a.get("xs") or fl.get("xs"):
                    merged["xs"] = starts(a, na) + starts(fl, nb)
                else:
                    merged.pop("xs", None)
                if a.get("natural") and fl.get("natural"):
                    merged["natural"] = float(a["natural"] * main["size"] / max(a.get("nsize") or a["size"], 1e-3)
                                              + fl["natural"] * main["size"] / max(fl.get("nsize") or fl["size"], 1e-3)
                                              + 0.26 * main["size"])
                    merged["nsize"] = float(main["size"])
                else:
                    merged.pop("natural", None)
                    merged.pop("nsize", None)
                out[-1] = merged
                continue
        out.append(fl)
    return out


def _open_tables(blocks, lines, mh, w, h):
    """Boxes of tables that have rules across but no upright lines. Such a table is two or more rules of
    the same width, one above the other, with rows between them in which the text stands in three or
    more separate columns."""
    rules = sorted((b for b in blocks if b["kind"] == "rule" and b["box"][2] - b["box"][0] >= 12 * mh), key=lambda b: b["box"][1])
    out, used = [], set()
    for i, top in enumerate(rules):
        if id(top) in used:
            continue
        group = [top]
        for other in rules[i + 1:]:
            if abs(other["box"][0] - top["box"][0]) <= 1.5 * mh and abs(other["box"][2] - top["box"][2]) <= 1.5 * mh \
                    and other["box"][1] - group[-1]["box"][1] <= 0.5 * h:
                group.append(other)
        if len(group) < 2:
            continue
        x0, x1 = int(top["box"][0]), int(top["box"][2])

        def band(ya, yb):
            """(rows, rows with three or more separate pieces of text, long lines) between two heights"""
            inside = [fl for fl in lines if ya <= (fl["box"][1] + fl["box"][3]) / 2 <= yb
                      and x0 - mh <= (fl["box"][0] + fl["box"][2]) / 2 <= x1 + mh]
            rows = {}
            for fl in inside:
                rows.setdefault(int(round((fl["box"][1] + fl["box"][3]) / 2 / (0.6 * mh))), []).append(fl)
            merged = []
            for key in sorted(rows):                    # neighbouring bins are one row
                if merged and key - merged[-1][0] <= 1:
                    merged[-1] = (key, merged[-1][1] + rows[key])
                else:
                    merged.append((key, list(rows[key])))
            return len(merged), sum(1 for _, r in merged if len(r) >= 3), \
                sum(1 for fl in inside if fl["box"][2] - fl["box"][0] >= 0.6 * (x1 - x0))

        # a rule above the table proper (under the page's running head, with the table's title below it)
        # is not the table's: start at the first rule that has columns right under it
        while len(group) >= 3 and band(group[0]["box"][1], group[1]["box"][3])[1] == 0:
            group = group[1:]
        while len(group) >= 3 and band(group[-2]["box"][1], group[-1]["box"][3])[1] == 0:
            group = group[:-1]
        top = group[0]
        if id(top) in used:
            continue                                    # the table this rule opens has been found already
        best = None
        for last in group[1:]:                          # the lowest rule that still closes a stretch of columns
            y0, y1 = int(top["box"][1]), int(last["box"][3])
            n_rows, wide, long_text = band(y0, y1)
            if wide >= 2 and wide >= 0.4 * n_rows and long_text <= 0.25 * n_rows:
                best = (max(0, x0 - 2), max(0, y0 - 3), min(w, x1 + 2), min(h, y1 + 3), [id(g) for g in group if g["box"][1] <= last["box"][1]])
        if best:
            out.append(best[:4])
            used.update(best[4])
    return out


def _gather_drawings(figs, ruled, rest, lines, mh, w, h, fixed):
    """A drawing - a single-line diagram, a flowchart - is line work, small shapes and labels, with white
    space between them. Found piece by piece it comes out as a dozen scraps with its labels set as loose
    text all round. Here the pieces are gathered: line work is added, pieces close to one another are
    joined, and the short labels in among them are taken into the picture."""
    # line work (upright lines, boxes, arrows' shafts) as pieces of its own
    k = int(max(5, 0.9 * mh)) | 1
    work = cv2.dilate(ruled.astype(np.uint8), np.ones((k, k), np.uint8))
    n, lab, stats, _ = cv2.connectedComponentsWithStats(work, connectivity=8)
    pieces = [list(f) + [False] for f in figs]
    for i in range(1, n):
        x, y, cw, ch = (int(v) for v in stats[i, :4])
        if ch < 2.0 * mh:
            continue                                    # a rule across: text furniture, not a drawing
        if cw >= 0.6 * w and ch >= 0.6 * h:
            continue                                    # a frame round the page
        pieces.append([x, y, x + cw, y + ch, True])
    if not pieces:
        return figs
    def near(a, b, gap):
        return a[0] - gap < b[2] and b[0] - gap < a[2] and a[1] - gap < b[3] and b[1] - gap < a[3]
    # join what lies close together, as long as line work is involved (two photographs side by side stay two)
    changed = True
    while changed:
        changed = False
        for a in pieces:
            for b in pieces:
                if a is b:
                    continue
                gap = 2.2 * mh if (a[4] or b[4]) else 0
                if near(a, b, gap):
                    a[0], a[1], a[2], a[3], a[4] = min(a[0], b[0]), min(a[1], b[1]), max(a[2], b[2]), max(a[3], b[3]), a[4] or b[4]
                    pieces.remove(b)
                    changed = True
                    break
            if changed:
                break
        # labels: short text right by a drawing of some size belongs to it
        for a in pieces:
            if not a[4] or a[3] - a[1] < 5 * mh or a[2] - a[0] < 5 * mh:
                continue
            for fl in lines:
                if fl.get("_in"):
                    continue
                x0, y0, x1, y1 = fl["box"]
                if _is_caption(fl) or x1 - x0 > 0.45 * (a[2] - a[0]) and x1 - x0 > 14 * mh:
                    continue
                if near(a, (x0, y0, x1, y1), 1.3 * mh) and not (a[0] <= x0 and x1 <= a[2] and a[1] <= y0 and y1 <= a[3]):
                    # only a label if most of it lies beside or inside the drawing's own extent
                    if (x0 >= a[0] - 6 * mh and x1 <= a[2] + 6 * mh):
                        a[0], a[1], a[2], a[3] = int(min(a[0], x0 - 2)), int(min(a[1], y0 - 2)), int(max(a[2], x1 + 2)), int(max(a[3], y1 + 2))
                        changed = True
    out = []
    for a in pieces:
        if a[4] and (a[3] - a[1] < 3 * mh or a[2] - a[0] < 3 * mh):
            continue                                    # line work alone and small: a bracket, a tick - left out as before
        out.append([max(0, a[0] - 2), max(0, a[1] - 2), min(w, a[2] + 2), min(h, a[3] + 2)])
    return out


def _layout_page(rgb, flines):
    """Work out what is on a page: ruled tables, pictures (figures, plots, photos, anything that is not
    recognised text), stand-alone rules, and text gathered into paragraphs.

    Returns a list of blocks, each a dict with "kind" (para | table | figure | rule), "box" (x0, y0, x1, y1
    in pixels) and its content. Figure blocks carry their picture as (bytes, "png" | "jpg")."""
    h, w = rgb.shape[:2]
    lines = [dict(fl) for fl in flines if fl["text"].strip()]
    # A formula is not text that OCR can read: a line with an equals sign or other mathematics in it,
    # most of which could not be confirmed, is kept as a picture (with whatever is drawn round it).
    formulas = [fl for fl in lines if _looks_like_formula(fl)]
    lines = [fl for fl in lines if not _looks_like_formula(fl)]
    mh = float(np.median([fl["box"][3] - fl["box"][1] for fl in lines])) if lines else max(12.0, h / 80)
    # the rest of a formula: the reader often hands a formula over in pieces, and only some of them
    # look like mathematics. A short piece on the same line, right beside one that does, is part of it.
    grew = True
    while grew:
        grew = False
        for fl in list(lines):
            x0, y0, x1, y1 = fl["box"]
            if len(fl["text"]) > 45 or (fl.get("ok") and len(fl["text"]) > 12):
                continue
            for fm in formulas:
                a0, b0, a1, b1 = fm["box"]
                if min(y1, b1) - max(y0, b0) >= 0.4 * min(y1 - y0, b1 - b0) and max(x0, a0) - min(x1, a1) <= 2.0 * mh:
                    formulas.append(fl)
                    lines.remove(fl)
                    grew = True
                    break
    sure = [fl["size"] for fl in lines if fl["family"]]
    if sure:                                        # a guessed size may not stray far from the measured ones
        typical = float(np.median(sure))
        for fl in lines:
            if not fl["family"]:
                fl["size"] = float(np.clip(fl["size"], 0.7 * typical, 1.5 * typical))
    step = max(1, min(h, w) // 400)
    paper = np.median(rgb[::step, ::step].reshape(-1, 3), axis=0)
    diff = np.abs(rgb.astype(np.int16) - paper.astype(np.int16)).max(axis=2)
    dark = (diff > 60).astype(np.uint8)
    blocks = []

    # --- rules: long straight runs of ink; a grid of them is a table
    hk, vk = int(max(40, 3.0 * mh)), int(max(40, 2.4 * mh))
    hm = cv2.morphologyEx(dark, cv2.MORPH_OPEN, np.ones((1, hk), np.uint8))
    vm = cv2.morphologyEx(dark, cv2.MORPH_OPEN, np.ones((vk, 1), np.uint8))
    n, lab, stats, _ = cv2.connectedComponentsWithStats(((hm | vm) > 0).astype(np.uint8), connectivity=8)
    taken = np.zeros((h, w), bool)                  # pixels that belong to a table or a rule
    ruled = np.zeros((h, w), bool)                  # ... those of stand-alone rules and unclaimed line work
    boxes_fig = []
    for fl in formulas:
        x0, y0, x1, y1 = fl["box"]
        pad = 0.5 * (y1 - y0)
        boxes_fig.append((int(max(0, x0 - pad)), int(max(0, y0 - pad)), int(min(w, x1 + pad)), int(min(h, y1 + pad))))
    # ink that is neither recognised text nor a straight rule: what a picture is made of
    nontext = (diff > 22) & ~cv2.dilate(hm | vm, np.ones((7, 7), np.uint8)).astype(bool)
    for fl in lines:
        x0, y0, x1, y1 = (int(v) for v in fl["box"])
        nontext[max(0, y0 - 3):y1 + 3, max(0, x0 - 3):x1 + 3] = False

    def hollow(x, y, cw, ch):
        """Nothing but text inside this box, away from its edges: a border or a text box, not a picture."""
        mx, my = max(4, int(0.06 * cw)), max(4, int(0.06 * ch))
        inner = nontext[y + my:y + ch - my, x + mx:x + cw - mx]
        return inner.size > 0 and float(inner.mean()) < 0.004

    def page_sized(cw, ch):
        return cw >= 0.6 * w and ch >= 0.6 * h

    def at_edge(x0, y0, x1, y1):
        """Long and thin along the very edge of the page: a scanner shadow, a viewer's frame - not content."""
        return ((y1 <= 0.035 * h or y0 >= 0.965 * h) and x1 - x0 >= 0.5 * w) or \
               ((x1 <= 0.045 * w or x0 >= 0.955 * w) and y1 - y0 >= 0.5 * h)

    frames = []
    for i in range(1, n):
        x, y, cw, ch = (int(v) for v in stats[i, :4])
        part = lab[y:y + ch, x:x + cw] == i
        rows = _clusters(np.flatnonzero((hm[y:y + ch, x:x + cw] > 0)[:, :].astype(bool).__and__(part).sum(axis=1) >= 0.5 * cw), 3)
        cols = _clusters(np.flatnonzero((vm[y:y + ch, x:x + cw] > 0).astype(bool).__and__(part).sum(axis=0) >= 0.5 * ch), 3)
        framed = _framed_table(hm[y:y + ch, x:x + cw].astype(bool) & part, vm[y:y + ch, x:x + cw].astype(bool) & part, hk, vk) \
            if cw >= 6 * mh and ch >= 2 * mh else None
        if framed == "drawing":
            boxes_fig.append((x, y, x + cw, y + ch))     # boxes and lines that are no table: a drawing
            continue
        if framed == "box":
            frames.append((x, y, x + cw, y + ch))
            framed = None
        if framed:
            ys, xs = [y + r for r in framed["ys"]], [x + c for c in framed["xs"]]
            cells = [[[] for _ in xs[:-1]] for _ in ys[:-1]]
            inside = []
            for fl in lines:
                cx, cy = (fl["box"][0] + fl["box"][2]) / 2, (fl["box"][1] + fl["box"][3]) / 2
                if xs[0] < cx < xs[-1] and ys[0] < cy < ys[-1]:
                    r = min(len(ys) - 2, max(0, int(np.searchsorted(ys, cy)) - 1))
                    c = min(len(xs) - 2, max(0, int(np.searchsorted(xs, cx)) - 1))
                    r, c = framed["covered"].get((r, c), (r, c))
                    cells[r][c].append(fl)
                    inside.append(fl)
            if inside:
                fills = [[None] * (len(xs) - 1) for _ in ys[:-1]]
                pics = {}
                good = [fl for fl in inside if fl["family"]]
                fam = max(set(f["family"] for f in good), key=[f["family"] for f in good].count) if good else None
                for (r, c), (rs, cs) in framed["span"].items():
                    cy0, cy1, cx0, cx1 = int(ys[r]) + 3, int(ys[r + rs]) - 2, int(xs[c]) + 3, int(xs[c + cs]) - 2
                    patch = rgb[cy0:cy1, cx0:cx1]
                    col = np.median(patch.reshape(-1, 3), axis=0) if patch.size else paper
                    fills[r][c] = tuple(int(v) for v in col) if np.abs(col - paper).max() > 10 else None
                    if not patch.size or cy1 - cy0 < 5 or cx1 - cx0 < 5:
                        continue
                    # Is everything in this cell text that was read and confirmed? Ink that no line of text
                    # accounts for (a tick box, a word the reader missed), or a line mostly unconfirmed,
                    # and the cell is kept as a picture: exactly what the page shows, in the right place.
                    ink = np.abs(patch.astype(np.int16) - col.astype(np.int16)).max(axis=2) > 60
                    for fl in cells[r][c]:
                        bx0, by0, bx1, by1 = (int(v) for v in fl["box"])
                        ink[max(0, by0 - 3 - cy0):max(0, by1 + 3 - cy0), max(0, bx0 - 3 - cx0):max(0, bx1 + 3 - cx0)] = False
                    stray = int(cv2.morphologyEx(ink.astype(np.uint8), cv2.MORPH_OPEN, np.ones((2, 2), np.uint8)).sum())
                    doubt = any(_unsure_share(fl) >= 0.5 for fl in cells[r][c])
                    for fa in cells[r][c]:                  # two pieces of text side by side in one cell: columns
                        for fb in cells[r][c]:              # inside it, which a cell of text cannot show
                            if fb["box"][0] - fa["box"][2] > 1.5 * mh and \
                                    min(fa["box"][3], fb["box"][3]) - max(fa["box"][1], fb["box"][1]) > 0.5 * (fa["box"][3] - fa["box"][1]):
                                doubt = True
                    if stray >= max(12.0, (0.45 * mh) ** 2) or doubt:
                        pics[(r, c)] = {"kind": "figure", "box": (cx0, cy0, cx1, cy1), "image": _encode_picture(patch)}
                    else:
                        for fl in cells[r][c]:              # a line with no font of its own takes the table's
                            if not fl["family"] and fam:
                                fl["family"] = fam
                rule = np.median(rgb[y:y + ch, x:x + cw][part], axis=0)
                blocks.append({"kind": "table", "box": (xs[0], ys[0], xs[-1], ys[-1]), "xs": xs, "ys": ys, "cells": cells,
                               "fills": fills, "rule": tuple(int(v) for v in rule), "span": framed["span"],
                               "covered": framed["covered"], "pics": pics})
                pad = int(max(6, 0.6 * mh))             # ... with its frame, however faint that is in places
                taken[max(0, y - pad):y + ch + pad, max(0, x - pad):x + cw + pad] = True
                ids = {id(fl) for fl in inside}
                lines = [fl for fl in lines if id(fl) not in ids]
                continue
        if len(rows) >= 2 and len(cols) >= 2:
            ys, xs = [y + r for r in rows], [x + c for c in cols]
            cells = [[[] for _ in xs[:-1]] for _ in ys[:-1]]
            inside = []
            for fl in lines:
                cx, cy = (fl["box"][0] + fl["box"][2]) / 2, (fl["box"][1] + fl["box"][3]) / 2
                if xs[0] < cx < xs[-1] and ys[0] < cy < ys[-1]:
                    r = int(np.searchsorted(ys, cy)) - 1
                    c = int(np.searchsorted(xs, cx)) - 1
                    cells[r][c].append(fl)
                    inside.append(fl)
            ncell = (len(ys) - 1) * (len(xs) - 1)
            filled = sum(bool(cell) for row in cells for cell in row)
            if page_sized(cw, ch) and ncell == 1 and hollow(x, y, cw, ch):
                taken[y:y + ch, x:x + cw] |= cv2.dilate(part.astype(np.uint8), np.ones((5, 5), np.uint8)).astype(bool)
                continue                            # a border drawn round the page: not a table, not a picture
            if (ncell >= 2 or (inside and hollow(x, y, cw, ch))) and filled >= 0.3 * ncell:
                fills = []
                for r in range(len(ys) - 1):
                    fills.append([])
                    for c in range(len(xs) - 1):
                        patch = rgb[int(ys[r]) + 3:int(ys[r + 1]) - 2, int(xs[c]) + 3:int(xs[c + 1]) - 2]
                        col = np.median(patch.reshape(-1, 3), axis=0) if patch.size else paper
                        fills[-1].append(tuple(int(v) for v in col) if np.abs(col - paper).max() > 10 else None)
                rule = np.median(rgb[y:y + ch, x:x + cw][part], axis=0)
                blocks.append({"kind": "table", "box": (xs[0], ys[0], xs[-1], ys[-1]), "xs": xs, "ys": ys, "cells": cells,
                               "fills": fills, "rule": tuple(int(v) for v in rule)})
                taken[y:y + ch, x:x + cw] = True
                ids = {id(fl) for fl in inside}
                lines = [fl for fl in lines if id(fl) not in ids]
                continue
            boxes_fig.append((x, y, x + cw, y + ch))          # a frame with something else in it: a figure
        elif at_edge(x, y, x + cw, y + ch):
            taken[y:y + ch, x:x + cw] |= cv2.dilate(part.astype(np.uint8), np.ones((5, 5), np.uint8)).astype(bool)
        elif len(rows) == 1 and len(cols) == 0 and cw >= 4 * mh:
            ry = y + rows[0]
            blocks.append({"kind": "rule", "box": (x, ry - 1, x + cw, ry + 1),
                           "colour": tuple(int(v) for v in np.median(rgb[y:y + ch, x:x + cw][part], axis=0)),
                           "weight": float(max(1, ch))})
            taken[y:y + ch, x:x + cw] = True
            ruled[y:y + ch, x:x + cw] |= part
        else:
            ruled[y:y + ch, x:x + cw] |= part           # upright lines, corners, crossings: line work of a drawing

    # --- a frame with rules to write on inside it: a form. Set as text its blanks and tick boxes scatter;
    # it is kept whole, as a picture.
    # (a frame whose sides are too faint to count as rules: a rule above, the same rule below, and pale
    # ink all the way down both ends between them)
    pale = diff > 22
    across = sorted((b for b in blocks if b["kind"] == "rule" and b["box"][2] - b["box"][0] >= 10 * mh), key=lambda b: b["box"][1])
    for i, top in enumerate(across):
        for bottom in across[i + 1:]:
            x0, x1 = int(top["box"][0]), int(top["box"][2])
            y0, y1 = int(top["box"][1]), int(bottom["box"][3])
            if abs(bottom["box"][0] - x0) > 0.5 * mh or abs(bottom["box"][2] - x1) > 0.5 * mh or y1 - y0 < 4 * mh:
                continue
            sides = [float(pale[y0:y1, max(0, x - 8):x + 9].any(axis=1).mean()) for x in (x0, x1)]
            if min(sides) >= 0.9:
                frames.append((max(0, x0 - 8), y0, min(w, x1 + 9), y1))
                taken[y0:y1, max(0, x0 - 9):x0 + 10] = True      # the sides are the frame's, not pictures of their own
                taken[y0:y1, max(0, x1 - 9):x1 + 10] = True
                break
    for fx0, fy0, fx1, fy1 in frames:
        if fx1 - fx0 >= 0.85 * w and fy1 - fy0 >= 0.85 * h:
            continue                                # a border round the page
        blanks = [b for b in blocks if b["kind"] == "rule" and fx0 <= (b["box"][0] + b["box"][2]) / 2 <= fx1
                  and fy0 <= (b["box"][1] + b["box"][3]) / 2 <= fy1]
        if len(blanks) < 3:
            continue
        boxes_fig.append((max(0, fx0 - 2), max(0, fy0 - 2), min(w, fx1 + 2), min(h, fy1 + 2)))
        gone = {id(b) for b in blanks}
        for b in blocks:                            # ... and anything made of it so far goes back into it
            if b["kind"] == "table" and fx0 - 4 <= b["box"][0] and b["box"][2] <= fx1 + 4 and fy0 - 4 <= b["box"][1] and b["box"][3] <= fy1 + 4:
                gone.add(id(b))
                lines += [fl for row in b["cells"] for cell in row for fl in cell]
        blocks = [b for b in blocks if id(b) not in gone]
        taken[fy0:fy1, fx0:fx1] = False

    # --- tables with rules across but none down: columns kept apart by space alone. Rebuilt as text they
    # come out as a scatter of numbers; the stretch between the top and bottom rule is kept as a picture.
    for box in _open_tables(blocks, lines, mh, w, h):
        blocks = [b for b in blocks if not (b["kind"] == "rule" and box[1] - 2 <= (b["box"][1] + b["box"][3]) / 2 <= box[3] + 2
                                            and box[0] - mh <= b["box"][0] and b["box"][2] <= box[2] + mh)]
        # a picture in its own right, there and then: nothing else on the page may grow into it
        blocks.append({"kind": "figure", "box": box, "image": _encode_picture(rgb[box[1]:box[3], box[0]:box[2]])})
        lines = [fl for fl in lines if not (box[1] <= (fl["box"][1] + fl["box"][3]) / 2 <= box[3]
                                            and box[0] - mh <= (fl["box"][0] + fl["box"][2]) / 2 <= box[2] + mh)]
        taken[box[1]:box[3], box[0]:box[2]] = True

    lines = _join_same_row(lines, mh)

    # --- pictures: whatever ink is left once text, tables and rules are set aside
    rest = (diff > 22) & ~taken
    for fl in lines:
        x0, y0, x1, y1 = (int(v) for v in fl["box"])
        rest[max(0, y0 - 3):y1 + 3, max(0, x0 - 3):x1 + 3] = False
    rest = cv2.morphologyEx(rest.astype(np.uint8), cv2.MORPH_OPEN, np.ones((2, 2), np.uint8))
    k = int(max(5, 0.9 * mh)) | 1
    merged = cv2.dilate(rest, np.ones((k, k), np.uint8))
    for x0, y0, x1, y1 in boxes_fig:
        merged[y0:y1, x0:x1] = 1
    n, lab, stats, _ = cv2.connectedComponentsWithStats(merged, connectivity=8)
    figs = []
    for i in range(1, n):
        x, y, cw, ch = (int(v) for v in stats[i, :4])
        if int(rest[y:y + ch, x:x + cw].sum()) < (0.6 * mh) ** 2 and (x, y, x + cw, y + ch) not in boxes_fig:
            continue                                # a speck
        if at_edge(x, y, x + cw, y + ch):
            continue
        if page_sized(cw, ch):
            # as big as the page: a real picture has ink of its own in its middle; page edges, margin
            # lines and a frame round the page do not (whatever else is on the page inside them)
            mx, my = max(4, int(0.06 * cw)), max(4, int(0.06 * ch))
            own = (lab[y + my:y + ch - my, x + mx:x + cw - mx] == i) & (rest[y + my:y + ch - my, x + mx:x + cw - mx] > 0)
            if own.size and float(own.mean()) < 0.004:
                continue
        figs.append([max(0, x - 2), max(0, y - 2), min(w, x + cw + 2), min(h, y + ch + 2)])
    figs = _gather_drawings(figs, ruled, rest, lines, mh, w, h, boxes_fig)
    blocks = [b for b in blocks if not (b["kind"] == "rule" and any(
        f[0] - 2 <= (b["box"][0] + b["box"][2]) / 2 <= f[2] + 2 and f[1] - 2 <= (b["box"][1] + b["box"][3]) / 2 <= f[3] + 2
        and f[3] - f[1] >= 3 * mh for f in figs))]
    changed = True
    while changed:                                  # text sitting in a picture belongs to the picture
        changed = False
        for f in figs:
            for fl in list(lines):
                cx, cy = (fl["box"][0] + fl["box"][2]) / 2, (fl["box"][1] + fl["box"][3]) / 2
                if _is_caption(fl) and not (f[1] + 0.2 * (f[3] - f[1]) <= cy <= f[3] - 0.2 * (f[3] - f[1])):
                    continue                        # "FIGURE D.2 ...": the picture's caption, not part of it
                if f[0] <= cx <= f[2] and f[1] <= cy <= f[3]:
                    f[0], f[1] = min(f[0], int(fl["box"][0]) - 2), min(f[1], int(fl["box"][1]) - 2)
                    f[2], f[3] = max(f[2], int(fl["box"][2]) + 2), max(f[3], int(fl["box"][3]) + 2)
                    lines.remove(fl)
                    changed = True
        for a in figs:
            for b in figs:
                if a is not b and a[0] < b[2] and b[0] < a[2] and a[1] < b[3] and b[1] < a[3]:
                    a[0], a[1], a[2], a[3] = min(a[0], b[0]), min(a[1], b[1]), max(a[2], b[2]), max(a[3], b[3])
                    figs.remove(b)
                    changed = True
                    break
            if changed:
                break
    tables = [b["box"] for b in blocks if b["kind"] == "table"]
    for x0, y0, x1, y1 in figs:
        x0, y0, x1, y1 = max(0, x0), max(0, y0), min(w, x1), min(h, y1)
        if any(t[0] <= (x0 + x1) / 2 <= t[2] and t[1] <= (y0 + y1) / 2 <= t[3]
               and (x1 - x0) * (y1 - y0) < 0.8 * (t[2] - t[0]) * (t[3] - t[1]) for t in tables):
            continue                                # a drawing in a table cell: the cell shows it already
        if y1 - y0 < 2.5 * mh and (x0, y0, x1, y1) not in boxes_fig:
            # a scrap no taller than a couple of lines, lying in among the text (a word the reader
            # missed, a smudge): as a picture it would be given a line of its own and push the text
            # below it down - it is left out
            near = sum(1 for fl in lines if fl["box"][1] - 1.5 * mh <= (y0 + y1) / 2 <= fl["box"][3] + 1.5 * mh
                       and fl["box"][0] - 2 * mh <= x1 and x0 <= fl["box"][2] + 2 * mh)
            if near >= 2:
                continue
        if x1 - x0 >= 4 and y1 - y0 >= 4:
            blocks.append({"kind": "figure", "box": (x0, y0, x1, y1), "image": _encode_picture(rgb[y0:y1, x0:x1])})

    # --- text: lines that continue one another become a paragraph
    blocks += _set_alignment(_paragraphs(lines))
    return blocks


def _set_alignment(paras, bounds=None):
    """Say of each paragraph whether it is set to the left, centred or to the right of the column it stands
    in (justified is known already): b["align"] and, for the two that are not the left, b["col"] - the
    edges it was measured from. bounds: the edges of a table cell; without it the columns are found from
    the page's own paragraphs. Returns paras.

    Centred: every line has the same room on its left as on its right, and stands clear of both edges.
    To the right: every line ends on the right edge and starts well short of the left."""
    paras = [b for b in paras if b.get("kind") == "para"]
    for b in paras:
        b["align"] = "left"
    if not paras:
        return paras
    cols = []
    if bounds is None:
        x0, x1 = min(b["box"][0] for b in paras), max(b["box"][2] for b in paras)
        for b in paras:                                 # the columns: where the text of some length stands
            if len(b["lines"]) >= 2 and b["box"][2] - b["box"][0] >= 12 * b["size"]:
                tol = 0.8 * b["size"]
                for c in cols:
                    if abs(c[0] - b["box"][0]) <= tol and abs(c[1] - b["box"][2]) <= tol:
                        c[0], c[1], c[2] = min(c[0], b["box"][0]), max(c[1], b["box"][2]), c[2] + len(b["lines"])
                        break
                else:
                    cols.append([b["box"][0], b["box"][2], len(b["lines"])])
        most = max((c[2] for c in cols), default=0)
        cols = [c for c in cols if c[2] >= max(3, 0.15 * most)]
        every = sum(len(b["lines"]) for b in paras)
        if not cols or sum(c[2] for c in cols) < 0.5 * every:
            return paras                                # nothing to measure from: an index, a page of scraps
        cols = [(c[0], c[1]) for c in cols] + [(x0, x1)]
    else:
        cols = [(float(bounds[0]), float(bounds[1]))]
    for b in paras:
        size, lines = b["size"], b["lines"]
        text = " ".join(fl["text"] for fl in lines).strip()
        if len(lines) > 3 or b.get("justified") or _starts_item(lines[0]) or _ITEM_START.match(text) or not text:
            continue
        slack = 0.8 * size
        inside = [c for c in cols if c[0] - slack <= b["box"][0] and b["box"][2] <= c[1] + slack]
        if not inside:
            continue
        c0, c1 = min(inside, key=lambda c: c[1] - c[0])
        wide = c1 - c0
        # alone on its rows, between those edges: a piece of a line whose other piece is a block of its
        # own, or an entry in the middle one of three columns, is neither centred nor set to the right
        y0, y1 = b["box"][1] + 0.25 * size, b["box"][3] - 0.25 * size
        if any(o is not b and o["box"][1] < y1 and y0 < o["box"][3] and o["box"][0] < c1 and c0 < o["box"][2] for o in paras):
            continue
        if text.endswith("-") or sum(ch.isalnum() for ch in text) < 2:
            continue
        lm = [fl["box"][0] - c0 for fl in lines]
        rm = [c1 - fl["box"][2] for fl in lines]
        clear = 1.2 * size if bounds is not None else 1.5 * size
        if min(lm) >= clear and all(abs(l - r) <= 0.7 * size + 0.02 * wide for l, r in zip(lm, rm)):
            b["align"], b["col"] = "center", (c0, c1)
        elif max(abs(r) for r in rm) <= (1.0 if bounds is not None else 0.6) * size and \
                min(lm) >= max((2.0 if bounds is not None else 3.0) * size, 0.0 if bounds is not None else 0.3 * wide) \
                and (len(lines) == 1 or max(lm) - min(lm) > size):
            b["align"], b["col"] = "right", (c0, c1)
    if os.environ.get("SNAPCLEAN_DEBUG_ALIGN"):
        for b in paras:
            if b["align"] != "left":
                print("ALIGN", "cell" if bounds is not None else "page", b["align"], repr(" ".join(fl["text"] for fl in b["lines"])[:60]))
    return paras


def _paragraphs(lines):
    """Gather text lines into paragraph blocks.

    A line continues the one above when it is the same size, at an even line spacing, and starts at the
    paragraph's left edge. The FIRST line of a paragraph may start somewhere else - indented, or (a
    numbered item) hanging out to the left; that is recorded as the paragraph's "first" and "body" edges.
    A line that stops short of the right edge ends its paragraph."""
    lines = sorted(lines, key=lambda fl: (fl["base"], fl["box"][0]))
    groups = []
    for fl in lines:
        size = fl["size"]
        best = None
        for g in ([] if _starts_item(fl) else groups):  # a list item is always the start of something
            last = g[-1]
            gap = fl["base"] - last["base"]
            body = g[1]["box"][0] if len(g) >= 2 else None
            edge_ok = abs(fl["box"][0] - body) <= 0.7 * size if body is not None else \
                abs(fl["box"][0] - g[0]["box"][0]) <= 4.0 * size
            if (edge_ok and abs(last["size"] / size - 1) <= 0.12
                    and 0.9 * size <= gap <= 1.9 * size and fl["box"][0] < last["box"][2] and last["box"][0] < fl["box"][2]
                    and (len(g) < 2 or abs(gap - (g[-1]["base"] - g[-2]["base"])) <= 0.25 * size)
                    and (last["family"] == fl["family"] or not last["family"] or not fl["family"])):
                best = g
        if best is not None:
            best.append(fl)
        else:
            groups.append([fl])
    every_right = [fl["box"][2] for fl in lines]
    out = []
    for g in groups:
        right = max(fl["box"][2] for fl in g)
        width = right - min(fl["box"][0] for fl in g)
        start = 0
        for i, fl in enumerate(g):                  # a short line ends its paragraph
            ends = i == len(g) - 1 or fl["box"][2] < right - 0.2 * width
            # ... and so does a line all in bold above one that is not (a heading set close to its text)
            if not ends and i == start and fl["bold"] and not g[i + 1]["bold"] and not fl.get("styles") \
                    and abs(fl["box"][0] - g[i + 1]["box"][0]) <= 0.7 * fl["size"]:
                ends = True
            if ends:
                part = g[start:i + 1]
                start = i + 1
                known = [p for p in part if p["family"]] or part
                lead = max(known, key=lambda p: len(p["text"]))
                pitch = float(np.median(np.diff([p["base"] for p in part]))) if len(part) > 1 else 0.0
                rights = [p["box"][2] for p in part[:-1]]
                tol = 0.45 * lead["size"]
                # justified: every line but the last ends on an edge that several lines of the page end on
                on_edge = [sum(abs(r - e) <= tol for e in every_right) >= 3 for r in rights]
                edge = float(np.median([r for r, ok in zip(rights, on_edge) if ok])) if any(on_edge) else 0.0
                level = [ok and abs(r - edge) <= tol for r, ok in zip(rights, on_edge)]
                # (one line in a long paragraph may fall short: a word at its end that was not read)
                justified = bool(rights) and sum(level) >= max(1, math.ceil(0.8 * len(rights)))
                first = part[0]["box"][0]
                body = float(np.median([p["box"][0] for p in part[1:]])) if len(part) > 1 else first
                out.append({"kind": "para", "lines": part, "family": lead["family"], "bold": lead["bold"],
                            "italic": lead["italic"], "size": float(np.median([p["size"] for p in known])),
                            "pitch": pitch, "colour": lead["colour"], "justified": justified,
                            "first": float(first), "body": float(body),
                            "box": (min(p["box"][0] for p in part), min(p["box"][1] for p in part),
                                    max(p["box"][2] for p in part), max(p["box"][3] for p in part))})
    return out


class _DocxFlow:
    """A Word file made of ordinary paragraphs, real tables and inline pictures, laid out to follow the
    original pages: same page size, same fonts and sizes, each block at about the place it was."""

    def __init__(self, path, highlight=True, keep_lines=True):
        import zipfile
        self.zip = zipfile.ZipFile(str(path), "w", zipfile.ZIP_DEFLATED)
        self.body, self.rels, self.media, self.shape = [], [], 0, 0
        self.highlight = highlight
        self.keep_lines = keep_lines    # every line ends where it did in the original
        self.sect = None
        self.default_font = "Arial"

    # -- pieces
    def _rpr(self, family, bold, italic, size_pt, colour, mark=False, squeeze=100):
        font = _xml(family or self.default_font)
        r, g, b = (int(c) for c in colour)
        if r > 200 and g > 200 and b > 200:            # near-white text would vanish off its background
            r = g = b = 0
        half = max(2, int(round(size_pt * 2)))
        return (f'<w:rPr><w:rFonts w:ascii="{font}" w:hAnsi="{font}" w:cs="{font}" w:eastAsia="{font}"/>'
                + ('<w:b/><w:bCs/>' if bold else '') + ('<w:i/><w:iCs/>' if italic else '')
                + f'<w:color w:val="{r:02X}{g:02X}{b:02X}"/>' + (f'<w:w w:val="{int(squeeze)}"/>' if squeeze != 100 else '')
                + f'<w:sz w:val="{half}"/><w:szCs w:val="{half}"/>'
                + ('<w:highlight w:val="yellow"/>' if mark and self.highlight else '') + '</w:rPr>')

    def _para(self, b, k, before, left, right, in_cell=False):
        size = b["size"] * k
        half = max(2, int(round(size * 2)))             # Word sets type in half points: what it will really use
        line = b["pitch"] * k if b["pitch"] > 0 else 1.22 * size
        plain = (b["family"], b["bold"], b["italic"])
        keep = self.keep_lines
        body_x, first_x = b.get("body", b["box"][0]), b.get("first", b["box"][0])
        one = b["lines"][0]
        if len(b["lines"]) == 1 and _starts_item(one) and one.get("xs") and len(one["xs"]) == len(one["text"].split()):
            body_x, first_x = float(one["xs"][1]), float(one["box"][0])       # "(4)", a tab, then the text where it stands
        left = left + max(0.0, (body_x - b["box"][0]) * k)
        first = (first_x - body_x) * k                  # > 0: first line indented; < 0: hanging out to the left
        hanging = first < -0.5 * size
        runs, text, flag, last = [], "", None, ""

        def flush():
            nonlocal text, flag
            if text and flag is not None:
                runs.append((text, flag))
            text, flag = "", None

        for li, fl in enumerate(b["lines"]):
            words = fl["text"].split()
            oks = fl["oks"] if fl.get("oks") and len(fl["oks"]) == len(words) else [bool(fl["ok"])] * len(words)
            looks = fl["styles"] if fl.get("styles") and len(fl["styles"]) == len(words) else [None] * len(words)
            pics = fl.get("pics") or {}
            # a line's own style (a bold line in a paragraph that is mostly not)
            mine = (fl["family"], fl["bold"], fl["italic"]) if fl.get("family") else plain
            mine = plain if mine == plain else mine
            # Lines end where they did. A line that would come out wider than its place - the font here
            # is never quite the original's - has its letters drawn a few per cent narrower, so it fits
            # and nothing runs on to an extra line.
            squeeze = 100
            if keep and fl.get("natural") and fl.get("nsize"):
                natural = fl["natural"] / fl["nsize"] * (half / 2.0)
                room = (fl["box"][2] - fl["box"][0]) * k
                # (a justified line is aimed a little short: its spaces are stretched to the edge anyway,
                # and a line that is a hair too long would wrap and push everything below it down)
                aim = 0.96 if b.get("justified") and li < len(b["lines"]) - 1 else 0.985
                if natural > aim * room:
                    squeeze = int(max(66, min(100, math.floor(100.0 * aim * room / natural))))
            xs = fl.get("xs") if fl.get("xs") and len(fl["xs"]) == len(words) else None
            for wi, (word, ok, look) in enumerate(zip(words, oks, looks)):
                key = (ok, tuple(look) if look and tuple(look) != plain else mine, squeeze)
                glue = " " if last else ""
                if wi == 0 and li > 0:
                    if keep:
                        glue = "\n"
                    elif last.endswith("-") and word[:1].islower():
                        glue = ""
                        if text.endswith("-") and known_word(_core(last[:-1] + word)[1]):
                            text = text[:-1]             # "protec-" + "tive" run together again: protective
                if wi == 1 and li == 0 and hanging and xs and abs(xs[1] - body_x) <= 0.8 * b["size"]:
                    glue = "\t"                         # "(1)", then the text at the paragraph's own edge
                if not ok and wi in pics:               # an unidentified word, shown as its own picture
                    text += glue
                    if text and flag is None:
                        flag = (True, mine, squeeze)
                    flush()
                    scale = b["size"] / max(float(fl.get("size") or b["size"]), 1e-3)
                    runs.append((pics[wi], ("picture", min(1.25, max(0.8, scale)), 100)))
                    last = word
                    continue
                if flag is not None and key != flag:
                    if glue.strip(" ") == "" and (key[1] == plain and flag[1] != plain or (ok and not flag[0])):
                        text, glue = text + glue, ""    # keep the space with the marked / styled run
                    flush()
                flag, last = key, word
                text += glue + word
        flush()
        if keep and b.get("justified") and len(b["lines"]) > 1:
            right = max(0.0, right)
        align = b.get("align", "left") if b.get("col") else "left"
        if align != "left":
            # really centred (or set to the right) in Word too, between the edges it was measured from -
            # not held in place by an indent, which would leave it where it is when its words change
            lpt, rpt = max(0.0, (b["box"][0] - b["col"][0]) * k), max(0.0, (b["col"][1] - b["box"][2]) * k)
            if in_cell:
                right = rpt
            if align == "center":
                give = max(0.0, min(lpt, rpt, left, right))
                left, right, first = left - give, right - give, 0.0
            else:
                give = max(0.0, min(lpt, left))
                left, right, first = left - give, max(0.0, min(right, rpt)), 0.0
        ind = (f'<w:ind w:left="{max(0, int(round(left * 20)))}" w:right="{max(0, int(round(right * 20)))}"'
               + (f' w:hanging="{int(round(-first * 20))}"' if first < -0.5 else
                  f' w:firstLine="{int(round(first * 20))}"' if first > 0.5 else '') + '/>')
        ppr = (f'<w:pPr><w:spacing w:before="{max(0, int(round(before * 20)))}" w:after="0" '
               f'w:line="{max(20, int(round(line * 20)))}" w:lineRule="exact"/>' + ind
               + ('<w:jc w:val="both"/>' if b.get("justified") else f'<w:jc w:val="{align}"/>' if align != "left" else '') + '</w:pPr>')

        def typed(t):                                   # text with its line breaks and tabs
            out = []
            for piece in re.split("([\n\t])", t):
                if piece == "\n":
                    out.append('<w:br/>')
                elif piece == "\t":
                    out.append('<w:tab/>')
                elif piece:
                    out.append(f'<w:t xml:space="preserve">{_xml(piece)}</w:t>')
            return "".join(out)

        body = "".join(self._word_pic(t, size * look, line) if ok == "picture" else
                       '<w:r>' + self._rpr(look[0], look[1], look[2], size, b["colour"], mark=not ok, squeeze=sq)
                       + typed(t) + '</w:r>' for t, (ok, look, sq) in runs if t)
        return f'<w:p>{ppr}{body}</w:p>'

    def _word_pic(self, pic, em_pt, line_pt):
        """An inline picture of one word: sized to the paragraph's type and dropped so its baseline is the line's."""
        data, wide, tall, drop = pic
        if (tall - drop) * em_pt > 0.98 * line_pt:      # must fit the line (Word crops what sticks out above it)
            em_pt = 0.98 * line_pt / max(tall - drop, 1e-3)
        if getattr(self, "dry", False):
            return ""
        self.media += 1
        self.shape += 1
        name = f"image{self.media}.png"
        self.zip.writestr("word/media/" + name, data)
        self.rels.append(f'<Relationship Id="rIdI{self.media}" Type="http://schemas.openxmlformats.org/officeDocument/'
                         f'2006/relationships/image" Target="media/{name}"/>')
        cx, cy = int(round(wide * em_pt * 12700)), int(round(tall * em_pt * 12700))
        return (f'<w:r><w:rPr><w:position w:val="{-int(round(drop * em_pt * 2))}"/></w:rPr><w:drawing>'
                f'<wp:inline distT="0" distB="0" distL="0" distR="0"><wp:extent cx="{cx}" cy="{cy}"/>'
                f'<wp:docPr id="{self.shape}" name="Word {self.shape}" descr="a word the program could not identify"/>'
                '<wp:cNvGraphicFramePr/>'
                '<a:graphic><a:graphicData uri="http://schemas.openxmlformats.org/drawingml/2006/picture"><pic:pic>'
                f'<pic:nvPicPr><pic:cNvPr id="{self.shape}" name="{name}"/><pic:cNvPicPr/></pic:nvPicPr>'
                f'<pic:blipFill><a:blip r:embed="rIdI{self.media}"/><a:stretch><a:fillRect/></a:stretch></pic:blipFill>'
                f'<pic:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="{cx}" cy="{cy}"/></a:xfrm>'
                '<a:prstGeom prst="rect"><a:avLst/></a:prstGeom></pic:spPr></pic:pic></a:graphicData></a:graphic>'
                '</wp:inline></w:drawing></w:r>')

    def _spacer(self, pts):
        v = max(20, int(round(pts * 20)))
        return (f'<w:p><w:pPr><w:spacing w:before="0" w:after="0" w:line="{v}" w:lineRule="exact"/>'
                '<w:rPr><w:sz w:val="2"/></w:rPr></w:pPr></w:p>')

    def _figure(self, b, k, before, left, in_cell=False):
        data, ext = b["image"]
        if getattr(self, "dry", False):
            return ""
        self.media += 1
        self.shape += 1
        name = f"image{self.media}.{ext}"
        self.zip.writestr("word/media/" + name, data)
        self.rels.append(f'<Relationship Id="rIdI{self.media}" Type="http://schemas.openxmlformats.org/officeDocument/'
                         f'2006/relationships/image" Target="media/{name}"/>')
        cx = int(round((b["box"][2] - b["box"][0]) * k * 12700))
        cy = int(round((b["box"][3] - b["box"][1]) * k * 12700))
        tallest = getattr(self, "tallest", 0)
        if tallest and cy > tallest:                    # a picture as tall as the page: a touch smaller, or it
            cx, cy = int(cx * tallest / cy), int(tallest)   # spills on to an empty page of its own
        # the line is made exactly as tall as the picture: left to itself, a word processor adds the
        # depth of a line of text under every picture, and a page with several comes out too long
        tall = int(math.ceil(cy / 12700.0 * 20)) + 20
        # ... "at least" a hair, so the line grows to the picture: a line cut to an exact height cuts the
        # top off a picture that stands in a table cell (and in Word, sometimes, anywhere)
        tall, rule = 20, "atLeast"
        return (f'<w:p><w:pPr><w:spacing w:before="{max(0, int(round(before * 20)))}" w:after="0" w:line="{tall}" w:lineRule="{rule}"/>'
                f'<w:ind w:left="{max(0, int(round(left * 20)))}"/><w:rPr><w:sz w:val="2"/></w:rPr></w:pPr>'
                f'<w:r><w:rPr><w:sz w:val="2"/></w:rPr><w:drawing>'
                f'<wp:inline distT="0" distB="0" distL="0" distR="0"><wp:extent cx="{cx}" cy="{cy}"/>'
                f'<wp:docPr id="{self.shape}" name="Picture {self.shape}"/><wp:cNvGraphicFramePr/>'
                '<a:graphic><a:graphicData uri="http://schemas.openxmlformats.org/drawingml/2006/picture"><pic:pic>'
                f'<pic:nvPicPr><pic:cNvPr id="{self.shape}" name="{name}"/><pic:cNvPicPr/></pic:nvPicPr>'
                f'<pic:blipFill><a:blip r:embed="rIdI{self.media}"/><a:stretch><a:fillRect/></a:stretch></pic:blipFill>'
                f'<pic:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="{cx}" cy="{cy}"/></a:xfrm>'
                '<a:prstGeom prst="rect"><a:avLst/></a:prstGeom></pic:spPr></pic:pic></a:graphicData></a:graphic>'
                '</wp:inline></w:drawing></w:r></w:p>')

    def _rule(self, b, k, before, left, right):
        r, g, bl = b["colour"]
        sz = max(2, min(48, int(round(b["weight"] * k * 8))))
        return (f'<w:p><w:pPr><w:pBdr><w:top w:val="single" w:sz="{sz}" w:space="0" w:color="{r:02X}{g:02X}{bl:02X}"/></w:pBdr>'
                f'<w:spacing w:before="{max(0, int(round(before * 20)))}" w:after="0" w:line="40" w:lineRule="exact"/>'
                f'<w:ind w:left="{max(0, int(round(left * 20)))}" w:right="{max(0, int(round(right * 20)))}"/>'
                '<w:rPr><w:sz w:val="2"/></w:rPr></w:pPr></w:p>')

    def _table(self, b, k, left):
        xs, ys = b["xs"], b["ys"]
        widths = [max(20, int(round((xs[i + 1] - xs[i]) * k * 20))) for i in range(len(xs) - 1)]
        r, g, bl = b["rule"]
        edge = f'w:val="single" w:sz="4" w:space="0" w:color="{r:02X}{g:02X}{bl:02X}"'
        out = [f'<w:tbl><w:tblPr><w:tblW w:w="{sum(widths)}" w:type="dxa"/><w:tblInd w:w="{int(round(left * 20))}" w:type="dxa"/>'
               f'<w:tblBorders><w:top {edge}/><w:left {edge}/><w:bottom {edge}/><w:right {edge}/><w:insideH {edge}/>'
               f'<w:insideV {edge}/></w:tblBorders><w:tblLayout w:type="fixed"/><w:tblCellMar><w:top w:w="0" w:type="dxa"/>'
               '<w:left w:w="0" w:type="dxa"/><w:bottom w:w="0" w:type="dxa"/><w:right w:w="0" w:type="dxa"/></w:tblCellMar>'
               '</w:tblPr><w:tblGrid>' + "".join(f'<w:gridCol w:w="{v}"/>' for v in widths) + '</w:tblGrid>']
        for ri in range(len(ys) - 1):
            rowh = max(20, int(round((ys[ri + 1] - ys[ri]) * k * 20)))
            out.append(f'<w:tr><w:trPr><w:trHeight w:val="{rowh}" w:hRule="exact"/></w:trPr>')
            span, covered = b.get("span") or {}, b.get("covered") or {}
            for ci in range(len(xs) - 1):
                merge, wide = "", widths[ci]
                if (ri, ci) in covered:
                    r0, c0 = covered[(ri, ci)]
                    if ci != c0:
                        continue                        # inside a cell that runs across: no cell of its own
                    rs, cs = span[(r0, c0)]             # below the start of a cell that runs down
                    wide = sum(widths[c0:c0 + cs])
                    fill = b["fills"][r0][c0]
                    shade = f'<w:shd w:val="clear" w:color="auto" w:fill="{fill[0]:02X}{fill[1]:02X}{fill[2]:02X}"/>' if fill else ''
                    out.append(f'<w:tc><w:tcPr><w:tcW w:w="{wide}" w:type="dxa"/>' + (f'<w:gridSpan w:val="{cs}"/>' if cs > 1 else '') +
                               f'<w:vMerge/>{shade}</w:tcPr><w:p><w:pPr><w:spacing w:before="0" w:after="0" w:line="20" '
                               'w:lineRule="exact"/></w:pPr></w:p></w:tc>')
                    continue
                if (ri, ci) in span:
                    rs, cs = span[(ri, ci)]
                    wide = sum(widths[ci:ci + cs])
                    merge = (f'<w:gridSpan w:val="{cs}"/>' if cs > 1 else '') + ('<w:vMerge w:val="restart"/>' if rs > 1 else '')
                fill = b["fills"][ri][ci]
                shade = f'<w:shd w:val="clear" w:color="auto" w:fill="{fill[0]:02X}{fill[1]:02X}{fill[2]:02X}"/>' if fill else ''
                out.append(f'<w:tc><w:tcPr><w:tcW w:w="{wide}" w:type="dxa"/>{merge}{shade}</w:tcPr>')
                paras = sorted(_set_alignment(_paragraphs(b["cells"][ri][ci]), (xs[ci], xs[ci + (b.get("span") or {}).get((ri, ci), (1, 1))[1]])), key=lambda p: p["box"][1])
                cursor = ys[ri]
                pic = (b.get("pics") or {}).get((ri, ci))
                if pic is not None:                     # this cell is kept as a picture of itself
                    paras = []
                    out.append(self._figure(pic, k, max(0.0, (pic["box"][1] - ys[ri]) * k - 1.0), max(0.0, (pic["box"][0] - xs[ci]) * k), True)
                               or '<w:p/>')
                    out.append('</w:tc>')
                    continue
                for p in paras:
                    size = p["size"]
                    top = p["lines"][0]["base"] - (p["pitch"] if p["pitch"] > 0 else 1.22 * size) + 0.24 * size
                    out.append(self._para(p, k, max(0.0, (top - cursor) * k), max(0.0, (p["box"][0] - xs[ci]) * k), 0, True))
                    cursor = p["lines"][-1]["base"] + 0.24 * size
                if not paras:
                    out.append('<w:p><w:pPr><w:spacing w:before="0" w:after="0" w:line="20" w:lineRule="exact"/></w:pPr></w:p>')
                out.append('</w:tc>')
            out.append('</w:tr>')
        out.append('</w:tbl>')
        return "".join(out)

    def _gap(self, px):
        """A vertical gap of `px` page pixels, as it will be written: noted, and narrowed if the page is over-full."""
        px = max(0.0, px)
        self.gaps = getattr(self, "gaps", 0.0) + px
        return px * getattr(self, "gap", 1.0)

    def _stack(self, blocks, k, top, left_edge, right_edge):
        """Blocks one under another, starting at pixel row `top`, in a column from left_edge to right_edge."""
        out, cursor, after_table = [], top, False
        for b in sorted(blocks, key=lambda b: b["box"][1]):
            x0, y0, x1, y1 = b["box"]
            left = max(0.0, (x0 - left_edge) * k)
            if b["kind"] == "para":
                size = b["size"]
                pitch = b["pitch"] if b["pitch"] > 0 else 1.22 * size
                if b["pitch"] <= 0:
                    # A one-line paragraph has no spacing of its own to measure. Set closer to the line
                    # above than the usual spacing allows, it takes a lower line (never lower than the
                    # type itself) - otherwise every item of a tight list would be pushed down a little,
                    # and the foot of the page on to the next.
                    room = b["lines"][0]["base"] + 0.24 * size - cursor
                    if room < pitch:
                        pitch = max(1.0 * size, room)
                        b = dict(b, pitch=pitch)
                start = b["lines"][0]["base"] - pitch + 0.24 * size          # where Word's line box begins
                # free-flowing text gets a little room, so that lines break about where they did; with
                # the original's line ends kept, a justified paragraph is exactly as wide as it was
                slack = 0.0 if (self.keep_lines and b.get("justified")) else 1.2 * size
                out.append(self._para(b, k, self._gap(start - cursor) * k, left, max(0.0, (right_edge - x1 - slack) * k)))
                # where this paragraph really ends: if it had to start late (no room above it), it ends
                # late too, and the next gap is shortened by as much - so one tight spot does not shift
                # the rest of the page
                cursor = max(start, cursor) + pitch * len(b["lines"])
                after_table = False
            elif b["kind"] == "figure":
                out.append(self._figure(b, k, self._gap(y0 - cursor) * k, left))
                cursor, after_table = max(cursor, y0) + (y1 - y0) + 1.5 / k, False
            elif b["kind"] == "rule":
                out.append(self._rule(b, k, self._gap(y0 - cursor) * k, left, max(0.0, (right_edge - x1) * k)))
                cursor, after_table = max(cursor, y0) + (y1 - y0) + 2 / k, False
            else:
                out.append(self._spacer(max(1.0, self._gap(y0 - cursor) * k)))
                out.append(self._table(b, k, left))
                cursor, after_table = max(cursor + 1 / k, y0) + (y1 - y0), True
        if after_table or not out:
            out.append(self._spacer(1.0))
        return "".join(out), cursor

    def add_page(self, w, h, k, blocks, whole=None):
        """w, h: page size in pixels. k: pixels -> points. blocks: from _layout_page. whole: the page's own
        picture, used in place of the blocks if they cannot be made to fit the page."""
        if self.sect is not None:
            self._close(final=False)
        fams = [b["family"] for b in blocks if b["kind"] == "para" and b["family"]]
        if fams:
            self.default_font = max(set(fams), key=fams.count)
        if not blocks:
            self.body.append(self._spacer(1.0))
            self.sect = (w * k, h * k, 36.0, 36.0, 36.0)
            return
        left = max(0.0, min(b["box"][0] for b in blocks))
        right = min(float(w), max(b["box"][2] for b in blocks))
        top = max(0.0, min(b["box"][1] for b in blocks))
        ml, mt = max(18.0, left * k), max(14.0, min(top * k, 0.5 * h * k))
        mr = max(18.0, (w - right) * k - 14.0)
        left_edge, top_edge, right_edge = ml / k, mt / k, w - mr / k
        self.tallest = int((h * k - mt - 48.0) * 12700)
        # blocks that sit side by side (a picture with notes beside it, two columns) share a band
        bands = []
        span = max(1.0, right - left)
        fences = [(b["box"][1] + b["box"][3]) / 2 for b in blocks
                  if b["kind"] == "rule" and b["box"][2] - b["box"][0] >= 0.6 * span]     # rules across the page
        for b in sorted(blocks, key=lambda b: b["box"][1]):
            mid = (b["box"][1] + b["box"][3]) / 2
            for band in bands:
                o = min(band["y1"], b["box"][3]) - max(band["y0"], b["box"][1])
                # what lies below a rule drawn across the page is not beside what lies above it
                if b["kind"] != "rule" and any(band["mid"] < f < mid for f in fences):
                    continue
                if o > 0.3 * min(band["y1"] - band["y0"], b["box"][3] - b["box"][1]):
                    band["items"].append(b)
                    band["y0"], band["y1"] = min(band["y0"], b["box"][1]), max(band["y1"], b["box"][3])
                    break
            else:
                bands.append({"y0": b["box"][1], "y1": b["box"][3], "items": [b], "mid": mid})
        # A page set in columns is ONE band, not one per paragraph: bands whose blocks all sit inside the
        # columns of the band above are joined to it. (Each band is a table in the Word file, and every
        # table costs a little height - dozens of them pushed the foot of the page on to the next.)
        tol = 0.012 * w
        sizes = [b["size"] for b in blocks if b["kind"] == "para"]
        typ = float(np.median(sizes)) if sizes else 0.012 * h        # the height of a line of type, in pixels
        joined = []
        for band in sorted(bands, key=lambda bd: bd["y0"]):
            starts = []
            for b in sorted(band["items"], key=lambda b: b["box"][0]):
                if not starts or b["box"][0] >= starts[-1][1] - 2:
                    starts.append([b["box"][0], b["box"][2]])
                else:
                    starts[-1][1] = max(starts[-1][1], b["box"][2])
            cur = joined[-1] if joined else None
            if cur is not None and min(band["y1"], cur["y1"]) - band["y0"] >= max(4.0, min(0.25 * (band["y1"] - band["y0"]), 0.6 * typ)):
                # it starts before the band above has ended: they are side by side, whatever the first
                # look said - one band (stacked, the lower would be pushed down the page)
                cur["items"] += band["items"]
                cur["y1"] = max(cur["y1"], band["y1"])
                again = []
                for b in sorted(cur["items"], key=lambda b: b["box"][0]):
                    if not again or b["box"][0] >= again[-1][1] - 2:
                        again.append([b["box"][0], b["box"][2]])
                    else:
                        again[-1][1] = max(again[-1][1], b["box"][2])
                cur["edges"] = [c[0] for c in again] + [max(right_edge, again[-1][1])] if len(again) >= 2 else None
                continue
            if cur is not None and cur["edges"]:
                spans = list(zip(cur["edges"], cur["edges"][1:]))
                inside = all(any(e0 - tol <= b["box"][0] and b["box"][2] <= e1 + tol for e0, e1 in spans) for b in band["items"])
                # columns of its own must be the same columns (a three-column table under two-column
                # text is not more of that text)
                same = len(starts) == 1 or (len(starts) == len(spans) and
                                            all(abs(c[0] - e) <= 3 * tol for c, e in zip(starts, cur["edges"])))
                if inside and same:
                    cur["items"] += band["items"]
                    cur["y1"] = max(cur["y1"], band["y1"])
                    continue
            # the columns' left edges, the last one's right edge standing in for the page's
            band["edges"] = [c[0] for c in starts] + [max(right_edge, starts[-1][1])] if len(starts) >= 2 else None
            joined.append(band)
        bands = joined
        def lay():
            """Write the page's bands; returns the row (in page pixels) the content really ends on."""
            cursor = top_edge
            for band in sorted(bands, key=lambda bd: bd["y0"]):
                cols = []
                for b in sorted(band["items"], key=lambda b: b["box"][0]):
                    if cols and b["box"][0] < cols[-1]["x1"] - 2:
                        cols[-1]["items"].append(b)
                        cols[-1]["x1"] = max(cols[-1]["x1"], b["box"][2])
                    else:
                        cols.append({"x0": b["box"][0], "x1": b["box"][2], "items": [b]})
                if len(cols) == 1:
                    xml, cursor = self._stack(band["items"], k, cursor, left_edge, right_edge)
                    self.body.append(xml)
                    continue
                # side by side: an invisible one-row table, one cell per column
                edges = [cols[0]["x0"]] + [c["x0"] for c in cols[1:]] + [max(right_edge, cols[-1]["x1"])]
                widths = [max(20, int(round((edges[i + 1] - edges[i]) * k * 20))) for i in range(len(cols))]
                self.body.append(self._spacer(max(1.0, self._gap(band["y0"] - cursor) * k)))
                row = [f'<w:tbl><w:tblPr><w:tblW w:w="{sum(widths)}" w:type="dxa"/><w:tblInd w:w="{int(round((edges[0] - left_edge) * k * 20))}" '
                       'w:type="dxa"/><w:tblLayout w:type="fixed"/><w:tblCellMar><w:top w:w="0" w:type="dxa"/><w:left w:w="0" w:type="dxa"/>'
                       '<w:bottom w:w="0" w:type="dxa"/><w:right w:w="0" w:type="dxa"/></w:tblCellMar></w:tblPr><w:tblGrid>'
                       + "".join(f'<w:gridCol w:w="{v}"/>' for v in widths) + '</w:tblGrid><w:tr>']
                ends = []
                for ci, col in enumerate(cols):
                    xml, end = self._stack(col["items"], k, band["y0"], edges[ci], edges[ci + 1])
                    ends.append(end)
                    row.append(f'<w:tc><w:tcPr><w:tcW w:w="{widths[ci]}" w:type="dxa"/></w:tcPr>{xml}</w:tc>')
                row.append('</w:tr></w:tbl>')
                self.body.append("".join(row))
                cursor = max([max(cursor + 1 / k, band["y0"]) + (band["y1"] - band["y0"])] + ends) + 2.0 / k   # where the columns really end
            return cursor

        # Once without writing anything, to see where the page would end. If that is past the foot of
        # the page - something on it took more room than it had in the original - the gaps between
        # blocks are narrowed by just enough, so the page stays one page and the next starts where it should.
        mark = len(self.body)
        self.dry, self.gap, self.gaps = True, 1.0, 0.0
        over = lay() - (h - 16.0 / k)
        del self.body[mark:]
        self.dry = False
        if os.environ.get("SNAPCLEAN_DEBUG"):
            print(f"    word page: content ends {over * k:+.0f} pt from the foot; gaps total {self.gaps * k:.0f} pt")
        self.gap = 1.0 if over <= 0 or self.gaps <= 0 else max(0.0, 1.0 - 1.15 * over / self.gaps)
        if whole is not None and (over - 0.85 * self.gaps) * k > 36.0:
            # Even with every gap closed the page runs half an inch or more past its foot: the layout has
            # gone wrong (something on the page this program does not understand). A page that spills
            # throws every page after it out of step, so this one is put in as its picture instead.
            self.pictured = getattr(self, "pictured", 0) + 1
            self.sect = None
            return self.add_page(w, h, k, [{"kind": "figure", "box": (0, 0, w, h), "image": whole}])
        lay()
        self.body.append(self._spacer(1.0))
        self.sect = (w * k, h * k, ml, mt, mr)

    def _close(self, final):
        wp, hp, ml, mt, mr = self.sect
        sect = (f'<w:sectPr><w:pgSz w:w="{int(round(wp * 20))}" w:h="{int(round(hp * 20))}"'
                f'{" w:orient=" + chr(34) + "landscape" + chr(34) if wp > hp else ""}/>'
                f'<w:pgMar w:top="{int(round(mt * 20))}" w:right="{int(round(mr * 20))}" w:bottom="200" '
                f'w:left="{int(round(ml * 20))}" w:header="0" w:footer="0" w:gutter="0"/></w:sectPr>')
        if final:
            self.body.append(sect)
        else:
            self.body.append('<w:p><w:pPr><w:spacing w:before="0" w:after="0" w:line="20" w:lineRule="exact"/>'
                             f'<w:rPr><w:sz w:val="2"/></w:rPr>{sect}</w:pPr></w:p>')

    def save(self):
        if self.sect is None:
            self.body.append("<w:p/>")
            self.sect = (612.0, 792.0, 36.0, 36.0, 36.0)
        self._close(final=True)
        head = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
        self.zip.writestr("[Content_Types].xml", head +
                          '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
                          '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
                          '<Default Extension="xml" ContentType="application/xml"/><Default Extension="png" ContentType="image/png"/>'
                          '<Default Extension="jpg" ContentType="image/jpeg"/>'
                          '<Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.'
                          'wordprocessingml.document.main+xml"/></Types>')
        self.zip.writestr("_rels/.rels", head +
                          '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                          '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/'
                          'officeDocument" Target="word/document.xml"/></Relationships>')
        self.zip.writestr("word/_rels/document.xml.rels", head +
                          '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                          + "".join(self.rels) + '</Relationships>')
        self.zip.writestr("word/document.xml", head + f'<w:document {_Docx.NS}><w:body>' + "".join(self.body)
                          + '</w:body></w:document>')
        self.zip.close()


_WORKER = {}                    # per-process state when pages are handled in parallel


def _encode_picture(rgb):
    """(bytes, "png" | "jpg"). Clean pages stay lossless; noisy scans, which PNG cannot shrink and
    which would otherwise fill memory and bloat the files, are stored as high-quality JPEG."""
    ok, png = cv2.imencode(".png", np.ascontiguousarray(rgb[..., ::-1]))
    if png.size <= 0.3 * rgb.shape[0] * rgb.shape[1]:
        return png.tobytes(), "png"
    ok, jpg = cv2.imencode(".jpg", np.ascontiguousarray(rgb[..., ::-1]), [cv2.IMWRITE_JPEG_QUALITY, 88])
    return (jpg.tobytes(), "jpg") if ok and jpg.size < png.size else (png.tobytes(), "png")


READ_SCHEME = "10"       # changes whenever pages are read differently, so old kept readings are not reused


def _reader_tag():
    """Part of a kept reading's name: readings made another way (second engine, graphics card extras)
    are not the same readings."""
    if _OCR["name"] != "rapid":
        return ""
    card = bool(_graphics_card())
    return ("t" if _OCR.get("tesseract") else "") + ("g" if card else "") + os.environ.get("DEWATERMARK_EXTRA", "") + \
        "e" + os.environ.get("DEWATERMARK_ENLARGE", "") + \
        os.environ.get("DEWATERMARK_MODELS", "")[:1]


def _kept_reading(path, rgb=None):
    """Read a page's text - or fetch the reading kept from an earlier run over the very same picture.

    Reading is most of the work, and a second run (another strictness, or after typing in words the
    program could not read) asks for exactly the same readings. They are kept as small JSON files in
    the computer's temporary folder, named by the page picture's contents."""
    import tempfile
    store = None
    try:
        digest = hashlib.sha1()
        with open(path, "rb") as f:
            for block in iter(lambda: f.read(1 << 20), b""):
                digest.update(block)
        folder = Path(tempfile.gettempdir()) / "snapclean_readings"
        store = folder / f"{digest.hexdigest()}_{_OCR['name']}{_reader_tag()}_{READ_SCHEME}.json"
        if store.exists() and not os.environ.get("DEWATERMARK_NO_KEEP"):
            data = json.loads(store.read_text(encoding="utf-8"))
            ocr = [(t, x0, y0, x1, y1, c) for t, x0, y0, x1, y1, c in data["ocr"]]
            _OCR["last_read"] = "kept"
            return ocr, {tuple(k): [tuple(v) for v in spans] for k, spans in data["spans"]}
    except Exception:
        store = None if store is None or store.exists() else store
    if rgb is None:
        rgb = _load_page(path)[0]
    ocr = ocr_lines(rgb, conf=True)
    _OCR["last_read"] = (_OCR.get("device") or "unknown") if _OCR["name"] == "rapid" else "processor"
    spans = dict(_OCR.get("spans") or {})
    try:
        if store is not None and not os.environ.get("DEWATERMARK_NO_KEEP"):
            store.parent.mkdir(parents=True, exist_ok=True)
            part = store.with_suffix(f".{os.getpid()}.part")
            part.write_text(json.dumps({"ocr": [list(item) for item in ocr],
                                        "spans": [[list(k), [list(v) for v in sp]] for k, sp in spans.items()]}),
                            encoding="utf-8")
            os.replace(part, store)
    except Exception:
        pass
    return ocr, spans


def _read_task(path):
    """Read one page's text (first pass over a document). Returns what _page_result needs to carry on."""
    ocr, spans = _kept_reading(path)
    return ocr, spans, _OCR.get("last_read", "")


# ---- words the user typed in ------------------------------------------------------------------

USER_VOTES = 9          # a word the user typed counts as this many readings: nothing overrules it


def load_answers(path):
    """The user's typed-in words: {what the program read: what it really says}. Empty if there are none."""
    try:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        return {str(k): str(v) for k, v in (data.get("readings") or {}).items() if str(v).strip() and " " not in str(v).strip()}
    except Exception:
        return {}


def save_answers(path, readings):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps({"readings": dict(sorted(readings.items()))}, indent=1, ensure_ascii=False),
                          encoding="utf-8")


def _apply_answers(ocr, answers):
    """Put the user's words in place of the readings they were typed for."""
    if not answers:
        return ocr
    out = []
    for text, x0, y0, x1, y1, conf in ocr:
        toks = text.split()
        cs = list(conf) if isinstance(conf, list) and len(conf) == len(toks) else \
            [float(min(conf) if isinstance(conf, list) and conf else (conf if not isinstance(conf, list) else 0.0))] * len(toks)
        for i, tok in enumerate(toks):
            if tok in answers:
                toks[i], cs[i] = answers[tok], USER_VOTES + 0.99
        out.append((" ".join(toks), x0, y0, x1, y1, cs))
    return out


def _word_picture(rgb, L, fit, i, tint=False):
    """The picture of one word, cut so that it sits in a line of typed text like a word does.

    It runs from the word's left edge to its right, and from above the tallest letter to below the
    longest tail - the same band whatever the word, so every picture is about one "em" of the line's
    type high and lines up along the baseline. The paper is made pure white (or highlighter yellow), so
    no grey box shows round it. Returns (PNG bytes, width in ems, height in ems, part below the line in ems)."""
    ox, oy = L["org"]
    u, s = L["u"], float(fit["sizes"][i])
    base = oy + float(fit["bases"][i])
    c0, c1, r0, r1 = L["words"][i]
    above, below = 0.80, 0.26
    h, w = rgb.shape[:2]
    # a word taller than the usual band (a bracket, a big capital) keeps all of itself
    # Above: the full band. Below: only as far as this word's own tails go - a word with none ends on
    # the baseline and needs no lowering at all to sit right.
    top = oy + r0 / u - 2                               # no higher than the word itself: it must not cover the line above
    bottom = max(base + 1.0, min(base + max(below * s, 0.0), oy + r1 / u + 1), oy + r1 / u + 1)
    x0, x1 = int(max(0, math.floor(ox + c0 / u - 1))), int(min(w, math.ceil(ox + c1 / u + 1)))
    y0, y1 = int(max(0, math.floor(top))), int(min(h, math.ceil(bottom)))
    if x1 - x0 < 2 or y1 - y0 < 2:
        return None
    crop = rgb[y0:y1, x0:x1].astype(np.float32)
    # ink that belongs to the lines above and below is wiped: only this word's own rows are kept
    ink_top, ink_bottom = int(oy + r0 / u - 1) - y0, int(math.ceil(oy + r1 / u + 1)) - y0
    paper = np.maximum(np.asarray(L["bg"], np.float32), 1.0)
    crop[:max(0, ink_top)] = paper
    crop[max(0, ink_bottom):] = paper
    clean = np.clip(crop / paper, 0.0, 1.0)             # paper -> exactly white
    clean = np.where(clean > 0.93, 1.0, clean)
    shade = np.array([1.0, 1.0, 0.45], np.float32) if tint else np.ones(3, np.float32)
    img = np.rint(clean * shade * 255.0).astype(np.uint8)
    bgra = np.dstack([img[:, :, ::-1], np.full(img.shape[:2], 255, np.uint8)])
    if not tint:                                        # see-through paper: only the ink covers anything
        bgra[:, :, 3] = np.rint((1.0 - clean.min(axis=2)) * 255.0).astype(np.uint8)
    ok, png = cv2.imencode(".png", np.ascontiguousarray(bgra), [cv2.IMWRITE_PNG_COMPRESSION, 9])
    if not ok:
        return None
    drop = (y1 - base) / s
    return png.tobytes(), (x1 - x0) / s, (y1 - y0) / s, (drop if drop > 0.06 else 0.0)


def preview_word(entry, text):
    """What a review entry's strip of page will look like with `text` drawn in place of the boxed word.

    Drawn the way the document is: in the font and size chosen for that line, on its baseline, and
    fitted to the width of the word it replaces. Returns (PNG bytes, fits) - fits is False when the
    text would have to be squeezed or stretched so far that the program will keep the picture instead.
    None if the entry has nothing to draw with."""
    import io
    from PIL import Image as _Image, ImageDraw, ImageFont
    d = entry.get("draw")
    text = (text or "").strip()
    if not d or not text or not entry.get("png"):
        return None
    try:
        strip = _Image.open(io.BytesIO(entry["png"])).convert("RGB")
        size = max(4, int(round(d["size"])))
        if d.get("font"):
            font = ImageFont.truetype(d["font"], size)
        else:
            import pymupdf as fitz
            font = ImageFont.truetype(io.BytesIO(fitz.Font(d["code"]).buffer), size)
        x0, y0, x1, y1 = d["box"]
        base = d["base"]
        l, t, r, b = font.getbbox(text, anchor="ls")
        natural = max(1.0, float(r - l))
        stretch = (x1 - x0) / natural
        fits = 0.5 <= stretch <= 1.9
        pad = 6
        word = _Image.new("L", (int(natural) + 2 * pad, int(b - t) + 2 * pad), 0)
        ImageDraw.Draw(word).text((pad - l, pad - t), text, font=font, fill=255, anchor="ls")
        word = word.resize((max(1, int(round(word.width * stretch))), word.height), _Image.LANCZOS)
        paper = tuple(int(v) for v in d.get("paper", (252, 252, 252)))
        draw = ImageDraw.Draw(strip)
        draw.rectangle((x0 - 6, y0 - 6, x1 + 6, y1 + 6), fill=paper)        # the old word, and the red box round it
        ink = _Image.new("RGB", word.size, (12, 12, 12))
        strip.paste(ink, (int(round(x0 - pad * stretch)), int(round(base + t - pad))), word)
        draw.rectangle((x0 - 5, min(y0, base + t) - 5, x1 + 5, max(y1, base + b) + 5),
                       outline=(0, 150, 60) if fits else (230, 120, 0), width=2)
        out = io.BytesIO()
        strip.save(out, "PNG")
        return out.getvalue(), fits
    except Exception:
        return None


def _review_entry(rgb, L, i, raw, guess, reason, fit=None):
    """One word left as a picture, for the user to look at: a strip of the page with the word boxed."""
    ox, oy = L["org"]
    u = L["u"]
    c0, c1, r0, r1 = L["words"][i]
    wx0, wx1 = ox + c0 / u, ox + c1 / u
    wy0, wy1 = oy + r0 / u, oy + r1 / u
    line_h = float(np.clip(L["Du"].shape[0] / u, 12.0, 70.0))
    h, w = rgb.shape[:2]
    # the whole line the word is in (up to a good way either side), with the line above and the line below
    line_x0, line_x1 = ox, ox + L["D"].shape[1]
    reach = min(26 * line_h, 950.0)
    x0 = int(max(0, max(line_x0 - 0.5 * line_h, wx0 - reach)))
    x1 = int(min(w, min(line_x1 + 0.5 * line_h, wx1 + reach)))
    y0, y1 = int(max(0, wy0 - 2.25 * line_h)), int(min(h, wy1 + 2.25 * line_h))
    strip = np.ascontiguousarray(rgb[y0:y1, x0:x1])
    grey = cv2.cvtColor(strip, cv2.COLOR_RGB2GRAY)
    grey = (grey // 24) * 24 + 12                       # a few shades are plenty, and make a small file
    strip = cv2.cvtColor(grey, cv2.COLOR_GRAY2BGR)
    cv2.rectangle(strip, (int(wx0 - x0) - 3, int(wy0 - y0) - 3), (int(wx1 - x0) + 3, int(wy1 - y0) + 3), (0, 0, 230), 2)
    ok, png = cv2.imencode(".png", strip, [cv2.IMWRITE_PNG_COMPRESSION, 9])
    entry = {"reading": raw, "guess": guess, "reason": reason, "png": png.tobytes() if ok else b""}
    if fit is not None:                                 # what is needed to show the word as it will be redrawn
        face = fit["faces"][i]
        entry["draw"] = {"font": face.path, "code": face.code, "size": float(fit["sizes"][i]),
                         "base": float(oy + fit["bases"][i] - y0), "paper": [int(v) // 24 * 24 + 12 for v in L["bg"]],
                         "box": [float(wx0 - x0), float(wy0 - y0), float(wx1 - x0), float(wy1 - y0)]}
    return entry


def learn_terms(readings, least=3):
    """The document's own vocabulary: words no dictionary has but the document keeps using - NFPA, OSHA,
    a product or company name. Built from a first reading of every page and used, for this document
    only, as extra dictionary words.

    A term must be letters only, at least three of them, read the same way by two readings of the page
    each time, and found at least `least` times. Left out: anything one confusion away from a real
    word (a misreading that repeats, "elecuical"), and anything one letter away from a term seen far
    more often ("NEPA" beside "NFPA")."""
    count = {}
    for ocr in readings:
        after_hyphen = False
        for item in ocr:
            cs = item[5] if isinstance(item[5], list) else [item[5]] * len(item[0].split())
            toks = item[0].split()
            for j, (tok, c) in enumerate(zip(toks, cs)):
                # the halves of a word split over two lines ("protec-" / "tive") are not words
                if tok.endswith("-") or (j == 0 and after_hyphen):
                    continue
                core = _core(tok)[1]
                if core.endswith(("'s", "’s")):
                    core = core[:-2]
                if votes_of(c) >= 2 and len(core) >= 3 and core.isalpha() and not known_word(core):
                    count[core] = count.get(core, 0) + 1
            after_hyphen = bool(toks) and toks[-1].endswith("-")
    terms = set()
    for core, k in count.items():
        if k < least or _best_repair(core):
            continue
        rival = max((count[w] for w in count if w != core and len(w) == len(core)
                     and sum(a != b for a, b in zip(w, core)) == 1), default=0)
        if rival >= 3 * k:
            continue
        terms.add(core)
    return terms


def _page_result(path, plan, setter, keep_plain=False, flow=False, read=None, terms=None):
    """Everything one page needs for the PDF / Word file, as plain data (so it can come back from another process)."""
    rgb, info, times = _load_page(path)
    h, w = rgb.shape[:2]
    res = {"path": str(path), "w": w, "h": h, "dpi": _page_dpi(info, w, h), "failed": False, "planned": False, "times": times,
           "flattened": bool(isinstance(info, dict) and info.get("flattened")),
           "png": None, "ext": "png", "jobs": [], "hidden": [], "dlines": [], "replaced": 0, "flow": None,
           "confirmed": 0, "repaired": 0}
    if read is None:
        read = _kept_reading(path, rgb) + (_OCR.get("last_read", ""),)
    ocr, _OCR["spans"] = read[0], dict(read[1])
    res["device"] = read[2] if len(read) > 2 else ""
    if isinstance(terms, dict):
        _WORKER["terms"], _WORKER["counts"] = set(terms.get("terms") or ()), dict(terms.get("counts") or {})
        _WORKER["answers"] = dict(terms.get("answers") or {})
        _WORKER["options"] = dict(terms.get("options") or {})
    else:
        _WORKER["terms"], _WORKER["counts"], _WORKER["answers"], _WORKER["options"] = set(terms or ()), {}, {}, {}
    ocr = _apply_answers(ocr, _WORKER["answers"])
    _WORKER["review"] = []
    res["lines"] = len(ocr)
    res["ocr"] = [item[:5] for item in ocr]
    res["words"] = sum(len(item[0].split()) for item in ocr)
    if plan:
        try:
            picture, jobs, hidden, words, replaced, dlines, flines = _plan_page(rgb, ocr, setter, word_level=flow)
            res["why"] = dict(_WORKER.get("why") or {})
            res["review"] = list(_WORKER.get("review") or [])
            data, ext = _encode_picture(picture)
            if setter.mode == "substitute":
                res["fonts"] = "one font for the whole document: " + setter.subs[setter.body][(False, False)].family
            elif setter.mode == "matched":
                res["fonts"] = "matched line by line to the installed fonts"
            res.update(png=data, ext=ext, jobs=jobs, hidden=hidden, words=words, replaced=replaced,
                       dlines=dlines, planned=True, repaired=_WORKER.get("repaired", 0))
            if flow:
                res["flow"] = _layout_page(rgb, flines)
                res["whole"] = _encode_picture(rgb)
                if (_WORKER.get("options") or {}).get("html"):
                    res["ref"] = _reference_picture(rgb)
                res["confirmed"] = sum(sum(fl["oks"]) if fl["oks"] else (len(fl["text"].split()) if fl["ok"] else 0)
                                       for fl in flines)
        except Exception:               # never lose the whole document to one odd page: do this page the plain way
            import traceback
            traceback.print_exc()
            res["failed"] = True
    if res["png"] is None:
        res["png"], res["ext"] = _encode_picture(rgb)
    # a plain PDF made alongside a Word file needs the page picture with nothing erased
    res["plain"] = _encode_picture(rgb) if keep_plain and res["planned"] else None
    return res


def _worker_init(engine, tesseract, short_names, strictness="strict", use_dictionary=True):
    set_strictness(strictness, use_dictionary)
    os.environ["OMP_THREAD_LIMIT"] = "1"            # one Tesseract thread per worker: the workers are the parallelism
    _OCR["name"], _OCR["tesseract"] = engine, tesseract
    _WORKER["short"], _WORKER["few_threads"] = short_names, True


def _page_task(path, plan, keep_plain=False, flow=False, read=None, terms=None, state=None):
    setter = None
    if plan:
        setter = _WORKER.get("setter")
        if setter is None:
            setter = _WORKER["setter"] = Retypesetter()
            if state or _WORKER.get("short"):       # use the fonts already chosen on the first pages
                setter.adopt(state or _WORKER["short"])
    return _page_result(path, plan, setter, keep_plain, flow, read, terms)


def default_jobs():
    """How many pages to work on at once: the CPU cores, less one to keep the computer usable, at most 8."""
    return max(1, min(8, (os.cpu_count() or 2) - 1))


def _xml(text):
    return (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace('"', "&quot;").translate({c: None for c in range(32) if c not in (9, 10, 13)}))


class _Docx:
    """A minimal Word file writer: each page is its picture (matched text erased) behind one text box per
    re-typeset line, placed where the line was. Written with the standard library only."""

    NS = ('xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" '
          'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships" '
          'xmlns:wp="http://schemas.openxmlformats.org/drawingml/2006/wordprocessingDrawing" '
          'xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main" '
          'xmlns:pic="http://schemas.openxmlformats.org/drawingml/2006/picture" '
          'xmlns:wps="http://schemas.microsoft.com/office/word/2010/wordprocessingShape" '
          'xmlns:mc="http://schemas.openxmlformats.org/markup-compatibility/2006"')

    def __init__(self, path):
        import zipfile
        self.zip = zipfile.ZipFile(str(path), "w", zipfile.ZIP_DEFLATED)
        self.body, self.rels, self.n, self.shape = [], [], 0, 0
        self.last = None

    def _anchor(self, x, y, w, h, behind, inner):
        self.shape += 1
        return (f'<wp:anchor distT="0" distB="0" distL="0" distR="0" simplePos="0" relativeHeight="{self.shape + 2}" '
                f'behindDoc="{int(behind)}" locked="0" layoutInCell="1" allowOverlap="1"><wp:simplePos x="0" y="0"/>'
                f'<wp:positionH relativeFrom="page"><wp:posOffset>{x}</wp:posOffset></wp:positionH>'
                f'<wp:positionV relativeFrom="page"><wp:posOffset>{y}</wp:posOffset></wp:positionV>'
                f'<wp:extent cx="{w}" cy="{h}"/><wp:effectExtent l="0" t="0" r="0" b="0"/><wp:wrapNone/>'
                f'<wp:docPr id="{self.shape}" name="s{self.shape}"/><wp:cNvGraphicFramePr/>{inner}</wp:anchor>')

    def add_page(self, width_pt, height_pt, png, lines, k, ext="png"):
        """png: the page picture (ext says png or jpg). lines: the dicts made by _plan_page (pixels). k: pixels -> points."""
        E = 12700                                                   # EMU per point
        if self.last is not None:
            self._close_section(final=False)
        self.n += 1
        self.zip.writestr(f"word/media/page{self.n}.{ext}", png)
        self.rels.append(f'<Relationship Id="rId{self.n}" Type="http://schemas.openxmlformats.org/officeDocument/2006/'
                         f'relationships/image" Target="media/page{self.n}.{ext}"/>')
        W, H = int(round(width_pt * E)), int(round(height_pt * E))
        runs = ['<w:r><w:drawing>' + self._anchor(0, 0, W, H, True,
                '<a:graphic><a:graphicData uri="http://schemas.openxmlformats.org/drawingml/2006/picture"><pic:pic>'
                f'<pic:nvPicPr><pic:cNvPr id="{self.shape + 1}" name="page{self.n}.png"/><pic:cNvPicPr/></pic:nvPicPr>'
                f'<pic:blipFill><a:blip r:embed="rId{self.n}"/><a:stretch><a:fillRect/></a:stretch></pic:blipFill>'
                f'<pic:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="{W}" cy="{H}"/></a:xfrm>'
                '<a:prstGeom prst="rect"><a:avLst/></a:prstGeom></pic:spPr></pic:pic></a:graphicData></a:graphic>')
                + '</w:drawing></w:r>']
        for d in lines:
            size = d["size"] * k                                     # points
            line_h = (d["ascent"] + d["descent"]) * size
            chars = max(len(d["text"]) - 1, 1)
            track = (d["width"] - d["natural"]) * k / chars if d["natural"] > 0 else 0.0   # spread to the original width
            track = max(-1.0, min(1.5, track))
            r, g, b = (int(c) for c in d["colour"])
            font = _xml(d["family"])
            rpr = (f'<w:rFonts w:ascii="{font}" w:hAnsi="{font}" w:cs="{font}" w:eastAsia="{font}"/>'
                   + ('<w:b/><w:bCs/>' if d["bold"] else '') + ('<w:i/><w:iCs/>' if d["italic"] else '')
                   + f'<w:color w:val="{r:02X}{g:02X}{b:02X}"/><w:spacing w:val="{int(round(track * 20))}"/>'
                   + f'<w:sz w:val="{max(2, int(round(size * 2)))}"/><w:szCs w:val="{max(2, int(round(size * 2)))}"/>')
            para = (f'<w:p><w:pPr><w:spacing w:before="0" w:after="0" w:line="{max(20, int(round(line_h * 20)))}" '
                    f'w:lineRule="exact"/><w:rPr>{rpr}</w:rPr></w:pPr><w:r><w:rPr>{rpr}</w:rPr>'
                    f'<w:t xml:space="preserve">{_xml(d["text"])}</w:t></w:r></w:p>')
            x = int(round(d["x"] * k * E))
            y = int(round((d["base"] * k - d["ascent"] * size) * E))
            w = int(round((max(d["width"], d["natural"]) * k + size) * E))
            h = int(round(line_h * 1.15 * E))
            shape = ('<a:graphic><a:graphicData uri="http://schemas.microsoft.com/office/word/2010/wordprocessingShape">'
                     f'<wps:wsp><wps:cNvSpPr txBox="1"/><wps:spPr><a:xfrm><a:off x="0" y="0"/><a:ext cx="{w}" cy="{h}"/></a:xfrm>'
                     '<a:prstGeom prst="rect"><a:avLst/></a:prstGeom><a:noFill/><a:ln><a:noFill/></a:ln></wps:spPr>'
                     f'<wps:txbx><w:txbxContent>{para}</w:txbxContent></wps:txbx>'
                     '<wps:bodyPr rot="0" vert="horz" wrap="none" lIns="0" tIns="0" rIns="0" bIns="0" anchor="t" anchorCtr="0">'
                     '<a:noAutofit/></wps:bodyPr></wps:wsp></a:graphicData></a:graphic>')
            runs.append('<w:r><mc:AlternateContent><mc:Choice Requires="wps"><w:drawing>'
                        + self._anchor(x, y, w, h, False, shape) + '</w:drawing></mc:Choice></mc:AlternateContent></w:r>')
        tiny = '<w:spacing w:before="0" w:after="0" w:line="20" w:lineRule="exact"/><w:rPr><w:sz w:val="2"/></w:rPr>'
        self.body.append(f'<w:p><w:pPr>{tiny}</w:pPr>{"".join(runs)}</w:p>')
        self.last = (int(round(width_pt * 20)), int(round(height_pt * 20)))

    def _close_section(self, final):
        w, h = self.last
        sect = (f'<w:sectPr><w:pgSz w:w="{w}" w:h="{h}"{" w:orient=" + chr(34) + "landscape" + chr(34) if w > h else ""}/>'
                '<w:pgMar w:top="0" w:right="0" w:bottom="0" w:left="0" w:header="0" w:footer="0" w:gutter="0"/></w:sectPr>')
        if final:
            self.body.append(sect)
        else:
            self.body.append('<w:p><w:pPr><w:spacing w:before="0" w:after="0" w:line="20" w:lineRule="exact"/>'
                             f'<w:rPr><w:sz w:val="2"/></w:rPr>{sect}</w:pPr></w:p>')

    def save(self):
        if self.last is None:
            self.body.append("<w:p/>")
            self.last = (12240, 15840)
        self._close_section(final=True)
        head = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
        self.zip.writestr("[Content_Types].xml", head +
                          '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
                          '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
                          '<Default Extension="xml" ContentType="application/xml"/><Default Extension="png" ContentType="image/png"/>'
                          '<Default Extension="jpg" ContentType="image/jpeg"/>'
                          '<Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.'
                          'wordprocessingml.document.main+xml"/></Types>')
        self.zip.writestr("_rels/.rels", head +
                          '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                          '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/'
                          'officeDocument" Target="word/document.xml"/></Relationships>')
        self.zip.writestr("word/_rels/document.xml.rels", head +
                          '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                          + "".join(self.rels) + '</Relationships>')
        self.zip.writestr("word/document.xml", head + f'<w:document {self.NS}><w:body>' + "".join(self.body)
                          + '</w:body></w:document>')
        self.zip.close()


# ---- web page (.html): every paragraph, picture and table an object that can be edited and moved -------
#
# One self-contained file. Each page is a sheet of the original size; on it every paragraph is a text
# box, every picture an image, every ruled table a real table - all placed where they are on the page,
# and all of them objects: in Edit mode (E) the text is typed over in place, in Move mode (G) anything is
# dragged, resized, restacked or deleted, the way the slide-toolkit's presenter does it. Save writes the
# edited page back out as the same kind of file; Print gives the pages at their real size.

_HTML_CSS = r"""
:root{--ui:#1f2a37;--ui2:#334155;--acc:#2563eb}
*{box-sizing:border-box}
html{background:#6b7280}
body{margin:0;padding:52px 0 60px;font-family:"Times New Roman",Times,serif;color:#000}
.page{position:relative;margin:0 auto 18px;background:#fff;box-shadow:0 2px 12px rgba(0,0,0,.45);overflow:hidden}
.page>.ref{position:absolute;left:0;top:0;width:100%;height:100%;opacity:0;pointer-events:none;z-index:0}
body.showref .page>.ref{opacity:.45}
body.onlyref .page>.ref{opacity:1}
body.onlyref .page>.obj{visibility:hidden}
.obj{position:absolute;z-index:1;margin:0}
.tb{white-space:nowrap;cursor:default;outline:0}
.tb .ln{display:block;white-space:nowrap}
.tb .ln>span.t{display:inline-block;white-space:pre;transform-origin:left center}
.tb.flow{white-space:normal}
.tb.flow .ln{display:inline;white-space:normal}
.tb.ins{white-space:pre-wrap;min-width:20pt;min-height:1em}
.tb.note{background:#fff7a8;border:1px solid #d6b500;border-radius:3px;padding:3pt 5pt;box-shadow:1px 2px 5px rgba(0,0,0,.3);font-family:"Segoe UI",Arial,sans-serif;color:#222;z-index:50}
body.nonotes .tb.note{display:none}
img.pic{display:block;user-select:none;-webkit-user-drag:none}
img.wp{display:inline-block}
.rule{font-size:0;line-height:0}
table.tbl{border-collapse:collapse;table-layout:fixed}
table.tbl td{padding:0;vertical-align:top;position:relative;overflow:hidden}
table.tbl td>.tb,table.tbl td>img.pic{position:absolute}
mark{background:#fff36b;color:inherit}
body.nomark mark{background:transparent}
/* --- the editor (never printed) --- */
#bar{position:fixed;left:0;top:0;right:0;height:40px;z-index:9000;background:var(--ui);color:#e5e7eb;display:flex;align-items:center;
 gap:4px;padding:0 8px;font:13px "Segoe UI",system-ui,Arial,sans-serif;box-shadow:0 2px 8px rgba(0,0,0,.4);white-space:nowrap;overflow-x:auto}
#bar button,#bar select,#bar label.btn{font:inherit;color:#e5e7eb;background:var(--ui2);border:1px solid #475569;border-radius:5px;
 padding:4px 9px;cursor:pointer;height:28px;line-height:18px}
#bar button:hover,#bar label.btn:hover{background:#475569}
#bar button.on{background:var(--acc);border-color:#93c5fd;color:#fff}
#bar .sep{width:1px;height:22px;background:#475569;margin:0 4px}
#bar .grp{display:none;align-items:center;gap:4px}
body.edit #bar .grp.e,body.move #bar .grp.m,body.edit #bar .grp.t,body.move #bar .grp.t{display:flex}
#bar input[type=number]{font:inherit;color:#e5e7eb;background:var(--ui2);border:1px solid #475569;border-radius:5px;height:28px;width:58px;padding:0 4px}
#bar select{max-width:170px}
#bar input[type=color]{width:30px;height:26px;padding:0;border:1px solid #475569;background:var(--ui2);border-radius:5px}
#bar .title{opacity:.75;margin-right:6px;max-width:22vw;overflow:hidden;text-overflow:ellipsis}
#bar .sp{flex:1}
#hint{position:fixed;left:0;right:0;bottom:0;z-index:9000;background:rgba(31,42,55,.94);color:#e5e7eb;font:12px "Segoe UI",system-ui,Arial,sans-serif;
 padding:6px 12px;min-height:28px}
#hint b{color:#fff}
body.hideui #bar,body.hideui #hint{display:none}
body.hideui{padding-top:12px}
body.move .page>.obj{cursor:move}
body.move .page>.obj:hover{outline:1px dashed #60a5fa}
.sel{outline:2px solid var(--acc)!important}
.sel2{outline:2px dashed var(--acc)!important}
#grip{position:absolute;width:12px;height:12px;background:var(--acc);border:2px solid #fff;border-radius:2px;z-index:8000;cursor:nwse-resize;display:none}
#band{position:absolute;border:1px dashed var(--acc);background:rgba(37,99,235,.12);z-index:8000;display:none;pointer-events:none}
#gv,#gh{position:absolute;background:#e11d8f;z-index:7900;display:none;pointer-events:none}
#gv{top:0;bottom:0;width:1px}
#gh{left:0;right:0;height:1px}
#find{position:fixed;right:10px;top:46px;z-index:9001;background:var(--ui);color:#e5e7eb;border:1px solid #475569;border-radius:7px;padding:8px;display:none;
 font:13px "Segoe UI",system-ui,Arial,sans-serif;box-shadow:0 4px 14px rgba(0,0,0,.45)}
#find input{font:inherit;width:190px;margin:0 6px 6px 0;padding:3px 6px;border-radius:4px;border:1px solid #475569;background:#fff;color:#000}
#find button{font:inherit;color:#e5e7eb;background:var(--ui2);border:1px solid #475569;border-radius:5px;padding:3px 9px;cursor:pointer;margin-right:4px}
#find .n{opacity:.8;margin-left:6px}
body.hideui #find{display:none!important}
body.edit .tb{cursor:text}
body.edit .page>.tb:hover,body.edit td>.tb:hover{outline:1px dashed #f59e0b}
body.edit .tb:focus{outline:2px solid #f59e0b}
body.place .page{cursor:crosshair}
.pgno{position:absolute;right:6px;top:-16px;font:11px "Segoe UI",Arial,sans-serif;color:#e5e7eb}
@media print{
 html,body{background:#fff}
 body{padding:0}
 #bar,#hint,#grip,#band,#gv,#gh,#find,.pgno{display:none!important}
 .page{margin:0;box-shadow:none;page-break-after:always;break-after:page}
 .page>.ref{display:none}
 .tb.note{display:none!important}
 .sel,.sel2{outline:0!important}
 mark{background:transparent}
}
"""

_HTML_JS = r"""
(function(){
'use strict';
var $=function(s,r){return (r||document).querySelector(s)}, $$=function(s,r){return Array.prototype.slice.call((r||document).querySelectorAll(s))};
var placing='text', body=document.body, mode='view', sel=[], undo=[], hint=$('#hint'), grip=$('#grip'), band=$('#band'), lastBox=null, fileHandle=null, dirty=false;
var PT=96/72;                                     // CSS px in a point
function say(t){hint.innerHTML=t}
var HINTS={view:'<b>E</b> edit text · <b>G</b> move / resize · <b>Ctrl+F</b> find and replace · <b>O</b> show the original page behind · <b>Ctrl+S</b> save · <b>Ctrl+P</b> print or save as PDF · <b>H</b> hide these bars',
 edit:'<b>Edit text:</b> click a text box and type. Font, size, <b>B</b> <b>I</b> <b>U</b> in the bar change the words you have selected - or the whole box when none are selected. <b>＋text</b> then click a page to add a box. <b>Flow</b> lets a box re-wrap its text. <b>Esc</b> leaves.',
 move:'<b>Move / resize:</b> drag anything; drag the blue corner to resize (Shift frees a picture\'s proportions). Arrows nudge 1 px (Shift 10) · <b>Shift+click</b> or drag a box on empty paper to select several · <b>Delete</b> removes · <b>Backspace</b> puts it back where it was · <b>Ctrl+Z</b> undo · <b>Ctrl+D</b> duplicate · Alt = no snapping · <b>Esc</b> deselects.'};

/* ---- fit each printed line to the width it has on the page ---- */
function fitLine(ln){
  var t=ln.firstElementChild; if(!t||!t.classList.contains('t')) return;
  var want=parseFloat(ln.getAttribute('data-w'))*PT; if(!want) return;
  t.style.letterSpacing='';t.style.wordSpacing='';t.style.transform='';
  var have=t.getBoundingClientRect().width/zoomOf(ln); if(!have) return;
  var txt=t.textContent, n=txt.length, sp=(txt.match(/ /g)||[]).length, d=want-have;
  if(Math.abs(d)<0.4) return;
  if(d>0){                                        // narrower than the original: open the spaces of a full line
    if(ln.getAttribute('data-j')==='1'&&sp>0) t.style.wordSpacing=Math.min(d/sp,parseFloat(getComputedStyle(t).fontSize)*0.9)+'px';
  }else{                                          // wider: close the letters up, then squeeze what is left
    var fs=parseFloat(getComputedStyle(t).fontSize), ls=Math.max(d/Math.max(n,1),-0.05*fs);
    t.style.letterSpacing=ls+'px';
    var now=t.getBoundingClientRect().width/zoomOf(ln);
    if(now>want+0.5) t.style.transform='scaleX('+(want/now).toFixed(4)+')';
  }
}
function zoomOf(){return 1}
function fitAll(root){$$('.tb:not(.flow) .ln',root||document).forEach(fitLine)}

/* ---- modes ---- */
function setMode(m){
  if(mode===m) m='view';
  mode=m; body.classList.remove('edit','move','place'); if(m!=='view') body.classList.add(m);
  $$('#bar [data-mode]').forEach(function(b){b.classList.toggle('on',b.getAttribute('data-mode')===m)});
  $$('.tb').forEach(function(tb){ if(m==='edit') tb.setAttribute('contenteditable','true'); else tb.removeAttribute('contenteditable') });
  if(m!=='move') select([]);
  say(HINTS[m]);
}
function objOf(el){ while(el&&el!==body){ if(el.classList&&el.classList.contains('obj')&&el.parentNode.classList.contains('page')) return el; el=el.parentNode } return null }
function boxOf(el){ while(el&&el!==body){ if(el.classList&&el.classList.contains('tb')) return el; el=el.parentNode } return null }
function pageOf(el){ while(el&&el!==body){ if(el.classList&&el.classList.contains('page')) return el; el=el.parentNode } return null }

/* ---- selection ---- */
function select(list){
  sel.forEach(function(o){o.classList.remove('sel','sel2')});
  sel=list.filter(function(o,i){return o&&list.indexOf(o)===i});
  sel.forEach(function(o,i){o.classList.add(i===0?'sel':'sel2')});
  placeGrip(); if(typeof showType==='function') showType();
  if(mode==='move') say(sel.length? '<b>'+sel.length+' selected</b> — '+describe(sel[0])+' · drag to move, corner to resize, Delete to remove, Backspace to put back' : HINTS.move);
}
function describe(o){var r=geom(o);return (o.tagName==='IMG'?'picture':o.tagName==='TABLE'?'table':o.classList.contains('rule')?'line':'text box')+' '+Math.round(r.w)+'×'+Math.round(r.h)+' pt at '+Math.round(r.x)+', '+Math.round(r.y)}
function geom(o){return {x:parseFloat(o.style.left)||0,y:parseFloat(o.style.top)||0,w:o.offsetWidth/PT,h:o.offsetHeight/PT}}
function placeGrip(){
  if(mode!=='move'||!sel.length){grip.style.display='none';return}
  var o=sel[0], p=o.parentNode; p.appendChild(grip);
  grip.style.left=(o.offsetLeft+o.offsetWidth-6)+'px'; grip.style.top=(o.offsetTop+o.offsetHeight-6)+'px'; grip.style.display='block';
}
function snap(v,ev){return ev&&ev.altKey?v:Math.round(v/3)*3}       // 3 pt = 4 px
function remember(fn){undo.push(fn); if(undo.length>200) undo.shift(); dirty=true}
function styleState(list){var st=list.map(function(o){return [o,o.getAttribute('style')]});return function(){st.forEach(function(s){s[0].setAttribute('style',s[1]||'')});placeGrip();refit(list)}}
function refit(list){list.forEach(function(o){if(o.classList.contains('tb')) fitAll(o)})}

/* ---- move mode: drag, rubber band, resize ---- */
var drag=null;
document.addEventListener('mousedown',function(ev){
  if(ev.button!==0||ev.target.closest('#bar')||ev.target.closest('#hint')) return;
  if(mode==='place'){ dropBox(ev); return }
  if(mode!=='move') return;
  if(ev.target===grip){ ev.preventDefault(); var o=sel[0], g=geom(o);
    drag={kind:'size',o:o,x:ev.clientX,y:ev.clientY,w:g.w,h:g.h,fs:parseFloat(o.style.fontSize)||0,undo:styleState([o])}; return }
  var o2=objOf(ev.target), pg=pageOf(ev.target);
  if(o2&&!ev.ctrlKey&&!ev.metaKey){ ev.preventDefault();
    if(ev.shiftKey){ var i=sel.indexOf(o2); var l=sel.slice(); if(i>=0) l.splice(i,1); else l.push(o2); select(l); return }
    if(sel.indexOf(o2)<0) select([o2]);
    drag={kind:'move',x:ev.clientX,y:ev.clientY,start:sel.map(function(s){var g=geom(s);return [s,g.x,g.y]}),undo:styleState(sel),moved:false};
  }else if(pg){ ev.preventDefault(); var r=pg.getBoundingClientRect();
    drag={kind:'band',pg:pg,x0:ev.clientX-r.left,y0:ev.clientY-r.top,add:ev.shiftKey?sel.slice():[]}; pg.appendChild(band);
    band.style.left=drag.x0+'px';band.style.top=drag.y0+'px';band.style.width='0';band.style.height='0';band.style.display='block';
  }
});
document.addEventListener('mousemove',function(ev){
  if(!drag) return;
  var dx=(ev.clientX-drag.x)/PT, dy=(ev.clientY-drag.y)/PT;
  if(drag.kind==='move'){ drag.moved=true;
    var lead=drag.start[0], nx=snap(lead[1]+dx,ev), ny=snap(lead[2]+dy,ev), al=ev.altKey?null:alignTo(lead[0],nx,ny);
    if(al){ nx+=al.dx; ny+=al.dy }
    showGuides(lead[0].parentNode, al);
    var mx=nx-lead[1], my=ny-lead[2];
    drag.start.forEach(function(s){s[0].style.left=(s[1]+mx).toFixed(2)+'pt';s[0].style.top=(s[2]+my).toFixed(2)+'pt'}); placeGrip();
    say('moved '+Math.round(mx)+', '+Math.round(my)+' pt'+(al&&(al.gx!==null||al.gy!==null)?' — lined up with another object (Alt = free)':''));
  }else if(drag.kind==='size'){ var o=drag.o, w=Math.max(6,snap(drag.w+dx,ev)), h=Math.max(4,snap(drag.h+dy,ev));
    if(o.tagName==='IMG'){ if(!ev.shiftKey) h=w*drag.h/drag.w; o.style.width=w+'pt'; o.style.height=h+'pt' }
    else if(o.classList.contains('rule')){ o.style.width=w+'pt' }
    else if(o.tagName==='TABLE'){ o.style.transformOrigin='left top'; o.style.transform='scale('+(w/drag.w).toFixed(4)+')' }
    else { o.style.width=w+'pt'; if(!o.classList.contains('flow')&&!o.classList.contains('ins')) makeFlow(o,true) }
    placeGrip(); say('size '+Math.round(w)+' × '+Math.round(o.offsetHeight/PT)+' pt');
  }else if(drag.kind==='band'){ var r=drag.pg.getBoundingClientRect(), x=ev.clientX-r.left, y=ev.clientY-r.top;
    band.style.left=Math.min(x,drag.x0)+'px';band.style.top=Math.min(y,drag.y0)+'px';band.style.width=Math.abs(x-drag.x0)+'px';band.style.height=Math.abs(y-drag.y0)+'px';
  }
});
/* lining up: while one object is dragged, its edges and middle catch on those of the others on the page */
function alignTo(o,nx,ny){
  var pg=o.parentNode, w=o.offsetWidth/PT, h=o.offsetHeight/PT, own={x:[nx,nx+w/2,nx+w],y:[ny,ny+h/2,ny+h]};
  var tx=[pg.offsetWidth/PT/2], ty=[pg.offsetHeight/PT/2];
  $$('.obj',pg).forEach(function(q){ if(q.parentNode!==pg||sel.indexOf(q)>=0) return; var g=geom(q); tx.push(g.x,g.x+g.w/2,g.x+g.w); ty.push(g.y,g.y+g.h/2,g.y+g.h) });
  function best(mine,theirs){ var b=null; mine.forEach(function(m){theirs.forEach(function(t){var d=t-m; if(Math.abs(d)<2.4&&(b===null||Math.abs(d)<Math.abs(b.d))) b={d:d,at:t}})}); return b }
  var bx=best(own.x,tx), by=best(own.y,ty);
  return {dx:bx?bx.d:0, dy:by?by.d:0, gx:bx?bx.at:null, gy:by?by.at:null};
}
function showGuides(pg,al){
  var gv=$('#gv'), gh=$('#gh'); if(!gv||!gh) return;
  if(al&&al.gx!==null){ pg.appendChild(gv); gv.style.left=al.gx+'pt'; gv.style.display='block' } else gv.style.display='none';
  if(al&&al.gy!==null){ pg.appendChild(gh); gh.style.top=al.gy+'pt'; gh.style.display='block' } else gh.style.display='none';
}
document.addEventListener('mouseup',function(){
  showGuides(null,null);
  if(!drag) return;
  if(drag.kind==='move'&&drag.moved) remember(drag.undo);
  if(drag.kind==='size') remember(drag.undo);
  if(drag.kind==='band'){ var b=band.getBoundingClientRect(), hit=$$('.obj',drag.pg).filter(function(o){ if(o.parentNode!==drag.pg) return false; var r=o.getBoundingClientRect();
      return b.width>3&&r.left>=b.left&&r.right<=b.right&&r.top>=b.top&&r.bottom<=b.bottom});
    band.style.display='none'; select(drag.add.concat(hit)) }
  drag=null;
});

/* ---- keys ---- */
document.addEventListener('keydown',function(ev){
  var typing=ev.target.isContentEditable||/^(INPUT|SELECT|TEXTAREA)$/.test(ev.target.tagName), k=ev.key, ctrl=ev.ctrlKey||ev.metaKey;
  if(ctrl&&(k==='s'||k==='S')){ev.preventDefault();save();return}
  if(ctrl&&(k==='f'||k==='F')){ev.preventDefault();openFind();return}
  if(ctrl&&(k==='z'||k==='Z')&&!(typing&&mode==='edit')){ev.preventDefault();var u=undo.pop();if(u){u();say('undone')}return}
  if(k==='Escape'){ if(mode==='place'){setMode('edit')} else if(mode==='move'&&sel.length){select([])} else {if(document.activeElement) document.activeElement.blur(); setMode('view')} return }
  if(typing) return;
  if(ctrl&&mode==='move'&&sel.length&&/^[biuBIU]$/.test(k)){ ev.preventDefault(); style1({b:'bold',i:'italic',u:'underline'}[k.toLowerCase()]); return }
  if(!ctrl&&(k==='e'||k==='E')){ev.preventDefault();setMode('edit');return}
  if(!ctrl&&(k==='g'||k==='G')){ev.preventDefault();setMode('move');return}
  if(!ctrl&&(k==='o'||k==='O')){cycleRef();return}
  if(!ctrl&&(k==='h'||k==='H')){body.classList.toggle('hideui');return}
  if(mode!=='move'||!sel.length) return;
  var step=ev.shiftKey?7.5:0.75, d={ArrowLeft:[-step,0],ArrowRight:[step,0],ArrowUp:[0,-step],ArrowDown:[0,step]}[k];
  if(d){ev.preventDefault();remember(styleState(sel));sel.forEach(function(o){var g=geom(o);o.style.left=(g.x+d[0])+'pt';o.style.top=(g.y+d[1])+'pt'});placeGrip();return}
  if(k==='Delete'){ev.preventDefault();removeSel();return}
  if(k==='Backspace'){ev.preventDefault();resetSel();return}
  if(ctrl&&(k==='d'||k==='D')){ev.preventDefault();duplicate();return}
  if(ctrl&&k===']'){ev.preventDefault();stack(ev.shiftKey?'front':'up');return}
  if(ctrl&&k==='['){ev.preventDefault();stack(ev.shiftKey?'back':'down');return}
});
function removeSel(){ var gone=sel.map(function(o){return [o,o.parentNode,o.nextSibling]}); if(!gone.length) return;
  gone.forEach(function(g){g[1].removeChild(g[0])}); select([]);
  remember(function(){gone.forEach(function(g){g[1].insertBefore(g[0],g[2]&&g[2].parentNode===g[1]?g[2]:null)})}); say(gone.length+' removed — Ctrl+Z brings it back') }
function resetSel(){ remember(styleState(sel)); sel.forEach(function(o){var s=o.getAttribute('data-o'); if(s!==null) o.setAttribute('style',s)}); refit(sel); placeGrip(); say('put back as it was') }
function duplicate(){ var made=sel.map(function(o){var c=o.cloneNode(true);c.classList.remove('sel','sel2');var g=geom(o);c.style.left=(g.x+9)+'pt';c.style.top=(g.y+9)+'pt';c.removeAttribute('data-o');o.parentNode.appendChild(c);return c});
  remember(function(){made.forEach(function(c){if(c.parentNode) c.parentNode.removeChild(c)})}); select(made) }
function stack(how){ if(!sel.length) return; remember(styleState(sel));
  sel.forEach(function(o){ var z=parseInt(o.style.zIndex||'1',10), all=$$('.obj',o.parentNode).map(function(x){return parseInt(x.style.zIndex||'1',10)});
    o.style.zIndex= how==='front'?Math.max.apply(null,all)+1 : how==='back'?Math.max(1,Math.min.apply(null,all)-1) : how==='up'?z+1 : Math.max(1,z-1) }) }

/* ---- edit mode ---- */
document.addEventListener('focusin',function(ev){var b=boxOf(ev.target); if(b){lastBox=b; if(mode==='edit') say('editing a text box — the bar sets its size, style, colour, font and alignment; <b>Flow</b> lets it re-wrap')}});
document.addEventListener('input',function(ev){var b=boxOf(ev.target); if(b){dirty=true}});
function cur(){ return (mode==='edit'&&lastBox&&document.contains(lastBox))?[lastBox]:sel.filter(function(o){return o.classList.contains('tb')}) }
function eachBox(fn){ var l=cur(); if(!l.length){say('Click a text box first.');return} remember(styleState(l)); l.forEach(fn); refit(l); placeGrip() }
function cmd(name,val){ document.execCommand('styleWithCSS',false,true); document.execCommand(name,false,val); dirty=true }
/* Size, font, bold, italic, underline: on the words that are selected - or, with none selected, on the
   whole of the box being edited (edit mode) or of every selected box (move mode). */
var lastRange=null;
document.addEventListener('selectionchange',function(){ var s=window.getSelection(); if(!s.rangeCount) return;
  var b=boxOf(s.anchorNode); if(b){ lastRange=s.getRangeAt(0).cloneRange(); showType() } });
function someWords(){                              // the selected words, even after a click in the size box took the selection away
  if(mode!=='edit'||!lastRange||lastRange.collapsed||!document.contains(lastRange.startContainer)) return null;
  var b=boxOf(lastRange.startContainer); if(!b||b!==boxOf(lastRange.endContainer)) return null;
  var s=window.getSelection(); s.removeAllRanges(); s.addRange(lastRange); lastBox=b; return b }
function htmlState(list){ var st=list.map(function(o){return [o,o.innerHTML,o.getAttribute('style'),o.className]});
  return function(){ st.forEach(function(x){x[0].innerHTML=x[1]; x[0].setAttribute('style',x[2]||''); x[0].className=x[3]}); placeGrip(); refit(list); showType() } }
function allOf(b,fn){                              // run fn with all the text of a box selected
  var s=window.getSelection(), keep=(s.rangeCount&&mode==='edit')?s.getRangeAt(0).cloneRange():null, was=b.getAttribute('contenteditable');
  b.setAttribute('contenteditable','true'); var r=document.createRange(); r.selectNodeContents(b); s.removeAllRanges(); s.addRange(r);
  fn(b); s.removeAllRanges(); if(was===null) b.removeAttribute('contenteditable');
  if(keep&&document.contains(keep.startContainer)) s.addRange(keep) }
function typeDo(fn,reflow){                        // fn(box): called with the right words selected
  var b=someWords(), list=b?[b]:cur();
  if(!list.length){ say(mode==='move'?'Click a text box first (Shift+click for several).':'Click in a text box first.'); return }
  remember(htmlState(list));
  list.forEach(function(x){ if(reflow&&!x.classList.contains('flow')&&!x.classList.contains('ins')){ makeFlow(x,true); if(b){ b=someWords()||b } } });
  if(b){ fn(b,true); var s=window.getSelection(); if(s.rangeCount) lastRange=s.getRangeAt(0).cloneRange() } else list.forEach(function(x){ allOf(x,function(){fn(x,false)}) });
  refit(list); placeGrip(); showType(); dirty=true }
function style1(name){ typeDo(function(){ cmd(name) },false) }
function plain(){ typeDo(function(b,part){ ['bold','italic','underline'].forEach(function(n){ if(!document.queryCommandState(n)) cmd(n); cmd(n) });
  if(!part){ b.style.fontWeight='normal'; b.style.fontStyle='normal' } },false) }
function sizeNow(el){ return parseFloat(getComputedStyle(el).fontSize)/PT }
function setSize(pt,by){ pt=by?0:Math.max(3,Math.min(300,pt)); typeDo(function(b,part){
  if(part){ var el=window.getSelection().anchorNode; el=el.nodeType===1?el:el.parentNode; var to=by?sizeNow(el)*by:pt;
    cmd('fontSize','7');
    $$('font[size="7"],span',b).forEach(function(e){ var f=e.style.fontSize; if(e.tagName==='FONT'||/xxx-large/.test(f)){ e.removeAttribute('size'); e.style.fontSize=to.toFixed(2)+'pt' } });
    b.style.lineHeight='normal'; $$('.ln',b).forEach(function(l){l.style.height='';l.style.lineHeight=''}) }
  else{ var fs=parseFloat(b.style.fontSize)||sizeNow(b), f=by||pt/fs, lh=parseFloat(b.style.lineHeight)||0;
    b.style.fontSize=(fs*f).toFixed(2)+'pt'; if(lh) b.style.lineHeight=(lh*f).toFixed(2)+'pt';
    $$('*',b).forEach(function(e){ var v=e.style&&e.style.fontSize; if(v&&/pt$/.test(v)) e.style.fontSize=(parseFloat(v)*f).toFixed(2)+'pt'; else if(v&&/px$/.test(v)) e.style.fontSize=(parseFloat(v)*f).toFixed(2)+'px' }) } },true) }
function sizeBy(f){ setSize(0,f) }
function setFont(v){ typeDo(function(b,part){ cmd('fontName',v); if(!part){ b.style.fontFamily="'"+v+"'"; $$('*',b).forEach(function(e){ if(e.style&&e.style.fontFamily) e.style.fontFamily="'"+v+"'" }) } },true) }
function firstFont(el){ return (getComputedStyle(el).fontFamily.split(',')[0]||'').replace(/["']/g,'').trim() }
function showType(){                               // the bar shows the size, font and style of where you are
  var el=null, s=window.getSelection();
  if(mode==='edit'&&s.rangeCount&&boxOf(s.anchorNode)){ el=s.anchorNode; if(!s.isCollapsed&&s.getRangeAt(0).startContainer){ el=s.getRangeAt(0).startContainer;
      if(el.nodeType===3&&s.getRangeAt(0).startOffset>=el.nodeValue.length&&el.parentNode.nextSibling) el=el.parentNode.nextSibling } el=el.nodeType===1?el:el.parentNode }
  else if(mode==='move'){ var l=cur(); if(l.length){ el=l[0]; var t=document.createTreeWalker(el,NodeFilter.SHOW_TEXT,null), n; while((n=t.nextNode())){ if(n.nodeValue.trim()){el=n.parentNode;break} } } }
  var size=$('#size'), font=$('#font'); if(!el||!size){ return }
  var cs=getComputedStyle(el);
  if(document.activeElement!==size) size.value=(Math.round(sizeNow(el)*2)/2).toString();
  var name=firstFont(el), found=false; $$('option',font).forEach(function(o){ if(o.value.toLowerCase()===name.toLowerCase()||o.textContent.toLowerCase()===name.toLowerCase()){ font.value=o.value||o.textContent; found=true } });
  if(!found&&name){ var o=document.createElement('option'); o.textContent=name; font.insertBefore(o,font.children[1]); font.value=name }
  var on={bold:(parseInt(cs.fontWeight,10)||400)>=600, italic:cs.fontStyle==='italic'||cs.fontStyle==='oblique', underline:false};
  var u=el; while(u&&u!==body){ if(/underline/.test(getComputedStyle(u).textDecorationLine||'')){on.underline=true;break} if(u.classList&&u.classList.contains('tb')) break; u=u.parentNode }
  ['bold','italic','underline'].forEach(function(n){ var b=$('#bar [data-do="'+n+'"]'); if(b) b.classList.toggle('on',on[n]) }) }
(function(){                                       // the fonts this document is set in come first in the list
  var seen={}, names=[]; $$('.tb, .tb *').forEach(function(e){ var f=e.style&&e.style.fontFamily; if(!f) return; var n=f.split(',')[0].replace(/["']/g,'').trim();
    if(n&&!seen[n.toLowerCase()]){ seen[n.toLowerCase()]=1; names.push(n) } });
  if(!names.length) return; var g=document.createElement('optgroup'); g.label='In this document';
  names.sort().forEach(function(n){ var o=document.createElement('option'); o.textContent=n; g.appendChild(o) });
  var font=$('#font'), more=$('#fontmore'); font.insertBefore(g,more);
  $$('option',more).forEach(function(o){ if(seen[o.textContent.toLowerCase()]) o.remove() }) })();
function makeFlow(b,quiet){
  if(b.classList.contains('ins')) return;
  if(b.classList.contains('flow')){ if(!quiet) say('This box already flows.'); return }
  var lines=$$('.ln',b), ind=lines.map(function(l){return parseFloat(l.style.marginLeft)||0});
  lines.forEach(function(l,i){ var t=l.firstElementChild; if(t){t.style.letterSpacing='';t.style.wordSpacing='';t.style.transform=''}
    l.style.marginLeft=''; l.style.width='';
    var last=l.lastChild; while(last&&last.nodeType===1&&last.lastChild) last=last.lastChild;
    var next=lines[i+1], nt=next?next.textContent:'';
    if(next){ if(last&&last.nodeType===3&&/[a-z]-$/.test(last.nodeValue)&&/^[a-z]/.test(nt)&&l.getAttribute('data-hy')!=='0') last.nodeValue=last.nodeValue.slice(0,-1);
      else l.appendChild(document.createTextNode(' ')) } });
  b.classList.add('flow');
  if(lines.length>1){ var rest=Math.min.apply(null,ind.slice(1)); b.style.paddingLeft=rest+'pt'; b.style.textIndent=(ind[0]-rest)+'pt' }
  else if(ind.length){ b.style.paddingLeft=ind[0]+'pt' }
  if(b.getAttribute('data-just')==='1') b.style.textAlign='justify';
  if(b.getAttribute('data-al')){ b.style.textAlign=b.getAttribute('data-al'); b.style.paddingLeft=''; b.style.textIndent=''; b.style.width=b.getAttribute('data-bw')+'pt' }
  if(!b.style.width) b.style.width=b.getAttribute('data-bw')+'pt';
  dirty=true;
}
function dropBox(ev){ var pg=pageOf(ev.target); if(!pg) return; ev.preventDefault(); var r=pg.getBoundingClientRect();
  var b=document.createElement('div'); b.className='obj tb ins'+(placing==='note'?' note':''); b.setAttribute('contenteditable','true');
  b.style.cssText='left:'+((ev.clientX-r.left)/PT).toFixed(1)+'pt;top:'+((ev.clientY-r.top)/PT).toFixed(1)+'pt;width:'+(placing==='note'?140:180)+'pt;font-size:'+(placing==='note'?9:10)+'pt;line-height:12pt;z-index:'+(placing==='note'?50:5);
  b.textContent=placing==='note'?'Note':'Text'; pg.appendChild(b); remember(function(){if(b.parentNode) b.parentNode.removeChild(b)});
  setMode('edit'); b.focus(); document.execCommand('selectAll',false,null); lastBox=b }
function addImage(file){ var pg=sel.length?pageOf(sel[0]):(lastBox?pageOf(lastBox):nearestPage()); if(!file||!pg) return; var rd=new FileReader();
  rd.onload=function(){ var im=document.createElement('img'); im.className='obj pic'; im.onload=function(){ var w=Math.min(300,im.naturalWidth*0.75);
      im.style.cssText='left:36pt;top:36pt;width:'+w+'pt;height:'+(w*im.naturalHeight/im.naturalWidth).toFixed(1)+'pt;z-index:5'; if(mode!=='move') setMode('move'); select([im]); im.scrollIntoView({block:'center'}) };
    im.src=rd.result; pg.appendChild(im); remember(function(){if(im.parentNode) im.parentNode.removeChild(im)}) }; rd.readAsDataURL(file) }
function nearestPage(){ var mid=window.innerHeight/2, best=null, bd=1e9; $$('.page').forEach(function(p){var r=p.getBoundingClientRect(), d=Math.abs((r.top+r.bottom)/2-mid); if(d<bd){bd=d;best=p}}); return best }
function cycleRef(){ if(body.classList.contains('onlyref')){body.classList.remove('onlyref');say('original page hidden')}
  else if(body.classList.contains('showref')){body.classList.remove('showref');body.classList.add('onlyref');say('showing <b>only</b> the original page — O again to go back')}
  else{body.classList.add('showref');say('the original page shows faintly behind — O again for the original alone')} }

/* ---- save: the page as it now is, as a file of the same kind ---- */
function snapshot(){
  var keep={m:mode,s:sel.slice()}; setMode('view'); select([]); grip.style.display='none'; band.style.display='none';
  if(grip.parentNode!==body) body.appendChild(grip); if(band.parentNode!==body) body.appendChild(band);
  ['#gv','#gh'].forEach(function(q){var g=$(q); if(g){g.style.display='none'; if(g.parentNode!==body) body.appendChild(g)}}); findBox.style.display='none';
  var cls=body.className; body.className=cls.replace(/\b(edit|move|place|showref|onlyref|hideui|nonotes)\b/g,'').trim();
  var html='<!DOCTYPE html>\n'+document.documentElement.outerHTML; body.className=cls; if(keep.m!=='view') setMode(keep.m); return html }
function save(){
  var html=snapshot(), name=(document.title||'document').replace(/[\\/:*?"<>|]+/g,'_')+'.html';
  function down(){ var a=document.createElement('a'); a.href=URL.createObjectURL(new Blob([html],{type:'text/html'})); a.download=name; document.body.appendChild(a); a.click();
    setTimeout(function(){URL.revokeObjectURL(a.href);a.remove()},500); dirty=false; say('Saved as a download: <b>'+name+'</b> — put it over the old file to keep your changes.') }
  function write(h){ return h.createWritable().then(function(w){return w.write(html).then(function(){return w.close()})}).then(function(){dirty=false;say('Saved to <b>'+h.name+'</b>.')}) }
  if(fileHandle){ write(fileHandle).catch(down); return }
  if(window.showSaveFilePicker){ window.showSaveFilePicker({suggestedName:name,types:[{description:'Web page',accept:{'text/html':['.html']}}]})
      .then(function(h){fileHandle=h;return write(h)}).catch(function(e){ if(!e||e.name!=='AbortError') down() }) }
  else down();
}
window.addEventListener('beforeunload',function(ev){ if(dirty){ev.preventDefault();ev.returnValue=''} });

/* ---- the bar ---- */
$('#bar').addEventListener('mousedown',function(ev){ if(ev.target.tagName==='BUTTON') ev.preventDefault() });   // keep the text selection
$('#bar').addEventListener('click',function(ev){ var b=ev.target.closest('[data-do]'); if(!b) return; var a=b.getAttribute('data-do');
  if(a==='edit'||a==='move') setMode(a);
  else if(a==='find') openFind();
  else if(a==='save') save(); else if(a==='print') window.print(); else if(a==='ref') cycleRef(); else if(a==='undo'){var u=undo.pop(); if(u) u()}
  else if(a==='marks'){body.classList.toggle('nomark');dirty=true}
  else if(a==='bigger') sizeBy(1.08); else if(a==='smaller') sizeBy(1/1.08);
  else if(a==='bold'||a==='italic'||a==='underline') style1(a);
  else if(a==='plain') plain();
  else if(a==='left'||a==='center'||a==='right'||a==='justify') eachBox(function(x){ if(!x.classList.contains('flow')&&!x.classList.contains('ins')) makeFlow(x,true); x.style.textAlign=a });
  else if(a==='flow') eachBox(function(x){makeFlow(x)});
  else if(a==='flowall'){ var all=$$('.page>.tb:not(.flow):not(.ins)'); remember(function(){say('Undo of "flow all" is not kept — reload the file to go back.')}); all.forEach(function(x){makeFlow(x,true)}); say(all.length+' text boxes now re-wrap their text.') }
  else if(a==='addtext'||a==='addnote'){ body.classList.remove('edit','move'); mode='place'; placing=a==='addnote'?'note':'text'; body.classList.add('place'); say('Click on a page where the new '+(placing==='note'?'note':'text box')+' should go. Esc cancels.') }
  else if(a==='notes'){body.classList.toggle('nonotes')}
  else if(a==='word') toWord();
  else if(a==='del') removeSel(); else if(a==='reset') resetSel(); else if(a==='dup') duplicate();
  else if(a==='front'||a==='up'||a==='down'||a==='back') stack(a);
});
$('#font').addEventListener('change',function(){ var v=this.value; if(!v) return; setFont(v) });
$('#size').addEventListener('change',function(){ var v=parseFloat(this.value); if(v>0) setSize(v); this.blur() });
$('#size').addEventListener('keydown',function(ev){ if(ev.key==='Enter'){ ev.preventDefault(); this.blur() } ev.stopPropagation() });
$('#colour').addEventListener('input',function(){ var v=this.value, s=window.getSelection(); if(s&&!s.isCollapsed) cmd('foreColor',v); else eachBox(function(b){b.style.color=v}) });
$('#pick').addEventListener('change',function(){ addImage(this.files[0]); this.value='' });

/* ---- a Word file of it: the text and pictures in reading order (Word reads a web page saved as .doc) ---- */
function wordHtml(){
  var out=['<html xmlns:o="urn:schemas-microsoft-com:office:office" xmlns:w="urn:schemas-microsoft-com:office:word" xmlns="http://www.w3.org/TR/REC-html40"><head><meta charset="utf-8"><title>'+document.title+'</title>',
    '<style>@page{size:'+($('.page').offsetWidth/PT).toFixed(0)+'pt '+($('.page').offsetHeight/PT).toFixed(0)+'pt;margin:54pt} p{margin:0 0 6pt 0} td{border:1px solid #666;padding:2pt 4pt;vertical-align:top} table{border-collapse:collapse} mark{background:#fff36b}</style></head><body>'];
  function textOf(tb){ var c=tb.cloneNode(true); $$('.ln',c).forEach(function(l,i,all){ var t=l.textContent; if(i<all.length-1&&!c.classList.contains('flow')){ if(/[a-z]-$/.test(t)&&/^[a-z]/.test(all[i+1].textContent)){ var last=l.lastChild; while(last&&last.nodeType===1&&last.lastChild) last=last.lastChild; if(last&&last.nodeType===3) last.nodeValue=last.nodeValue.slice(0,-1) } else l.appendChild(document.createTextNode(' ')) } });
    $$('[style]',c).forEach(function(e){ var k=e.style, keep=''; if(k.fontWeight) keep+='font-weight:'+k.fontWeight+';'; if(k.fontStyle) keep+='font-style:'+k.fontStyle+';'; if(k.color) keep+='color:'+k.color+';'; if(k.textDecoration) keep+='text-decoration:'+k.textDecoration+';'; if(k.textDecorationLine&&!k.textDecoration) keep+='text-decoration:'+k.textDecorationLine+';'; if(/pt$/.test(k.fontSize)) keep+='font-size:'+k.fontSize+';'; if(k.fontFamily) keep+='font-family:'+k.fontFamily.replace(/"/g,"'")+';'; if(e.tagName==='IMG') keep+='width:'+k.width+';height:'+k.height+';'; e.setAttribute('style',keep) });
    return c.innerHTML }
  function para(tb){ var k=tb.style, fs=parseFloat(k.fontSize)||10; return '<p style="font-family:'+(k.fontFamily||'serif').replace(/"/g,"'")+';font-size:'+fs.toFixed(1)+'pt;'+(k.fontWeight?'font-weight:'+k.fontWeight+';':'')+(k.fontStyle?'font-style:'+k.fontStyle+';':'')+(k.textAlign?'text-align:'+k.textAlign+';':tb.getAttribute('data-just')==='1'?'text-align:justify;':tb.getAttribute('data-al')?'text-align:'+tb.getAttribute('data-al')+';':'')+'">'+textOf(tb)+'</p>' }
  $$('.page').forEach(function(pg,pi){
    var objs=$$('.obj',pg).filter(function(o){return o.parentNode===pg&&!o.classList.contains('note')&&!o.classList.contains('rule')});
    var mid=pg.offsetWidth/2, wide=function(o){return o.offsetWidth>0.6*pg.offsetWidth};
    objs.sort(function(a,b){ var ca=wide(a)?0:(a.offsetLeft+a.offsetWidth/2<mid?1:2), cb=wide(b)?0:(b.offsetLeft+b.offsetWidth/2<mid?1:2);
      if(wide(a)||wide(b)||ca===cb) return a.offsetTop-b.offsetTop||a.offsetLeft-b.offsetLeft; return ca-cb });
    if(pi) out.push('<br clear="all" style="page-break-before:always">');
    objs.forEach(function(o){
      if(o.tagName==='IMG') out.push('<p><img src="'+o.src+'" width="'+Math.round(o.offsetWidth)+'" height="'+Math.round(o.offsetHeight)+'"></p>');
      else if(o.tagName==='TABLE'){ out.push('<table>'); $$('tr',o).forEach(function(tr){ out.push('<tr>'); $$('td',tr).forEach(function(td){
            out.push('<td'+(td.colSpan>1?' colspan="'+td.colSpan+'"':'')+(td.rowSpan>1?' rowspan="'+td.rowSpan+'"':'')+' width="'+Math.round(td.offsetWidth)+'">');
            Array.prototype.forEach.call(td.children,function(c){ if(c.tagName==='IMG') out.push('<img src="'+c.src+'" width="'+Math.round(c.offsetWidth)+'" height="'+Math.round(c.offsetHeight)+'">'); else if(c.classList.contains('tb')) out.push(para(c)) });
            out.push('</td>') }); out.push('</tr>') }); out.push('</table><p></p>') }
      else if(o.classList.contains('tb')) out.push(para(o)) }) });
  out.push('</body></html>'); return out.join('\n') }
function toWord(){ var name=(document.title||'document').replace(/[\\/:*?"<>|]+/g,'_')+'.doc', a=document.createElement('a');
  a.href=URL.createObjectURL(new Blob(['\ufeff',wordHtml()],{type:'application/msword'})); a.download=name; document.body.appendChild(a); a.click();
  setTimeout(function(){URL.revokeObjectURL(a.href);a.remove()},500);
  say('Saved <b>'+name+'</b> to your downloads: the text and pictures in reading order, as flowing text. (For a Word file laid out like the page, use the program\'s own Word file.)') }

/* ---- find and replace, through every text box on every page ---- */
var findBox=$('#find');
function openFind(){ findBox.style.display='block'; if(mode!=='edit') setMode('edit'); $('#fq').focus(); $('#fq').select() }
function textNodes(){ var out=[]; $$('.tb').forEach(function(b){ var w=document.createTreeWalker(b,NodeFilter.SHOW_TEXT,null), n; while((n=w.nextNode())) out.push(n) }); return out }
function countAll(q){ var n=0; if(q) textNodes().forEach(function(t){ var i=-1; while((i=t.nodeValue.indexOf(q,i+1))>=0) n++ }); return n }
function findNext(){ var q=$('#fq').value; if(!q) return false; var nodes=textNodes(), s=window.getSelection(), from=0, off=0;
  if(s.rangeCount&&s.anchorNode){ var i=nodes.indexOf(s.focusNode); if(i>=0){from=i;off=s.focusOffset} }
  for(var k=0;k<=nodes.length;k++){ var t=nodes[(from+k)%nodes.length]; if(!t) break; var at=t.nodeValue.indexOf(q,k===0?off:0);
    if(at>=0){ var r=document.createRange(); r.setStart(t,at); r.setEnd(t,at+q.length); s.removeAllRanges(); s.addRange(r);
      var el=t.parentNode; el.scrollIntoView({block:'center'}); $('#fn').textContent=countAll(q)+' found'; return true } }
  $('#fn').textContent='not found'; return false }
function replaceOne(){ var q=$('#fq').value, s=window.getSelection(); if(!q) return;
  if(s.rangeCount&&s.toString()===q){ var r=s.getRangeAt(0), t=r.startContainer, a=r.startOffset, old=t.nodeValue, put=$('#fr').value;
    t.nodeValue=old.slice(0,a)+put+old.slice(a+q.length); remember(function(){t.nodeValue=old}); var b=boxOf(t); if(b) fitAll(b);
    var r2=document.createRange(); r2.setStart(t,a+put.length); r2.collapse(true); s.removeAllRanges(); s.addRange(r2) }
  findNext() }
function replaceAll(){ var q=$('#fq').value, put=$('#fr').value, n=0, olds=[]; if(!q) return;
  textNodes().forEach(function(t){ if(t.nodeValue.indexOf(q)>=0){ olds.push([t,t.nodeValue]); n+=t.nodeValue.split(q).length-1; t.nodeValue=t.nodeValue.split(q).join(put) } });
  if(n){ remember(function(){olds.forEach(function(o){o[0].nodeValue=o[1]});fitAll()}); fitAll() }
  $('#fn').textContent=n+' replaced'; say(n+' replaced on all pages — Ctrl+Z (outside a text box) undoes it. A phrase that runs over a line end or a change of style is not found.') }
findBox.addEventListener('click',function(ev){ var a=ev.target.getAttribute&&ev.target.getAttribute('data-f'); if(!a) return;
  if(a==='next') findNext(); else if(a==='one') replaceOne(); else if(a==='all') replaceAll(); else findBox.style.display='none' });
findBox.addEventListener('mousedown',function(ev){ if(ev.target.tagName==='BUTTON') ev.preventDefault() });
$('#fq').addEventListener('keydown',function(ev){ if(ev.key==='Enter'){ev.preventDefault();findNext()} });
$('#fq').addEventListener('input',function(){ $('#fn').textContent=this.value?countAll(this.value)+' found':'' });

say(HINTS.view);
if(document.fonts&&document.fonts.ready) document.fonts.ready.then(function(){fitAll()}); else window.addEventListener('load',function(){fitAll()});
fitAll();
window.__snapclean={setSize:setSize,setFont:setFont,style1:style1,showType:showType,wordHtml:wordHtml,fitAll:fitAll,setMode:setMode,select:select,snapshot:snapshot,makeFlow:makeFlow,replaceAll:replaceAll,findNext:findNext,alignTo:alignTo};
})();
"""

_HTML_BAR = (
    '<div id="bar"><span class="title">{title}</span>'
    '<button data-do="edit" data-mode="edit" title="Edit text in place (E)">✏ Edit text</button>'
    '<button data-do="move" data-mode="move" title="Move, resize, delete (G)">✥ Move / resize</button>'
    '<span class="sep"></span>'
    '<span class="grp t"><select id="font" title="Font - of the selected words, or of the whole box when no words are selected">'
    '<option value="">font…</option><optgroup label="Others" id="fontmore"><option>Times New Roman</option><option>Georgia</option><option>Cambria</option>'
    '<option>Palatino Linotype</option><option>Garamond</option><option>Book Antiqua</option><option>Arial</option><option>Calibri</option>'
    '<option>Segoe UI</option><option>Verdana</option><option>Tahoma</option><option>Consolas</option><option>Courier New</option></optgroup></select>'
    '<input type="number" id="size" min="3" max="300" step="0.5" title="Type size in points - type a number and press Enter. Selected words, or the whole box.">'
    '<button data-do="smaller" title="Smaller type">A−</button><button data-do="bigger" title="Larger type">A+</button>'
    '<button data-do="bold" title="Bold (Ctrl+B) - selected words, or the whole box"><b>B</b></button>'
    '<button data-do="italic" title="Italic (Ctrl+I) - selected words, or the whole box"><i>I</i></button>'
    '<button data-do="underline" title="Underline (Ctrl+U) - selected words, or the whole box"><u>U</u></button>'
    '<button data-do="plain" title="Plain: take bold, italic and underline off">T</button>'
    '<input type="color" id="colour" value="#000000" title="Colour">'
    '<button data-do="left" title="Align left">⯇</button><button data-do="center" title="Centre">≡</button><button data-do="right" title="Align right">⯈</button>'
    '<button data-do="justify" title="Justify">☰</button><span class="sep"></span></span>'
    '<span class="grp e"><button data-do="flow" title="Let this box re-wrap its text instead of keeping the printed line ends">Flow</button>'
    '<button data-do="flowall" title="Let every text box re-wrap">Flow all</button><button data-do="addtext" title="Add a text box: click, then click on a page">＋text</button>'
    '<button data-do="addnote" title="Add a note to yourself: click, then click on a page. Notes are never printed.">＋note</button>'
    '<label class="btn" title="Add a picture from a file">＋picture<input type="file" id="pick" accept="image/*" style="display:none"></label><span class="sep"></span></span>'
    '<span class="grp m"><button data-do="front" title="Bring to front (Ctrl+Shift+])">⤒</button><button data-do="up" title="Forward (Ctrl+])">⤴</button>'
    '<button data-do="down" title="Backward (Ctrl+[)">⤵</button><button data-do="back" title="Send to back (Ctrl+Shift+[)">⤓</button>'
    '<button data-do="dup" title="Duplicate (Ctrl+D)">⧉ duplicate</button><button data-do="reset" title="Put back where it was (Backspace)">↺ put back</button>'
    '<button data-do="del" title="Delete (Del)">✕ delete</button><span class="sep"></span></span>'
    '<button data-do="undo" title="Undo (Ctrl+Z)">↶ Undo</button><button data-do="ref" title="Show the original page behind, to compare (O)">◐ Original</button>'
    '<button data-do="marks" title="Show or hide the yellow marks on words the program was not sure of">▣ Marks</button>'
    '<button data-do="notes" title="Show or hide your notes">✎ Notes</button>'
    '<button data-do="find" title="Find and replace in all the text (Ctrl+F)">🔍 Find</button>'
    '<span class="sp"></span><button data-do="print" title="Print, or choose Save as PDF there, at the real page size (Ctrl+P)">🖨 Print / PDF</button>'
    '<button data-do="word" title="Save the text and pictures as a Word file (.doc): flowing text in reading order, not the exact layout">W Word</button>'
    '<button data-do="save" title="Save this page with your changes (Ctrl+S)">⤒ Save</button></div>'
    '<div id="hint"></div><div id="grip"></div><div id="band"></div><div id="gv"></div><div id="gh"></div>'
    '<div id="find"><div><input id="fq" placeholder="Find"><input id="fr" placeholder="Replace with"></div>'
    '<button data-f="next" title="Find the next one (Enter)">Next</button><button data-f="one" title="Replace this one and find the next">Replace</button>'
    '<button data-f="all" title="Replace every one, on every page">Replace all</button><button data-f="close">✕</button><span class="n" id="fn"></span></div>')

_HTML_GENERIC = {"serif": "'Times New Roman',Times,serif", "sans": "Arial,Helvetica,sans-serif", "mono": "Consolas,'Courier New',monospace"}


def _html_font(family):
    """A CSS font-family list for one of the program's font families: the family itself, look-alikes
    most computers have, then the generic kind. (Single quotes only: it goes inside style="...".)"""
    name = (family or "").strip()
    low = name.lower()
    if any(k in low for k in ("mono", "courier", "consol", "typewriter")):
        kind = "mono"
    elif any(k in low for k in ("sans", "arial", "helvet", "calibri", "verdana", "tahoma", "segoe", "franklin", "gothic", "a030", "d050")):
        kind = "sans"
    else:
        kind = "serif"
    alike = {"p052": "'Palatino Linotype','Book Antiqua',Palatino", "palatino": "'Palatino Linotype','Book Antiqua',Palatino",
             "c059": "'Century Schoolbook',Century", "nimbus roman": "'Times New Roman',Times", "freeserif": "'Times New Roman',Times",
             "baskerville": "'Baskerville Old Face',Baskerville,'Libre Baskerville'", "garamond": "Garamond,'EB Garamond'",
             "nimbus sans": "Arial,Helvetica", "freesans": "Arial,Helvetica", "liberation sans": "Arial,Helvetica",
             "liberation serif": "'Times New Roman',Times", "dejavu serif": "Georgia"}
    extra = next((v for key, v in alike.items() if key in low), "")
    quoted = "'" + re.sub(r"[\"'<>&;]", "", name) + "'" if name else ""
    return ",".join(p for p in (quoted, extra, _HTML_GENERIC[kind]) if p)


def _esc(text):
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


class _HtmlDoc:
    """The pages as one web page of movable, editable objects (see the note above _HTML_CSS)."""

    def __init__(self, path, title="", highlight=True):
        self.path, self.title, self.highlight = str(path), title or Path(path).stem, bool(highlight)
        self.pages, self.count = [], 0

    # -- pieces ------------------------------------------------------------------------------------
    def _uri(self, image):
        import base64
        data, ext = image
        kind = "jpeg" if ext in ("jpg", "jpeg") else ext
        return f"data:image/{kind};base64," + base64.b64encode(data).decode("ascii")

    def _line(self, fl, k, left_px, default):
        """One printed line: its words, each in its own style, marked where the program was not sure."""
        words = fl["text"].split()
        if not words:
            return ""
        looks = fl["styles"] if fl.get("styles") and len(fl["styles"]) == len(words) else [None] * len(words)
        oks = fl["oks"] if fl.get("oks") and len(fl["oks"]) == len(words) else [bool(fl.get("ok"))] * len(words)
        pics = fl.get("pics") or {}
        runs = []                                       # [(style, sure, html)]
        for i, word in enumerate(words):
            look = looks[i] if looks[i] else default
            sure = bool(oks[i]) or not self.highlight
            if i in pics:
                data, wide, tall, drop = pics[i]
                piece = (f'<img class="wp" alt="{_esc(word)}" src="{self._uri((data, "png"))}" '
                         f'style="width:{wide:.3f}em;height:{tall:.3f}em;vertical-align:{-drop:.3f}em">')
                sure = True
            else:
                piece = _esc(word)
            if runs and runs[-1][0] == look and runs[-1][1] == sure:
                runs[-1][2].append(piece)
            else:
                runs.append((look, sure, [piece]))
        out = []
        for j, (look, sure, pieces) in enumerate(runs):
            text = " ".join(pieces) + (" " if j < len(runs) - 1 else "")
            css = []
            if look != default:
                if look[0] != default[0]:
                    css.append(f"font-family:{_html_font(look[0])}")
                css.append("font-weight:" + ("bold" if look[1] else "normal"))
                css.append("font-style:" + ("italic" if look[2] else "normal"))
            if not sure:
                text = f"<mark>{text}</mark>"
            out.append(f'<span style="{";".join(css)}">{text}</span>' if css else text)
        wide = (fl["box"][2] - fl["box"][0]) * k
        size = ""
        return (f'<span class="ln" data-w="{wide:.2f}"' + (' data-j="1"' if fl.get("_full") else "") +
                f' style="margin-left:{max(0.0, (fl["box"][0] - left_px) * k):.2f}pt{size}"><span class="t">{"".join(out)}</span></span>')

    def _para(self, b, k, ox, oy, cls="obj tb"):
        """A paragraph as a text box. ox, oy: the pixel the box's position is measured from."""
        size = b["size"] * k
        pitch = (b["pitch"] if b["pitch"] > 0 else 1.2 * b["size"]) * k
        lines = b["lines"]
        x0 = min(fl["box"][0] for fl in lines)
        x1 = max(fl["box"][2] for fl in lines)
        widest = max(fl["box"][2] - fl["box"][0] for fl in lines)
        for i, fl in enumerate(lines):                  # a full line of a justified paragraph is spread to its width
            fl["_full"] = bool(b.get("justified")) and i < len(lines) - 1 and fl["box"][2] - fl["box"][0] >= 0.93 * widest
        # the first baseline sits where it does on the page: a line box of height L with type of size S
        # has its baseline L/2 + 0.34 S below its top
        top = lines[0]["base"] * k - (pitch / 2 + 0.34 * size)
        default = (b["family"], bool(b["bold"]), bool(b["italic"]))
        r, g, bl = (int(round(255 * v)) for v in b.get("colour", (0, 0, 0)))
        align = b.get("align", "left") if b.get("col") else "left"
        if align != "left":                             # the box reaches the edges the text is centred between
            give = max(0.0, min(x0 - b["col"][0], b["col"][1] - x1)) if align == "center" else max(0.0, x0 - b["col"][0])
            x0 -= give
            x1 += give if align == "center" else 0.0
        css = [f"left:{(x0 - ox) * k:.2f}pt", f"top:{top - oy * k:.2f}pt", f"font-family:{_html_font(b['family'])}",
               f"font-size:{size:.2f}pt", f"line-height:{pitch:.2f}pt"]
        if b["bold"]:
            css.append("font-weight:bold")
        if b["italic"]:
            css.append("font-style:italic")
        if (r, g, bl) != (0, 0, 0):
            css.append(f"color:#{r:02x}{g:02x}{bl:02x}")
        style = ";".join(css)
        body = "".join(self._line(fl, k, x0, default) for fl in lines)
        for fl in lines:
            fl.pop("_full", None)
        return (f'<div class="{cls}" data-bw="{(x1 - x0) * k + 0.25 * size:.1f}"' + (' data-just="1"' if b.get("justified") else "") +
                (f' data-al="{align}"' if align != "left" else "") + f' data-o="{style}" style="{style}">{body}</div>')

    def _figure(self, b, k, ox, oy, cls="obj pic"):
        x0, y0, x1, y1 = b["box"]
        style = f"left:{(x0 - ox) * k:.2f}pt;top:{(y0 - oy) * k:.2f}pt;width:{(x1 - x0) * k:.2f}pt;height:{(y1 - y0) * k:.2f}pt"
        return f'<img class="{cls}" alt="" draggable="false" data-o="{style}" style="{style}" src="{self._uri(b["image"])}">'

    def _rule(self, b, k):
        x0, y0, x1, y1 = b["box"]
        r, g, bl = b.get("colour", (0, 0, 0))
        weight = max(0.5, min(3.0, b.get("weight", 1.0) * k))
        style = (f"left:{x0 * k:.2f}pt;top:{(y0 + y1) / 2 * k - weight / 2:.2f}pt;width:{(x1 - x0) * k:.2f}pt;height:{weight:.2f}pt;"
                 f"background:#{int(r):02x}{int(g):02x}{int(bl):02x}")
        return f'<div class="obj rule" data-o="{style}" style="{style}"></div>'

    def _table(self, b, k):
        xs, ys = b["xs"], b["ys"]
        r, g, bl = b["rule"]
        edge = f"0.5pt solid #{int(r):02x}{int(g):02x}{int(bl):02x}"
        span, covered, pics = b.get("span") or {}, b.get("covered") or {}, b.get("pics") or {}
        style = f"left:{xs[0] * k:.2f}pt;top:{ys[0] * k:.2f}pt;width:{(xs[-1] - xs[0]) * k:.2f}pt"
        out = [f'<table class="obj tbl" data-o="{style}" style="{style}"><colgroup>' +
               "".join(f'<col style="width:{(xs[i + 1] - xs[i]) * k:.2f}pt">' for i in range(len(xs) - 1)) + '</colgroup>']
        for ri in range(len(ys) - 1):
            out.append(f'<tr style="height:{(ys[ri + 1] - ys[ri]) * k:.2f}pt">')
            for ci in range(len(xs) - 1):
                if (ri, ci) in covered:
                    continue
                rs, cs = span.get((ri, ci), (1, 1))
                fill = b["fills"][ri][ci]
                css = f"border:{edge};height:{(ys[ri + rs] - ys[ri]) * k:.2f}pt" + \
                    (f";background:#{fill[0]:02x}{fill[1]:02x}{fill[2]:02x}" if fill else "")
                out.append(f'<td style="{css}"' + (f' colspan="{cs}"' if cs > 1 else "") + (f' rowspan="{rs}"' if rs > 1 else "") + ">")
                if (ri, ci) in pics:
                    out.append(self._figure(pics[(ri, ci)], k, xs[ci], ys[ri], cls="pic"))
                else:
                    for p in sorted(_set_alignment(_paragraphs(b["cells"][ri][ci]), (xs[ci], xs[ci + (b.get("span") or {}).get((ri, ci), (1, 1))[1]])), key=lambda p: p["box"][1]):
                        out.append(self._para(p, k, xs[ci], ys[ri], cls="tb"))
                out.append("</td>")
            out.append("</tr>")
        out.append("</table>")
        return "".join(out)

    # -- pages -------------------------------------------------------------------------------------
    def add_page(self, w, h, k, blocks, reference=None):
        """w, h: page size in pixels. k: pixels -> points. blocks: from _layout_page (None: the page as
        one picture). reference: a small picture of the original page, kept behind for comparing."""
        self.count += 1
        out = [f'<div class="page" data-page="{self.count}" style="width:{w * k:.2f}pt;height:{h * k:.2f}pt">',
               f'<span class="pgno">{self.count}</span>']
        if reference is not None:
            out.append(f'<img class="ref" alt="" src="{self._uri(reference)}">')
        for b in sorted(blocks or [], key=lambda b: (b["box"][1], b["box"][0])):
            if b["kind"] == "para":
                out.append(self._para(b, k, 0, 0))
            elif b["kind"] == "figure":
                out.append(self._figure(b, k, 0, 0))
            elif b["kind"] == "rule":
                out.append(self._rule(b, k))
            elif b["kind"] == "table":
                out.append(self._table(b, k))
        out.append("</div>")
        self.pages.append("".join(out))
        self.size = (w * k, h * k)

    def _own_fonts(self):
        """@font-face rules carrying the program's fetched fonts that this document uses, so the page
        shows in them on any computer (their licence, the SIL Open Font License, allows embedding)."""
        import base64
        from PIL import ImageFont
        used, out = "".join(self.pages), []
        folder = fonts_folder()
        for f in (sorted(folder.glob("*.ttf")) if folder.is_dir() else []):
            try:
                family, style = ImageFont.truetype(str(f), 12).getname()
            except Exception:
                continue
            if f"'{family}'" not in used:
                continue
            low = (style or "").lower()
            out.append(f"@font-face{{font-family:'{family}';font-weight:{'bold' if 'bold' in low else 'normal'};"
                       f"font-style:{'italic' if 'italic' in low or 'oblique' in low else 'normal'};"
                       f"src:url(data:font/ttf;base64,{base64.b64encode(f.read_bytes()).decode('ascii')}) format('truetype')}}")
        return "".join(out)

    def save(self):
        wp, hp = getattr(self, "size", (612.0, 792.0))
        head = (f'<!DOCTYPE html>\n<html lang="en"><head><meta charset="utf-8"><title>{_esc(self.title)}</title>'
                f'<meta name="generator" content="SnapClean"><meta name="viewport" content="width=device-width, initial-scale=1">'
                f'<style>@page{{size:{wp:.1f}pt {hp:.1f}pt;margin:0}}{self._own_fonts()}{_HTML_CSS}</style></head><body>')
        with open(self.path, "w", encoding="utf-8", newline="\n") as f:
            f.write(head)
            f.write(_HTML_BAR.replace("{title}", _esc(self.title)))
            for page in self.pages:
                f.write("\n" + page)
            f.write("\n<script>" + _HTML_JS + "</script></body></html>\n")


def _reference_picture(rgb, widest=1000):
    """A small JPEG of the original page, for the web page's "show the original behind" switch."""
    h, w = rgb.shape[:2]
    if w > widest:
        rgb = cv2.resize(rgb, (widest, int(round(h * widest / w))), interpolation=cv2.INTER_AREA)
    ok, jpg = cv2.imencode(".jpg", np.ascontiguousarray(rgb[..., ::-1]), [cv2.IMWRITE_JPEG_QUALITY, 60])
    return (jpg.tobytes(), "jpg") if ok else None


# ---- Word file, structured: the document's content as a document, not as a copy of its pages -------------
#
# The other Word layouts rebuild each page where it stood. This one reads the pages for what they are made
# of - headings, paragraphs, list items, tables, pictures, captions, running heads - and writes one flowing
# document: real heading styles (so Word shows an outline and can build a table of contents), paragraphs
# joined across the columns and pages that cut them, running heads and page numbers taken out of the text
# and a page number put in the footer, one set of styles for everything. It no longer matches the original
# page for page; that is the point of it.

_PAGE_NUMBER = re.compile(r"^\s*(page\s+)?([0-9A-Za-z]{1,4}\s*[-–—]\s*)?\d{1,4}\s*$|^\s*[ivxlc]{1,7}\s*$|^\s*(19|20)\d\d\s+Edition\s*$", re.I)
_ITEM_START = re.compile(r"^(\([a-z0-9]{1,3}\)|[a-z]\.|[0-9]{1,2}[.)])\s+\S")
_SENTENCE_END = (".", "!", "?", ":", ";", "”", '"', ")", "]", "’")


class _DocxStructured(_DocxFlow):
    def __init__(self, path, highlight=True):
        super().__init__(path, highlight, keep_lines=False)
        self.pages = []                 # (w, h, k, blocks)
        self.report = {}

    def add_page(self, w, h, k, blocks, whole=None):
        self.pages.append((w, h, k, blocks or []))

    # -- reading the pages ------------------------------------------------------------------------------
    @staticmethod
    def _text(b):
        return " ".join(fl["text"].strip() for fl in b["lines"]).strip()

    def _ordered(self, page_no, w, h, k, blocks):
        """A page's blocks in reading order: what spans the page in its place, the columns between left to right."""
        blocks = [b for b in blocks if b["kind"] in ("para", "table", "figure")]
        if not blocks:
            return []
        x0, x1 = min(b["box"][0] for b in blocks), max(b["box"][2] for b in blocks)
        wide, mid = max(1.0, x1 - x0), (x0 + x1) / 2.0
        two = sum(1 for b in blocks if b["kind"] == "para" and b["box"][2] - b["box"][0] < 0.56 * wide
                  and len(b["lines"]) >= 2) >= 3                      # is this a page of columns at all?
        out, pending = [], []

        def flush():
            for col in (1, 2):
                side = sorted((b for b in pending if (1 if (b["box"][0] + b["box"][2]) / 2 < mid else 2) == col),
                              key=lambda b: (b["box"][1], b["box"][0]))
                edge = min((b["box"][0] for b in side if b["kind"] == "para"), default=0.0)
                out.extend({"b": b, "page": page_no, "col": col, "k": k, "w": w, "h": h, "edge": edge} for b in side)
            pending.clear()

        for b in sorted(blocks, key=lambda b: (b["box"][1], b["box"][0])):
            across = not two or b["box"][2] - b["box"][0] >= 0.62 * wide or \
                (b["box"][0] < mid - 0.12 * wide and b["box"][2] > mid + 0.12 * wide)
            if across:
                flush()
                out.append({"b": b, "page": page_no, "col": 0, "k": k, "w": w, "h": h, "edge": x0})
            else:
                pending.append(b)
        flush()
        return out

    def _furniture(self, items):
        """Running heads, running feet and page numbers: a short line standing alone at the same height at
        the top or the foot of page after page. Returns the ids of those items and the commonest wording."""
        pages = {it["page"] for it in items}
        if len(pages) < 3:
            return set(), ""
        gone, words = set(), {}
        for top in (True, False):
            cands = []
            for it in items:
                b = it["b"]
                if b["kind"] != "para" or len(b["lines"]) > 2 or len(self._text(b)) > 90:
                    continue
                y = (b["box"][1] + b["box"][3]) / 2.0 / it["h"]
                if (top and y < 0.10) or (not top and y > 0.915):
                    cands.append((round(y / 0.012), it))
            if not cands:
                continue
            levels = {}
            for lv, it in cands:
                levels.setdefault(lv, set()).add(it["page"])
            for lv, on in levels.items():
                near = on | levels.get(lv - 1, set()) | levels.get(lv + 1, set())
                if len(near) >= max(3, 0.4 * len(pages)):
                    for lv2, it in cands:
                        if abs(lv2 - lv) <= 1:
                            gone.add(id(it))
                            key = re.sub(r"[\d]+", "", self._text(it["b"])).strip(" -–—|.").strip()
                            if sum(ch.isalpha() for ch in key) >= 6 and len(key.split()) >= 2:
                                words[key] = words.get(key, 0) + 1
        for it in items:
            b = it["b"]
            if b["kind"] == "para" and len(b["lines"]) == 1 and id(it) not in gone:
                y = (b["box"][1] + b["box"][3]) / 2.0 / it["h"]
                if (y < 0.09 or y > 0.90) and _PAGE_NUMBER.match(self._text(b)):
                    gone.add(id(it))
        title = max(words, key=words.get) if words and max(words.values()) >= max(3, 0.5 * len(pages)) else ""
        return gone, title

    # -- writing ----------------------------------------------------------------------------------------
    def _run_props(self, bold, italic, base, family=None, mark=False, size_pt=None):
        """Only what differs from the paragraph's style."""
        out = ""
        if family:
            font = _xml(family)
            out += f'<w:rFonts w:ascii="{font}" w:hAnsi="{font}" w:cs="{font}"/>'
        if bold != base[0]:
            out += '<w:b/><w:bCs/>' if bold else '<w:b w:val="0"/><w:bCs w:val="0"/>'
        if italic != base[1]:
            out += '<w:i/><w:iCs/>' if italic else '<w:i w:val="0"/><w:iCs w:val="0"/>'
        if size_pt:
            out += f'<w:sz w:val="{int(round(size_pt * 2))}"/><w:szCs w:val="{int(round(size_pt * 2))}"/>'
        if mark and self.highlight:
            out += '<w:highlight w:val="yellow"/>'
        return f'<w:rPr>{out}</w:rPr>' if out else ''

    def _runs(self, lines, base, body_family, size_pt, skip_first=False, own_size=None):
        """The words of a paragraph's lines as runs: line ends closed up (a word divided at a line end made
        whole again), each word in its own weight and slant, unsure words marked."""
        words = []                                      # [text, bold, italic, sure, family, picture]
        for fl in lines:
            toks = fl["text"].split()
            looks = fl["styles"] if fl.get("styles") and len(fl["styles"]) == len(toks) else [None] * len(toks)
            oks = fl["oks"] if fl.get("oks") and len(fl["oks"]) == len(toks) else [bool(fl.get("ok"))] * len(toks)
            pics = fl.get("pics") or {}
            for i, tok in enumerate(toks):
                look = looks[i] or (fl.get("family"), bool(fl.get("bold")), bool(fl.get("italic")))
                item = [tok, bool(look[1]), bool(look[2]), bool(oks[i]), look[0], pics.get(i)]
                if i == 0 and words and words[-1][5] is None and item[5] is None:
                    last = words[-1][0]
                    if last.endswith("-") and len(last) > 2 and tok[:1].islower():
                        if known_word(_core(last[:-1] + tok)[1]) or not known_word(_core(last[:-1])[1]):
                            words[-1][0] = last[:-1] + tok          # "protec-" + "tive": protective
                        else:
                            words[-1][0] = last + tok               # "self-" + "contained" keeps its hyphen
                        words[-1][3] = words[-1][3] and item[3]
                        continue
                words.append(item)
        if skip_first and words:
            words = words[1:]
        out, group = [], []

        def close():
            if group:
                text = " ".join(g[0] for g in group)
                g = group[0]
                fam = g[4] if g[4] and body_family and g[4] != body_family else None
                out.append(f'<w:r>{self._run_props(g[1], g[2], base, fam, not g[3], own_size)}<w:t xml:space="preserve">{_xml(text)} </w:t></w:r>')
                group.clear()

        for wd in words:
            if wd[5] is not None:
                close()
                out.append(self._word_pic(wd[5], size_pt, 1.3 * size_pt))
                out.append('<w:r><w:t xml:space="preserve"> </w:t></w:r>')
                continue
            if group and (group[-1][1], group[-1][2], group[-1][3], group[-1][4]) != (wd[1], wd[2], wd[3], wd[4]):
                close()
            group.append(wd)
        close()
        return "".join(out)

    def _picture(self, block, k, room_pt, centre=True):
        """A picture paragraph, no wider than the text."""
        x0, y0, x1, y1 = block["box"]
        wide, tall = (x1 - x0) * k, (y1 - y0) * k
        scale = min(1.0, room_pt / max(wide, 1.0), 620.0 / max(tall, 1.0))
        fake = dict(block, box=(0, 0, (x1 - x0) * scale, (y1 - y0) * scale))
        xml = self._figure(fake, k, 6.0, 0)
        return xml.replace('<w:ind w:left="0"/>', '<w:jc w:val="center"/>' if centre else '<w:ind w:left="0"/>', 1) \
            .replace('w:after="0"', 'w:after="120"', 1)

    def _table_xml(self, b, k, room_pt, body_family, size_pt):
        xs, ys = b["xs"], b["ys"]
        total = max(1.0, (xs[-1] - xs[0]) * k)
        scale = min(1.0, room_pt / total)
        widths = [int(round((xs[i + 1] - xs[i]) * k * scale * 20)) for i in range(len(xs) - 1)]
        r, g, bl = (int(v) for v in b["rule"])
        edge = f'w:val="single" w:sz="4" w:space="0" w:color="{r:02X}{g:02X}{bl:02X}"'
        span, covered, pics = b.get("span") or {}, b.get("covered") or {}, b.get("pics") or {}
        out = ['<w:tbl><w:tblPr><w:tblW w:w="0" w:type="auto"/><w:jc w:val="center"/><w:tblBorders>'
               + "".join(f'<w:{s} {edge}/>' for s in ("top", "left", "bottom", "right", "insideH", "insideV"))
               + '</w:tblBorders><w:tblLayout w:type="fixed"/><w:tblCellMar><w:left w:w="70" w:type="dxa"/>'
               '<w:right w:w="70" w:type="dxa"/></w:tblCellMar></w:tblPr><w:tblGrid>'
               + "".join(f'<w:gridCol w:w="{v}"/>' for v in widths) + '</w:tblGrid>']
        for ri in range(len(ys) - 1):
            out.append('<w:tr>')
            for ci in range(len(xs) - 1):
                merge, wide = "", widths[ci]
                if (ri, ci) in covered:
                    r0, c0 = covered[(ri, ci)]
                    if ci != c0:
                        continue
                    rs, cs = span[(r0, c0)]
                    out.append(f'<w:tc><w:tcPr><w:tcW w:w="{sum(widths[c0:c0 + cs])}" w:type="dxa"/>'
                               + (f'<w:gridSpan w:val="{cs}"/>' if cs > 1 else '') + '<w:vMerge/></w:tcPr><w:p><w:pPr>'
                               '<w:pStyle w:val="TableText"/></w:pPr></w:p></w:tc>')
                    continue
                rs, cs = span.get((ri, ci), (1, 1))
                wide = sum(widths[ci:ci + cs])
                merge = (f'<w:gridSpan w:val="{cs}"/>' if cs > 1 else '') + ('<w:vMerge w:val="restart"/>' if rs > 1 else '')
                fill = b["fills"][ri][ci]
                shade = f'<w:shd w:val="clear" w:color="auto" w:fill="{fill[0]:02X}{fill[1]:02X}{fill[2]:02X}"/>' if fill else ''
                out.append(f'<w:tc><w:tcPr><w:tcW w:w="{wide}" w:type="dxa"/>{merge}{shade}</w:tcPr>')
                if (ri, ci) in pics:
                    out.append(self._picture(pics[(ri, ci)], k * scale, wide / 20.0 - 8, centre=False).replace('w:before="120"', 'w:before="0"'))
                else:
                    paras = sorted(_set_alignment(_paragraphs(b["cells"][ri][ci]), (xs[ci], xs[ci + (b.get("span") or {}).get((ri, ci), (1, 1))[1]])), key=lambda p: p["box"][1])
                    for p in paras:
                        base = (bool(p["bold"]), bool(p["italic"]))
                        out.append('<w:p><w:pPr><w:pStyle w:val="TableText"/>'
                                   + (f'<w:jc w:val="{p["align"]}"/>' if p.get("align") in ("center", "right") else '') + '</w:pPr>'
                                   + self._runs(p["lines"], (False, False), body_family, size_pt) + '</w:p>')
                    if not paras:
                        out.append('<w:p><w:pPr><w:pStyle w:val="TableText"/></w:pPr></w:p>')
                out.append('</w:tc>')
            out.append('</w:tr>')
        out.append('</w:tbl><w:p><w:pPr><w:spacing w:before="0" w:after="60"/></w:pPr></w:p>')
        return "".join(out)

    def save(self):
        items = []
        for n, (w, h, k, blocks) in enumerate(self.pages, start=1):
            items += self._ordered(n, w, h, k, blocks)
        gone, title = self._furniture(items)
        items = [it for it in items if id(it) not in gone]
        paras = [it for it in items if it["b"]["kind"] == "para"]
        # the body type: the size and family most of the text is set in
        sizes, fams, just = {}, {}, [0, 0]
        for it in paras:
            b, n = it["b"], len(self._text(it["b"]))
            pt = round(b["size"] * it["k"] * 2) / 2.0
            sizes[pt] = sizes.get(pt, 0) + n
            if b.get("family"):
                fams[b["family"]] = fams.get(b["family"], 0) + n
            if len(b["lines"]) >= 3:
                just[1 if b.get("justified") else 0] += 1
        body_pt = max(sizes, key=sizes.get) if sizes else 10.0
        body_pt = float(np.clip(body_pt, 6.0, 14.0))
        grow = max(1.0, 10.5 / body_pt)                  # small two-column type, set the full width, is hard to read
        body_pt *= grow
        body_family = max(fams, key=fams.get) if fams else self.default_font
        justified = just[1] > just[0]

        # what each paragraph is
        counts = {"h1": 0, "h2": 0, "h3": 0, "list": 0, "caption": 0, "body": 0, "joined": 0}
        for it in paras:
            b = it["b"]
            text = self._text(b)
            pt = b["size"] * it["k"] * grow
            first = b["lines"][0]
            toks = text.split()
            bold_share = 0.0
            n_all = b_all = 0
            for fl in b["lines"]:
                ws = fl["text"].split()
                looks = fl["styles"] if fl.get("styles") and len(fl["styles"]) == len(ws) else [None] * len(ws)
                for wd, look in zip(ws, looks):
                    n_all += len(wd)
                    b_all += len(wd) if (look[1] if look else fl.get("bold")) else 0
            bold_share = b_all / max(1, n_all)
            caps = sum(ch.isupper() for ch in text) >= 0.7 * max(1, sum(ch.isalpha() for ch in text)) and sum(ch.isalpha() for ch in text) >= 4
            col_w = (it["w"] - 2 * 0) * 1.0
            mid_gap = b.get("align") == "center"
            it["kind"] = "body"
            if _CAPTION.match(text) and len(text) <= 220:
                it["kind"] = "caption"
            elif _starts_item(first) or (bold_share < 0.5 and _ITEM_START.match(text)):
                it["kind"] = "list"
                it["level"] = int(np.clip(round((first["box"][0] - it["edge"]) / max(1.6 * b["size"], 1.0)), 0, 3))
            elif len(b["lines"]) <= 3 and len(text) <= 150 and len(toks) >= 1 and sum(ch.isalpha() for ch in text) >= 3:
                big = pt >= 1.3 * body_pt
                larger = pt >= 1.12 * body_pt
                if big or (larger and (bold_share >= 0.6 or caps or mid_gap)):
                    it["kind"] = "h1" if big else "h2"
                elif caps and mid_gap and len(text) <= 80 and bold_share >= 0.5:
                    it["kind"] = "h2"
                elif bold_share >= 0.9 and len(b["lines"]) <= 2 and len(text) <= 110 and not text.endswith((",", ";")):
                    it["kind"] = "h3"
            counts[it["kind"]] += 1

        # paragraphs cut by the end of a column or a page: joined again
        merged = []
        last_para = None
        for it in items:
            if it["b"]["kind"] == "para" and it.get("kind") == "body" and last_para is not None \
                    and last_para.get("kind") in ("body", "list"):
                before, after = self._text(last_para["b"]), self._text(it["b"])
                first_line = it["b"]["lines"][0]
                starts_new = it["b"].get("first", it["b"]["box"][0]) > it["b"].get("body", it["b"]["box"][0]) + 0.8 * it["b"]["size"]
                moved = (it["page"], it["col"]) != (last_para["page"], last_para["col"])
                if before and after and (before.endswith("-") and after[:1].islower() or (
                        not before.endswith(_SENTENCE_END) and (after[:1].islower() or (moved and not starts_new and after[:1].isdigit())))):
                    last_para["more"] = last_para.get("more", []) + it["b"]["lines"]
                    counts["joined"] += 1
                    counts["body"] -= 1
                    continue
            merged.append(it)
            if it["b"]["kind"] == "para":
                last_para = it if it.get("kind") in ("body", "list") else None
        items, merged = merged, []
        for it in items:
            prev = merged[-1] if merged else None
            if prev is not None and it["b"]["kind"] == "para" and prev["b"]["kind"] == "para" and it["page"] == prev["page"] \
                    and it["col"] == prev["col"] and -1.3 * prev["b"]["size"] <= it["b"]["box"][1] - prev["b"]["box"][3] <= 1.6 * prev["b"]["size"] \
                    and "more" not in prev:
                kinds = (prev.get("kind"), it.get("kind"))
                if os.environ.get("SNAPCLEAN_DEBUG_STRUCT") and kinds == ("h3", "body"):
                    print("RUNIN", repr(self._text(prev["b"])[:40]), round((it["b"]["box"][1] - prev["b"]["box"][3]) / prev["b"]["size"], 2),
                          round((it["b"]["box"][2] - prev["b"]["lines"][-1]["box"][2]) / prev["b"]["size"], 2))
                if kinds == ("h3", "body") and not self._text(prev["b"]).endswith(_SENTENCE_END) \
                        and it["b"]["box"][1] - prev["b"]["box"][3] <= 0.5 * prev["b"]["size"] \
                        and prev["b"]["lines"][-1]["box"][2] >= it["b"]["box"][2] - 2.0 * prev["b"]["size"] \
                        and not _ITEM_START.match(self._text(it["b"])):
                    # a bold run-in title that ran on to a second line: it is the start of the paragraph
                    prev["kind"] = "body"
                    prev["more"] = list(it["b"]["lines"]) + it.get("more", [])
                    counts["h3"] -= 1
                    continue
                same = abs(it["b"]["size"] - prev["b"]["size"]) <= 0.08 * prev["b"]["size"]
                if (kinds in (("h1", "h1"), ("h2", "h2")) and same) or \
                        (kinds[0] == kinds[1] and kinds[0] in ("body", "h3") and same and prev["b"].get("align") == "center"
                         and it["b"].get("align") == "center" and bool(prev["b"]["bold"]) == bool(it["b"]["bold"])
                         and not self._text(prev["b"]).endswith((".", "!", "?"))) or \
                        (kinds[0] == "h3" and kinds[1] in ("h3", "body") and len(self._text(it["b"]).split()) <= 4
                         and not self._text(prev["b"]).endswith(_SENTENCE_END) and not _ITEM_START.match(self._text(it["b"]))
                         and it["b"]["box"][1] - prev["b"]["box"][3] <= 0.8 * prev["b"]["size"]) or \
                        (kinds[0] == "caption" and len(self._text(prev["b"]).split()) <= 2 and kinds[1] in ("h3", "body")
                         and len(it["b"]["lines"]) <= 3 and len(self._text(it["b"])) <= 160):
                    prev["more"] = list(it["b"]["lines"])
                    counts[kinds[1]] -= 1
                    continue
            merged.append(it)
        items = merged

        # the page: the original's size, ordinary margins
        w, h, k, _ = self.pages[0] if self.pages else (612, 792, 1.0, [])
        wp, hp = w * k, h * k
        margin = 72.0 if wp >= 540 else 54.0
        room = wp - 2 * margin
        heads = {lv: [it["b"]["size"] * it["k"] * grow for it in items if it.get("kind") == lv] for lv in ("h1", "h2", "h3")}
        hsize = {"h1": max(body_pt * 1.5, float(np.median(heads["h1"])) if heads["h1"] else 0),
                 "h2": max(body_pt * 1.2, float(np.median(heads["h2"])) if heads["h2"] else 0),
                 "h3": max(body_pt, float(np.median(heads["h3"])) if heads["h3"] else 0)}
        body = []
        for it in items:
            b, kk = it["b"], it["k"]
            if b["kind"] == "figure":
                body.append(self._picture(b, kk, room))
                continue
            if b["kind"] == "table":
                body.append(self._table_xml(b, kk, room, body_family, body_pt))
                continue
            kind = it.get("kind", "body")
            lines = b["lines"] + it.get("more", [])
            jc = f'<w:jc w:val="{b["align"]}"/>' if b.get("align") in ("center", "right") else ''
            counts["centred"] = counts.get("centred", 0) + (b.get("align") == "center")
            counts["right"] = counts.get("right", 0) + (b.get("align") == "right")
            if kind in ("h1", "h2", "h3"):
                style = {"h1": "Heading1", "h2": "Heading2", "h3": "Heading3"}[kind]
                body.append(f'<w:p><w:pPr><w:pStyle w:val="{style}"/>{jc}</w:pPr>'
                            + self._runs(lines, (True, False), body_family, hsize[kind]) + '</w:p>')
            elif kind == "caption":
                body.append('<w:p><w:pPr><w:pStyle w:val="Caption"/></w:pPr>' + self._runs(lines, (True, False), body_family, body_pt) + '</w:p>')
            elif kind == "list":
                marker = lines[0]["text"].split()[0]
                left = int(round((0.25 + 0.25 * it.get("level", 0)) * 1440 + 0.3 * 1440))
                hang = int(round(0.3 * 1440 + 30 * max(0, len(marker) - 3)))
                body.append(f'<w:p><w:pPr><w:pStyle w:val="ListItem"/><w:ind w:left="{left}" w:hanging="{hang}"/></w:pPr>'
                            f'<w:r><w:t xml:space="preserve">{_xml(marker)}</w:t></w:r><w:r><w:tab/></w:r>'
                            + self._runs(lines, (False, False), body_family, body_pt, skip_first=True) + '</w:p>')
            else:
                indent = b.get("first", b["box"][0]) > b.get("body", b["box"][0]) + 0.8 * b["size"]
                base = (False, False)
                extra = jc if jc else '<w:ind w:firstLine="240"/>' if indent else ''

                size_pt = b["size"] * kk * grow
                # small print (a note, a footnote) keeps its size
                runs = self._runs(lines, base, body_family, body_pt, own_size=size_pt if size_pt <= 0.86 * body_pt else None)
                body.append(f'<w:p><w:pPr><w:pStyle w:val="Normal"/>{extra}</w:pPr>' + runs + '</w:p>')
        if os.environ.get("SNAPCLEAN_DEBUG_STRUCT"):
            for it in items:
                b = it["b"]
                if b["kind"] == "para":
                    print(it["page"], it["col"], it.get("kind"), [round(v / it["h"], 3) for v in (b["box"][1], b["box"][3])], repr(self._text(b)[:50]))
        self.report = dict(counts, pages=len(self.pages), running=len(gone), title=title)

        # the package
        head = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
        font = _xml(body_family)
        half = int(round(body_pt * 2))

        def style(sid, name, ppr, rpr, based="Normal", nxt="Normal", outline=None):
            lvl = f'<w:outlineLvl w:val="{outline}"/>' if outline is not None else ''
            return (f'<w:style w:type="paragraph"' + (' w:default="1"' if sid == "Normal" else '') + f' w:styleId="{sid}"><w:name w:val="{name}"/>'
                    + (f'<w:basedOn w:val="{based}"/>' if sid != "Normal" else '') + f'<w:next w:val="{nxt}"/><w:qFormat/>'
                    f'<w:pPr>{ppr}{lvl}</w:pPr><w:rPr>{rpr}</w:rPr></w:style>')

        styles = (head + f'<w:styles {_Docx.NS}><w:docDefaults><w:rPrDefault><w:rPr><w:rFonts w:ascii="{font}" w:hAnsi="{font}" w:cs="{font}"/>'
                  f'<w:sz w:val="{half}"/><w:szCs w:val="{half}"/><w:lang w:val="en-US"/></w:rPr></w:rPrDefault></w:docDefaults>'
                  + style("Normal", "Normal", f'<w:spacing w:before="0" w:after="120" w:line="{int(round(body_pt * 1.22 * 20))}" w:lineRule="atLeast"/>'
                          + ('<w:jc w:val="both"/>' if justified else ''), '')
                  + style("Heading1", "heading 1", '<w:keepNext/><w:spacing w:before="360" w:after="160"/><w:jc w:val="left"/>',
                          f'<w:b/><w:bCs/><w:sz w:val="{int(round(hsize["h1"] * 2))}"/><w:szCs w:val="{int(round(hsize["h1"] * 2))}"/>', outline=0)
                  + style("Heading2", "heading 2", '<w:keepNext/><w:spacing w:before="280" w:after="120"/><w:jc w:val="left"/>',
                          f'<w:b/><w:bCs/><w:sz w:val="{int(round(hsize["h2"] * 2))}"/><w:szCs w:val="{int(round(hsize["h2"] * 2))}"/>', outline=1)
                  + style("Heading3", "heading 3", '<w:keepNext/><w:spacing w:before="200" w:after="80"/><w:jc w:val="left"/>',
                          f'<w:b/><w:bCs/><w:sz w:val="{int(round(hsize["h3"] * 2))}"/><w:szCs w:val="{int(round(hsize["h3"] * 2))}"/>', outline=2)
                  + style("Caption", "caption", '<w:keepNext/><w:spacing w:before="120" w:after="120"/><w:jc w:val="center"/>', '<w:b/><w:bCs/>')
                  + style("ListItem", "List Item", '<w:spacing w:before="0" w:after="60"/>', '')
                  + style("TableText", "Table Text", '<w:spacing w:before="20" w:after="20" w:line="240" w:lineRule="auto"/><w:jc w:val="left"/>',
                          f'<w:sz w:val="{max(14, half - 2)}"/><w:szCs w:val="{max(14, half - 2)}"/>')
                  + style("Header", "header", '<w:spacing w:before="0" w:after="0"/><w:jc w:val="center"/>', f'<w:sz w:val="{max(14, half - 3)}"/>')
                  + style("Footer", "footer", '<w:spacing w:before="0" w:after="0"/><w:jc w:val="center"/>', f'<w:sz w:val="{max(14, half - 3)}"/>')
                  + '</w:styles>')
        header = (head + f'<w:hdr {_Docx.NS}><w:p><w:pPr><w:pStyle w:val="Header"/></w:pPr><w:r><w:t xml:space="preserve">{_xml(title)}</w:t></w:r></w:p></w:hdr>')
        footer = (head + f'<w:ftr {_Docx.NS}><w:p><w:pPr><w:pStyle w:val="Footer"/></w:pPr><w:r><w:fldChar w:fldCharType="begin"/></w:r>'
                  '<w:r><w:instrText xml:space="preserve"> PAGE </w:instrText></w:r><w:r><w:fldChar w:fldCharType="separate"/></w:r>'
                  '<w:r><w:t>1</w:t></w:r><w:r><w:fldChar w:fldCharType="end"/></w:r></w:p></w:ftr>')
        sect = ('<w:sectPr><w:headerReference w:type="default" r:id="rIdH1"/><w:footerReference w:type="default" r:id="rIdF1"/>'
                f'<w:pgSz w:w="{int(round(wp * 20))}" w:h="{int(round(hp * 20))}"/>'
                f'<w:pgMar w:top="{int(margin * 20)}" w:right="{int(margin * 20)}" w:bottom="{int(margin * 20)}" w:left="{int(margin * 20)}" '
                'w:header="560" w:footer="560" w:gutter="0"/></w:sectPr>')
        rel = "http://schemas.openxmlformats.org/officeDocument/2006/relationships/"
        self.zip.writestr("[Content_Types].xml", head +
                          '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
                          '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
                          '<Default Extension="xml" ContentType="application/xml"/><Default Extension="png" ContentType="image/png"/>'
                          '<Default Extension="jpg" ContentType="image/jpeg"/>'
                          '<Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/>'
                          '<Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"/>'
                          '<Override PartName="/word/header1.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.header+xml"/>'
                          '<Override PartName="/word/footer1.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.footer+xml"/>'
                          '</Types>')
        self.zip.writestr("_rels/.rels", head + '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                          f'<Relationship Id="rId1" Type="{rel}officeDocument" Target="word/document.xml"/></Relationships>')
        self.zip.writestr("word/_rels/document.xml.rels", head + '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                          f'<Relationship Id="rIdS1" Type="{rel}styles" Target="styles.xml"/>'
                          f'<Relationship Id="rIdH1" Type="{rel}header" Target="header1.xml"/>'
                          f'<Relationship Id="rIdF1" Type="{rel}footer" Target="footer1.xml"/>' + "".join(self.rels) + '</Relationships>')
        self.zip.writestr("word/styles.xml", styles)
        self.zip.writestr("word/header1.xml", header)
        self.zip.writestr("word/footer1.xml", footer)
        self.zip.writestr("word/document.xml", head + f'<w:document {_Docx.NS}><w:body>' + "".join(body) + sect + '</w:body></w:document>')
        self.zip.close()


def build_documents(png_paths, pdf_path=None, docx_path=None, retypeset=False, jobs=None, progress=None,
                    docx_layout="flow", highlight=True, strictness="strict", use_dictionary=True, answers=None,
                    word_pictures=False, highlight_pdf=False, html_path=None):
    """Turn PNG pages into a searchable PDF and/or a Word file, working each page out once.

    word_pictures: in the flowing Word file, a word the program could not identify is put in as its own
    picture - cut from the page, sized to the text round it and sitting on the same baseline - instead
    of as the program's best guess. highlight_pdf: such words get a yellow highlighter stroke in the PDF
    too (highlight does the same in the Word file).

    answers: a file of words the user typed in for readings the program was not sure of (see
    load_answers), or the dictionary itself. The result's "review" lists what is still left as
    pictures, one entry per different reading, most frequent first, each with a picture to show.

    PDF, retypeset=False: the page pictures as they are, with the recognised text invisible behind them.
    PDF, retypeset=True: every line whose redrawn version matches the picture is erased from the
    picture and drawn as real text in the closest installed font, at the same place and size -
    sharp at any zoom. Everything else (figures, table rules, lines that do not match, text on
    patterned backgrounds) stays as the original picture with hidden text.
    Word file, docx_layout="free": as "flow", but the text runs on freely - no fixed line ends, words
    that were hyphenated at a line end joined up again. Easier to edit; lines up less closely.

    Word file, docx_layout="flow" (the default): an ordinary document - text gathered into
    paragraphs, ruled tables as real tables, figures as pictures - arranged to follow the pages.
    Text the checks could not confirm is still included (there is no page picture behind it to
    fall back on) and, with highlight=True, marked yellow so it can be proof-read.
    Word file, docx_layout="structured": the content as one flowing document - heading styles, list
    items, paragraphs joined across the columns and pages that cut them, running heads and page numbers
    taken out, a page number in the footer. It does not follow the original pages.
    Word file, docx_layout="exact": each page is its picture, with the matched lines erased from
    it and put back as one text box per line in the same font, size, colour and place.

    strictness: "strict" (default), "balanced" or "all" - how sure the program must be before it
    redraws a word; see STRICTNESS.
    jobs: pages worked on at once, each in its own process (None = default_jobs(), 1 = no
    parallelism). The first pages are done alone, to settle which fonts the document uses.
    progress(done, total, name) is called per page. Returns {"lines", "words", "replaced", "failed"}."""
    import pymupdf as fitz
    png_paths = [str(p) for p in png_paths]
    set_strictness(strictness, use_dictionary)
    if not _OCR["name"]:
        ensure_ocr_packages()
    jobs = default_jobs() if jobs is None else max(1, int(jobs))
    plan = bool(retypeset or docx_path or html_path)
    doc = fitz.open() if pdf_path else None
    word_flow = bool(docx_path) and docx_layout != "exact"
    flow = word_flow or bool(html_path)                 # the page worked out as blocks: for either kind of file
    word = None
    if docx_path:
        word = _DocxStructured(docx_path, highlight) if docx_layout == "structured" else \
            _DocxFlow(docx_path, highlight, keep_lines=docx_layout != "free") if word_flow else _Docx(docx_path)
    web = _HtmlDoc(html_path, Path(html_path).stem, highlight) if html_path else None
    fonts = {"latin": fitz.Font("helv")}
    setter = Retypesetter() if plan else None
    stats = {"lines": 0, "words": 0, "replaced": 0, "failed": 0, "confirmed": 0, "repaired": 0,
             "dictionary": len(dictionary()) if STRICTNESS.get("dictionary", True) else 0}
    done = [0]
    review = {}

    keep_plain = bool(doc is not None and not retypeset and plan)      # plain PDF next to a Word file

    def add(res):
        k = 72.0 / res["dpi"]                           # pixels -> points
        if doc is not None:
            page = doc.new_page(width=res["w"] * k, height=res["h"] * k)
            if retypeset and res["planned"]:
                page.insert_image(page.rect, stream=res["png"], overlay=False)
                _draw_page(page, k, res["jobs"], res["hidden"], fonts)
            else:
                plain = res["plain"][0] if res.get("plain") else res["png"]
                page.insert_image(page.rect, stream=plain, overlay=False)
                _draw_page(page, k, [], res["ocr"], fonts)
        if web is not None:
            if res["flow"] is None:                     # the page could not be analysed: it goes in as its picture
                web.add_page(res["w"], res["h"], k, [{"kind": "figure", "box": (0, 0, res["w"], res["h"]),
                                                      "image": (res["png"], res["ext"])}])
            else:
                web.add_page(res["w"], res["h"], k, res["flow"], reference=res.get("ref"))
        if word is not None and word_flow:
            if res["flow"] is None:                     # the page could not be analysed: keep it as its picture
                word.add_page(res["w"], res["h"], k, [{"kind": "figure", "box": (0, 0, res["w"], res["h"]),
                                                       "image": (res["png"], res["ext"])}])
            else:
                word.add_page(res["w"], res["h"], k, res["flow"], whole=res.get("whole"))
        elif word is not None:
            word.add_page(res["w"] * k, res["h"] * k, res["png"], res["dlines"], k, res["ext"])
        for key in ("lines", "words", "replaced", "confirmed", "repaired"):
            stats[key] += res[key]
        for entry in res.get("review") or []:
            group = review.get(entry["reading"])
            if group is None:
                if len(review) < 4000:
                    review[entry["reading"]] = dict(entry, count=1, page=Path(res["path"]).name)
            else:
                group["count"] += 1
                if group.get("loose") and not entry.get("loose"):
                    # a better example of the same reading: one where the box is surely on the word
                    group.update(entry, count=group["count"], page=Path(res["path"]).name)
        for reason, k in (res.get("why") or {}).items():
            stats.setdefault("why", {})
            stats["why"][reason] = stats["why"].get(reason, 0) + k
        if res.get("fonts") and not stats.get("fonts"):
            stats["fonts"] = res["fonts"]
        if res.get("times", 1) > 1:
            stats["enlarged"] = stats.get("enlarged", 0) + 1
        if res.get("flattened"):
            stats["flattened"] = stats.get("flattened", 0) + 1
        if res.get("device"):
            stats.setdefault("devices", {})
            stats["devices"][res["device"]] = stats["devices"].get(res["device"], 0) + 1
        stats["failed"] += bool(res["failed"])
        done[0] += 1
        if progress:
            progress(done[0], len(png_paths), Path(res["path"]).name)

    todo = list(png_paths)
    if jobs > 1 and len(todo) >= 3:
        # every helper process needs memory of its own: do not start more than the computer has room for
        free = available_memory_gb()
        if free is not None:
            try:
                with Image.open(todo[0]) as im:
                    pixels = im.size[0] * im.size[1]
            except Exception:
                pixels = 8_000_000
            each = 0.45 + (0.6 if _OCR["name"] == "rapid" else 0.15) + 40 * pixels * 3 / 2 ** 30
            jobs = max(1, min(jobs, int(free * 0.75 / each)))
    pool = None

    def helpers():
        """The helper processes, started when first wanted; None when the work is done one page at a time."""
        nonlocal pool
        if pool is None and jobs > 1 and len(png_paths) >= 3 and not stats.get("parallel_failed"):
            import multiprocessing
            from concurrent.futures import ProcessPoolExecutor
            pool = ProcessPoolExecutor(max_workers=min(jobs, len(png_paths)), mp_context=multiprocessing.get_context("spawn"),
                                       initializer=_worker_init,
                                       initargs=(_OCR["name"], _OCR["tesseract"], None, STRICTNESS["level"],
                                                 STRICTNESS.get("dictionary", True)))
        return pool

    def gave_up():                                      # a helper died (often: out of memory) - one page at a time now
        nonlocal pool
        import traceback
        traceback.print_exc()
        stats["parallel_failed"] = True
        try:
            pool.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass
        pool = None

    def in_order(paths, submit, alone, use):
        """Do every path - in the helpers when there are any - handing results to use(path, result) in order."""
        from collections import deque
        paths = list(paths)
        if helpers() is not None:
            try:
                waiting, ahead = deque(), iter(list(paths))

                def top_up():                           # only a few pages ahead, so results do not pile up in memory
                    while len(waiting) < 2 * jobs:
                        path = next(ahead, None)
                        if path is None:
                            return
                        waiting.append(submit(path))
                top_up()
                while waiting:
                    result = waiting.popleft().result()
                    use(paths.pop(0), result)
                    top_up()
            except Exception:
                gave_up()
        for path in list(paths):
            use(path, alone(path))
            paths.remove(path)

    # First pass, for a document of several pages: read every page, and gather the words the document
    # itself keeps using (see learn_terms). They then count as dictionary words on every page - so a
    # name read on page 2 is confirmed there because pages 5, 9 and 30 have it too.
    typed = load_answers(answers) if isinstance(answers, (str, Path)) else dict(answers or {})
    stats["answers"] = len(typed)
    options = {"word_pictures": bool(word_pictures and flow), "highlight": bool(highlight), "highlight_pdf": bool(highlight_pdf),
               "html": bool(html_path)}
    reads, terms = {}, {"terms": set(), "counts": {}, "answers": typed, "options": options}
    if plan and len(todo) >= 2 and STRICTNESS.get("dictionary", True) and STRICTNESS["level"] != "all":
        count = [0]

        def keep(path, result):
            reads[path] = result
            count[0] += 1
            if progress:
                progress(count[0], len(png_paths), "reading text: " + Path(path).name)

        in_order(todo, lambda p: pool.submit(_read_task, p), _read_task, keep)
        found = learn_terms([r[0] for r in reads.values()])
        stats["terms"] = sorted(found, key=str.lower)
        tally = {}
        for r in reads.values():
            for item in r[0]:
                cs = item[5] if isinstance(item[5], list) else [item[5]] * len(item[0].split())
                for tok, c in zip(item[0].split(), cs):
                    core = _core(tok)[1].lower()
                    if votes_of(c) >= 2 and core.isalpha():
                        tally[core] = tally.get(core, 0) + 1
        terms = {"terms": found, "counts": {k: v for k, v in tally.items() if v >= 3}, "answers": typed, "options": options}

    # alone first: until the document's fonts are settled (or, with nothing to match, not at all)
    while todo and (jobs == 1 or len(png_paths) < 3 or (plan and done[0] < 3 and (setter.mode is None or (setter.mode == "matched" and setter.short is None)))):
        path = todo.pop(0)
        add(_page_result(path, plan, setter, keep_plain, flow, reads.pop(path, None), terms))
    state = setter.state() if plan else None
    in_order(todo, lambda p: pool.submit(_page_task, p, plan, keep_plain, flow, reads.pop(p, None), terms, state),
             lambda p: _page_result(p, plan, setter, keep_plain, flow, reads.pop(p, None), terms),
             lambda p, res: add(res))
    if pool is not None:
        pool.shutdown()
    stats["review"] = sorted(review.values(), key=lambda g: (bool(g.get("loose")), -g["count"], g["reading"].lower()))
    if doc is not None:
        doc.set_metadata({"producer": "snapclean.py", "creator": "snapclean.py"})
        try:
            fitz.TOOLS.mupdf_display_errors(False)      # (a font it cannot trim is kept whole: no need to say so)
            try:
                doc.subset_fonts()                      # keep only the letters actually used
            finally:
                fitz.TOOLS.mupdf_display_errors(True)
        except Exception:
            pass
        doc.save(str(pdf_path), deflate=True, garbage=3)
        doc.close()
    if word is not None:
        word.save()
        stats["word_pictured"] = int(getattr(word, "pictured", 0))
        if getattr(word, "report", None):
            stats["structure"] = dict(word.report)
    if web is not None:
        web.save()
    return stats


def save_searchable_pdf(png_paths, pdf_path, progress=None, retypeset=False, jobs=None):
    """One searchable PDF from PNG pages; see build_documents."""
    return build_documents(png_paths, pdf_path=pdf_path, retypeset=retypeset, jobs=jobs, progress=progress)


def page_tilt(rgb, limit=4.0):
    """Angle in degrees by which a scanned page is turned (positive = anticlockwise), within +-limit.

    Text lines are horizontal bands of ink; the angle that makes the row-by-row ink totals most
    uneven is the one that lines the text up."""
    h, w = rgb.shape[:2]
    f = 900.0 / max(h, w)
    small = cv2.resize(rgb, None, fx=f, fy=f, interpolation=cv2.INTER_AREA) if f < 1 else rgb
    grey = cv2.cvtColor(small, cv2.COLOR_RGB2GRAY).astype(np.float32)
    ink = np.clip(np.median(grey) - grey, 0, None)
    if ink.sum() < 1:
        return 0.0
    hh, ww = ink.shape

    def sharpness(angle):
        M = cv2.getRotationMatrix2D((ww / 2, hh / 2), angle, 1.0)
        rows = cv2.warpAffine(ink, M, (ww, hh), flags=cv2.INTER_LINEAR).sum(axis=1)
        return float(((rows[1:] - rows[:-1]) ** 2).sum())

    best = max(np.arange(-limit, limit + 0.01, 0.25), key=sharpness)
    best = max(np.arange(best - 0.25, best + 0.251, 0.05), key=sharpness)
    return 0.0 if sharpness(best) < 1.15 * sharpness(0.0) else float(best)


def straighten(rgb):
    """Turn a tilted scan upright. Returns (picture, angle it was turned by)."""
    angle = page_tilt(rgb)
    if abs(angle) < 0.08:
        return rgb, 0.0
    h, w = rgb.shape[:2]
    edge = np.concatenate([rgb[:4].reshape(-1, 3), rgb[-4:].reshape(-1, 3), rgb[:, :4].reshape(-1, 3), rgb[:, -4:].reshape(-1, 3)])
    paper = tuple(int(v) for v in np.median(edge, axis=0))
    M = cv2.getRotationMatrix2D((w / 2, h / 2), angle, 1.0)
    return cv2.warpAffine(rgb, M, (w, h), flags=cv2.INTER_CUBIC, borderValue=paper), angle


def pdf_to_pngs(pdf_path, out_dir, dpi=None, progress=None, upright=True, pages=None):
    """Turn every page of a PDF into a PNG picture in out_dir. Returns the PNG paths, in page order.

    dpi=None picks per page: the resolution of the scan itself when the page is one big picture
    (kept between 150 and 300), otherwise 200. The PNGs carry their DPI, so page sizes survive.
    upright=True turns slightly tilted scans straight, which the text matching needs.
    pages: page numbers (starting at 0) to take; None for all of them."""
    import pymupdf as fitz
    pdf_path, out_dir = Path(pdf_path), Path(out_dir)
    doc = fitz.open(str(pdf_path))
    if doc.needs_pass:
        raise RuntimeError("This PDF is password-protected. Remove the password first.")
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    wanted = list(range(len(doc))) if pages is None else [i for i in pages if 0 <= i < len(doc)]
    for count, i in enumerate(wanted):
        page = doc[i]
        d = dpi
        if not d:
            d = 200
            try:
                images = page.get_images(full=True)
                if len(images) == 1:
                    rects = page.get_image_rects(images[0][0])
                    if rects and abs(rects[0]) >= 0.8 * abs(page.rect):
                        d = float(np.clip(images[0][2] / (rects[0].width / 72.0), 150, 300))
            except Exception:
                pass
        pix = page.get_pixmap(dpi=int(round(d)), alpha=False, colorspace=fitz.csRGB)
        rgb = np.frombuffer(pix.samples, np.uint8).reshape(pix.height, pix.width, pix.n)[..., :3]
        if upright:
            rgb, _ = straighten(np.ascontiguousarray(rgb))
        path = out_dir / f"{pdf_path.stem}_p{i + 1:04d}.png"
        save_png(path, np.ascontiguousarray(rgb), {"mode": "RGB", "dpi": (int(round(d)), int(round(d)))})
        paths.append(path)
        if progress:
            progress(count + 1, len(wanted), path.name)
    doc.close()
    return paths


def _make_pdf(pngs, pdf_path, retypeset=False, jobs=None, docx_path=None, docx_layout="flow", highlight=True,
              pages=None, strictness="strict", use_dictionary=True, html_path=None):
    pngs = sorted(pngs, key=natural_key)
    if not pngs:
        print("  no pages to work on")
        return 2
    if pages:
        try:
            pngs = [pngs[i] for i in parse_pages(pages, len(pngs))]
        except ValueError as e:
            print(f"  {e}")
            return 2
    try:
        print(f"  OCR engine: {ensure_ocr_packages()}")
    except RuntimeError as e:
        print(f"  {e}")
        return 3
    for target in (pdf_path, docx_path, html_path):
        if target:
            Path(target).parent.mkdir(parents=True, exist_ok=True)
    st = build_documents(pngs, pdf_path=pdf_path, docx_path=docx_path, retypeset=retypeset, jobs=jobs,
                         docx_layout=docx_layout, highlight=highlight, strictness=strictness,
                         use_dictionary=use_dictionary, html_path=html_path,
                         progress=lambda d, t, name: print(f"  page {d}/{t}  {name}", flush=True))
    extra = f", {st['replaced']} of {st['words']} words re-typeset as real text"
    flow = f", {st['confirmed']} of {st['words']} words confirmed" + ("" if not highlight else ", the rest highlighted")
    if st.get("dictionary"):
        print(f"  dictionary: {st['dictionary']:,} words; {st['repaired']} reading(s) corrected with it")
    if st.get("fonts"):
        print(f"  fonts: {st['fonts']}")
    if st.get("why"):
        print("  left as pictures: " + ", ".join(f"{k} {r}" for r, k in sorted(st["why"].items(), key=lambda x: -x[1])))
    if st.get("terms"):
        print(f"  learned from the document: {len(st['terms'])} term(s) - {', '.join(st['terms'][:40])}")
    for label, target, note in (("searchable PDF", pdf_path, extra if retypeset else ""),
                                ("Word file", docx_path, extra if docx_layout == "exact" else flow),
                                ("web page (editable, movable objects)", html_path, flow)):
        if target:
            print(f"  {label}: {target}  ({len(pngs)} page(s), {st['lines']} text line(s){note})")
    return 0


def _rebuild(args):
    """A scanned or otherwise poor PDF -> pictures of its pages -> a new PDF and/or Word file."""
    src, out = Path(args.input), Path(args.output)
    if not src.is_file():
        print(f"no such PDF: {src}")
        return 2
    try:
        ensure_ocr_packages()
    except RuntimeError as e:
        print(e)
        return 3
    print(f"Turning {src.name} into pictures")
    try:
        import pymupdf as fitz
        with fitz.open(str(src)) as probe:
            wanted = parse_pages(args.pages, len(probe)) if args.pages else None
    except ValueError as e:
        print(e)
        return 2
    pages = pdf_to_pngs(src, out / (src.stem + "_pages"), dpi=args.dpi, upright=not args.keep_tilt, pages=wanted,
                        progress=lambda d, t, name: print(f"  page {d}/{t}", flush=True))
    pdf = None if args.no_pdf else out / (src.stem + "_rebuilt.pdf")
    docx = out / (src.stem + "_rebuilt.docx") if args.docx else None
    web = out / (src.stem + "_rebuilt.html") if getattr(args, "html", False) else None
    if not (pdf or docx or web):
        print(f"  pictures saved in {out / (src.stem + '_pages')}")
        return 0
    return _make_pdf(pages, pdf, retypeset=not args.plain, jobs=args.jobs, docx_path=docx,
                     docx_layout="exact" if args.exact_docx else "structured" if getattr(args, "structured_docx", False) else "flow", highlight=not args.no_highlight,
                     strictness=args.strictness, use_dictionary=not args.no_dictionary, html_path=web)


# --------------------------------------------------------------------------- CLI

def _gather(inputs):
    files = []
    for item in inputs:
        p = Path(item)
        if p.is_dir():
            files += sorted(f for f in p.iterdir() if is_picture(f))
        else:
            hits = sorted(glob.glob(item))
            files += [Path(x) for x in hits if is_picture(x)]
    seen, out = set(), []
    for f in files:
        if f.resolve() not in seen:
            seen.add(f.resolve())
            out.append(f)
    return expand_pictures(out)


def _ints(text):
    return [int(x) for x in text.replace(" ", "").split(",") if x] if text else None


def _box(text):
    v = _ints(text)
    if not v or len(v) != 4:
        raise argparse.ArgumentTypeError("box must be x0,y0,x1,y1")
    return tuple(v)


def _process(args, do_remove):
    files = _gather(args.input)
    if not files:
        sys.exit("no PNG files found")
    by_size = {}
    for f in files:
        by_size.setdefault(picture_size(f), []).append(f)

    out_dir = Path(args.output) if do_remove else None
    if do_remove:
        out_dir.mkdir(parents=True, exist_ok=True)
        if any(out_dir.resolve() == f.parent.resolve() for f in files):
            sys.exit("output folder must differ from the input folder (originals are never overwritten)")
    report = Path(args.report) if args.report else (out_dir / "_report" if do_remove else Path("snapclean_report"))
    report.mkdir(parents=True, exist_ok=True)

    status = 0
    for (w, h), group_files in sorted(by_size.items(), key=lambda kv: -len(kv[1])):
        print(f"\n{w}x{h}: {len(group_files)} page(s)")
        if len(group_files) < 3:
            print("  fewer than 3 pages of this size - cannot learn a watermark; " +
                  ("copied unchanged." if do_remove else "skipped."))
            if do_remove:
                for f in group_files:
                    if f.suffix.lower() == ".png":
                        shutil.copy2(f, out_dir / f.name)
                    else:                               # every page comes out a PNG, whatever it went in as
                        save_png(out_dir / (f.stem + ".png"), *load_png(f))
            continue
        take = min(len(group_files), sample_limit(w, h, args.max_samples))
        idx = np.unique(np.linspace(0, len(group_files) - 1, take).round().astype(int))
        sample = [load_png(group_files[i])[0] for i in idx]
        model = learn_model(sample, lo=args.lo, hi=args.hi, min_area=args.min_area, merge=args.merge,
                            opaque=args.opaque, bg_scale=args.bg_scale, fit_alpha=not args.no_alpha_fit,
                            stable=args.stable)
        del sample
        model.select(ids=_ints(args.select), exclude=_ints(args.exclude), include_opaque=args.include_opaque,
                     regions=args.region, protect=args.protect, alpha=args.alpha)
        print(model.summary())
        prev = report / f"preview_{w}x{h}.png"
        save_png(prev, model.preview())
        print(f"  preview: {prev}")

        if not model.selection.any():
            status = 2
            print("  nothing selected. No translucent watermark was found; if one of the groups above\n"
                  "  is the watermark, re-run with --select <id> (see the preview).")
            if do_remove:
                continue
        if not do_remove:
            continue
        cleaned = 0
        for f in group_files:
            rgb, info = load_png(f)
            out, removed = model.remove(rgb, args.tolerance)
            if args.enhance > 1:
                out, info = enhance_page(out, info, args.enhance)
            save_png(out_dir / (f.stem + ".png"), out, info)
            cleaned += bool(removed)
            if not removed:
                print(f"  {f.name}: watermark not present, saved unchanged")
        print(f"  cleaned {cleaned}/{len(group_files)} page(s) -> {out_dir}")
    if do_remove and (args.pdf or args.docx):
        print("\nBuilding the document(s)")
        status = max(status, _make_pdf([out_dir / f.name for f in files if (out_dir / f.name).exists()], args.pdf,
                                        args.retypeset, args.jobs, args.docx,
                                        "exact" if args.exact_docx else "structured" if getattr(args, "structured_docx", False) else "flow", not args.no_highlight,
                                        None, args.strictness, not args.no_dictionary))
    return status


def _add_common(p):
    p.add_argument("--report", help="folder for preview images")
    p.add_argument("--select", help="group ids to remove, e.g. 1,3 (default: all translucent pieces)")
    p.add_argument("--exclude", help="group ids to leave alone")
    p.add_argument("--include-opaque", action="store_true", help="also remove solid static elements (headers, logos)")
    p.add_argument("--region", type=_box, action="append", help="only remove inside x0,y0,x1,y1 (repeatable)")
    p.add_argument("--protect", type=_box, action="append", help="never touch x0,y0,x1,y1 (repeatable)")
    p.add_argument("--alpha", type=float, help="force watermark opacity 0-1 instead of fitting it")
    p.add_argument("--no-alpha-fit", action="store_true", help="use the minimum plausible opacity")
    p.add_argument("--max-samples", type=int, default=30, help="pages used to learn the watermark [30]")
    p.add_argument("--lo", type=float, default=2.0, help="mask grow threshold, grey levels [2]")
    p.add_argument("--hi", type=float, default=8.0, help="mask seed threshold, grey levels [8]")
    p.add_argument("--min-area", type=int, default=8, help="ignore static specks below this many px [8]")
    p.add_argument("--merge", type=float, default=0.015, help="grouping distance, fraction of diagonal [0.015]")
    p.add_argument("--opaque", type=float, default=0.6, help="core opacity at which a piece counts as solid [0.6]")
    p.add_argument("--stable", type=float, default=0.45, help="fraction of pages that must agree for a pixel to count as static [0.45]")
    p.add_argument("--bg-scale", type=float, default=0.15, help="background filter size for non-uniform pages [0.15]")


def cli_main(argv=None):
    ap = argparse.ArgumentParser(prog="snapclean.py", description="Learn a repeated watermark from a series of PNGs and remove it.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("analyze", help="detect static elements and write a preview; changes nothing")
    a.add_argument("input", nargs="+", help="folder, files or glob of page pictures (png, jpg, tif, bmp, webp, gif)")
    _add_common(a)
    r = sub.add_parser("run", help="detect and remove")
    r.add_argument("input", nargs="+", help="folder, files or glob of page pictures (png, jpg, tif, bmp, webp, gif)")
    r.add_argument("output", help="folder for cleaned PNGs")
    r.add_argument("--tolerance", type=float, default=2.0, help="ignore deviations below this (noise guard) [2]")
    r.add_argument("--enhance", type=int, default=1, choices=(1, 2, 3),
                   help="enlarge the cleaned pages 2x or 3x and sharpen the text [1 = off]")
    r.add_argument("--pdf", metavar="FILE.pdf", help="also save the cleaned pages as one searchable (OCR) PDF")
    r.add_argument("--retypeset", action="store_true",
                   help="in the PDF, replace matched words with real text in the closest installed font")
    r.add_argument("--docx", metavar="FILE.docx", help="also save the cleaned pages as a Word file")
    r.add_argument("--structured-docx", action="store_true",
                   help="Word file as a structured document: heading styles, lists, paragraphs joined across columns and pages, "
                        "running heads removed, a page number in the footer (does not follow the original pages)")
    r.add_argument("--exact-docx", action="store_true",
                   help="Word file as an exact page copy (page picture + one text box per line) instead of paragraphs")
    r.add_argument("--no-highlight", action="store_true", help="Word file: do not mark unconfirmed text in yellow")
    r.add_argument("--no-dictionary", action="store_true", help="do not use the word list to help the checks")
    r.add_argument("--strictness", choices=("strict", "balanced", "all"), default="strict",
                   help="how sure to be before redrawing a word: strict = nothing unconfirmed, "
                        "balanced = more words, all = everything the OCR read [strict]")
    r.add_argument("--jobs", type=int, default=None, help="pages worked on at once for the PDF [CPU cores - 1, max 8]")
    _add_common(r)
    p = sub.add_parser("pdf", help="turn PNG pages into one searchable (OCR) PDF, no watermark removal")
    p.add_argument("input", nargs="+", help="folder, files or glob of page pictures (png, jpg, tif, bmp, webp, gif)")
    p.add_argument("output", help="PDF file to write")
    p.add_argument("--retypeset", action="store_true",
                   help="replace matched words with real text in the closest installed font")
    p.add_argument("--docx", metavar="FILE.docx", help="also write a Word file")
    p.add_argument("--pages", help="only these pages, e.g. 1-3 or 2,5,9 (for a quick test) [all]")
    p.add_argument("--structured-docx", action="store_true",
                   help="Word file as a structured document: heading styles, lists, paragraphs joined across columns and pages, "
                        "running heads removed, a page number in the footer (does not follow the original pages)")
    p.add_argument("--exact-docx", action="store_true",
                   help="Word file as an exact page copy (page picture + one text box per line) instead of paragraphs")
    p.add_argument("--no-highlight", action="store_true", help="Word file: do not mark unconfirmed text in yellow")
    p.add_argument("--no-dictionary", action="store_true", help="do not use the word list to help the checks")
    p.add_argument("--strictness", choices=("strict", "balanced", "all"), default="strict",
                   help="how sure to be before redrawing a word: strict = nothing unconfirmed, "
                        "balanced = more words, all = everything the OCR read [strict]")
    p.add_argument("--jobs", type=int, default=None, help="pages worked on at once [CPU cores - 1, max 8]")
    b = sub.add_parser("rebuild", help="rebuild a scanned / rasterised / poor PDF as a new PDF and Word file")
    b.add_argument("input", help="the PDF to rebuild")
    b.add_argument("output", help="folder for the results")
    b.add_argument("--docx", action="store_true", help="also write a Word file")
    b.add_argument("--html", action="store_true", help="also write a web page: every paragraph, picture and table an "
                                                       "object that can be edited and moved in the browser")
    b.add_argument("--pages", help="only these pages, e.g. 1-3 or 2,5,9 (for a quick test) [all]")
    b.add_argument("--structured-docx", action="store_true",
                   help="Word file as a structured document: heading styles, lists, paragraphs joined across columns and pages, "
                        "running heads removed, a page number in the footer (does not follow the original pages)")
    b.add_argument("--exact-docx", action="store_true",
                   help="Word file as an exact page copy (page picture + one text box per line) instead of paragraphs")
    b.add_argument("--no-highlight", action="store_true", help="Word file: do not mark unconfirmed text in yellow")
    b.add_argument("--no-dictionary", action="store_true", help="do not use the word list to help the checks")
    b.add_argument("--strictness", choices=("strict", "balanced", "all"), default="strict",
                   help="how sure to be before redrawing a word: strict = nothing unconfirmed, "
                        "balanced = more words, all = everything the OCR read [strict]")
    b.add_argument("--no-pdf", action="store_true", help="do not write a PDF")
    b.add_argument("--plain", action="store_true", help="PDF: keep the page pictures, only add hidden search text")
    b.add_argument("--dpi", type=int, default=None, help="resolution to read the pages at [automatic, 150-300]")
    b.add_argument("--keep-tilt", action="store_true", help="do not straighten tilted scans")
    b.add_argument("--jobs", type=int, default=None, help="pages worked on at once [CPU cores - 1, max 8]")
    s = sub.add_parser("selftest", help="build synthetic watermarked pages and verify removal")
    s.add_argument("--keep", help="folder to keep the synthetic pages and results in")
    args = ap.parse_args(argv)
    if args.cmd == "selftest":
        return selftest(args.keep)
    if args.cmd == "pdf":
        return _make_pdf(_gather(args.input), args.output, args.retypeset, args.jobs, args.docx,
                         "exact" if args.exact_docx else "structured" if getattr(args, "structured_docx", False) else "flow", not args.no_highlight, args.pages, args.strictness,
                         not args.no_dictionary)
    if args.cmd == "rebuild":
        return _rebuild(args)
    return _process(args, args.cmd == "run")


# --------------------------------------------------------------------------- self-test

def _font(size):
    from PIL import ImageFont
    for name in ("DejaVuSans.ttf", "arial.ttf", "Arial.ttf", "LiberationSans-Regular.ttf"):
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            pass
    try:
        return ImageFont.load_default(size)
    except TypeError:
        return ImageFont.load_default()


def _synthetic(folder, mode, n=10, size=(850, 1100), seed=1):
    """Write n pages into folder/in and their clean truth into folder/truth."""
    from PIL import ImageDraw
    rng = np.random.default_rng(seed)
    w, h = size
    words = ("relay breaker feeder bus fault current voltage transformer zone trip pickup "
             "sequence impedance reach timer the of and to in for with on is at").split()
    body, head, big = _font(17), _font(20), _font(120)

    layer = Image.new("RGBA", (w * 2, h * 2), (0, 0, 0, 0))
    ink = (200, 30, 30, 70) if mode == "over" else (212, 212, 212, 255)
    ImageDraw.Draw(layer).text((w, h), "CONFIDENTIAL", font=big, fill=ink, anchor="mm")
    layer = layer.rotate(35, resample=Image.BICUBIC).crop((w // 2, h // 2, w // 2 + w, h // 2 + h))

    def draw_content(page):
        d = ImageDraw.Draw(page)
        d.text((60, 40), "ACME Utilities - Protection Settings Report", font=head, fill=(0, 0, 0))
        d.line((60, 72, w - 60, 72), fill=(0, 0, 0), width=2)
        y = 110 + int(rng.integers(0, 14))
        while y < h - 80:
            line = " ".join(rng.choice(words, int(rng.integers(4, 13))))
            d.text((60, y), line, font=body, fill=(0, 0, 0))
            y += int(rng.integers(24, 40))

    (folder / "in").mkdir(parents=True)
    (folder / "truth").mkdir()
    for i in range(n):
        state = rng.bit_generator.state
        truth = Image.new("RGB", size, "white")
        draw_content(truth)
        truth.save(folder / "truth" / f"page_{i:02d}.png")
        if i == n - 1:                                     # one page with no watermark at all
            page = truth
        elif mode == "over":                               # watermark blended on top of text
            page = Image.alpha_composite(truth.convert("RGBA"), layer).convert("RGB")
        else:                                              # watermark printed under the text
            rng.bit_generator.state = state
            page = Image.alpha_composite(Image.new("RGBA", size, "white"), layer).convert("RGB")
            draw_content(page)
        page.save(folder / "in" / f"page_{i:02d}.png")


def selftest(keep=None):
    root = Path(keep) if keep else Path(tempfile.mkdtemp(prefix="snapclean_"))
    ok = True
    for mode in ("over", "under"):
        folder = root / mode
        if folder.exists():
            shutil.rmtree(folder)
        _synthetic(folder, mode)
        paths = sorted((folder / "in").glob("*.png"))
        pages = [load_png(p)[0] for p in paths]
        model = learn_model(pages)
        (folder / "out").mkdir()
        save_png(folder / "preview.png", model.preview())
        sel = model.selection
        worst_before = worst_after = 0.0
        mean_after = []
        outside_same = header_same = True
        for p, page in zip(paths, pages):
            truth = load_png(folder / "truth" / p.name)[0].astype(np.int16)
            out, _ = model.remove(page)
            save_png(folder / "out" / p.name, out)
            outside_same &= bool((out[~sel] == page[~sel]).all())
            header_same &= bool((out[:90] == truth[:90]).all())
            worst_before = max(worst_before, float(np.abs(page - truth).mean(axis=2).max()))
            err = np.abs(out - truth).max(axis=2)
            worst_after = max(worst_after, float(np.percentile(err, 99.99)))
            mean_after.append(float(err[sel].mean()) if sel.any() else 0.0)
        passed = outside_same and header_same and sel.any() and worst_after <= 12 and max(mean_after) <= 1.0
        ok &= passed
        print(f"[{mode:5s}] {'PASS' if passed else 'FAIL'}  watermark error before: {worst_before:.0f} levels | "
              f"after: mean {max(mean_after):.2f}, 99.99th pct {worst_after:.0f} | "
              f"outside mask identical: {outside_same} | header intact: {header_same}")
        print(model.summary())
    print(f"\nfiles: {root}" if keep else "")
    if not keep:
        shutil.rmtree(root, ignore_errors=True)
    return 0 if ok else 1


# =============================================================================
# PART 2 - SNAPSHOT TAB (hotkey, mark an area, save, press a key, repeat)
# =============================================================================

SETTINGS_FILE = Path.home() / ".snapkey_hotkey.json"      # same file as the old snapkey_hotkey.py
MAX_UNTIL_SAME = 500

HOTKEYS = {"F9": "<f9>", "F8": "<f8>", "F7": "<f7>", "F6": "<f6>", "F10": "<f10>",
           "Ctrl+Alt+S": "<ctrl>+<alt>+s", "Ctrl+Shift+F9": "<ctrl>+<shift>+<f9>"}

PRE_KEY_CHOICES = ["Esc", "F5", "Home", "End", "Space", "Enter", "Tab", "Page Down", "Down arrow", "Ctrl+0", "Ctrl+Home"]
MOUSE_BUTTONS = ["Left", "Right", "Middle", "Left double-click"]

KEY_CHOICES = ["Right arrow", "Left arrow", "Down arrow", "Up arrow", "Page Down", "Page Up",
               "Space", "Enter", "Tab", "n", "Ctrl+Right arrow"]

SNAP_DEFAULTS = {
    "area_mode": "drag", "width": "1920", "height": "1080", "reuse": False,
    "key": "Right arrow", "mode": "count", "count": "10", "delay": "1.0", "first_wait": "0.5",
    "out": str(Path.home() / "snapshots"), "prefix": "snap", "start": "", "digits": "3",
    "format": "png", "hotkey": "F9", "minimize": True,
    "click_on": False, "click_button": "Left", "pre_key_on": False, "pre_key": "Esc", "pre_wait": "0.5",
}


def _keymaps():
    K = keyboard.Key
    special = {
        "right": K.right, "left": K.left, "up": K.up, "down": K.down,
        "pagedown": K.page_down, "pageup": K.page_up, "space": K.space, "enter": K.enter,
        "return": K.enter, "tab": K.tab, "esc": K.esc, "escape": K.esc, "home": K.home,
        "end": K.end, "backspace": K.backspace, "delete": K.delete,
        **{f"f{i}": getattr(K, f"f{i}") for i in range(1, 13)},
    }
    mods = {"ctrl": K.ctrl, "control": K.ctrl, "alt": K.alt, "shift": K.shift, "win": K.cmd, "cmd": K.cmd}
    return special, mods


def parse_key(spec: str):
    """'Ctrl+Right arrow' -> ([Key.ctrl], Key.right).  Raises ValueError if not understood."""
    if keyboard is None:
        raise ValueError(f"The keyboard package (pynput) could not be loaded: {KEYBOARD_ERROR}")
    special, modifiers = _keymaps()
    parts = [re.sub(r"\s+|arrow", "", p.lower()) for p in spec.split("+")] if spec != "+" else ["+"]
    if not parts or not parts[-1]:
        raise ValueError("Choose the key to press.")
    mods = []
    for m in parts[:-1]:
        if m not in modifiers:
            raise ValueError(f"'{m}' is not a modifier. Use Ctrl, Alt, Shift or Win.")
        mods.append(modifiers[m])
    name = parts[-1]
    if name in special:
        return mods, special[name]
    if len(name) == 1:
        return mods, name
    raise ValueError(f"'{spec}' is not a key name this tool knows.")


def next_start(out: Path, prefix: str, ext: str) -> int:
    pattern = re.compile(rf"^{re.escape(prefix)}_(\d+)\.{ext}$", re.IGNORECASE)
    numbers = [int(m.group(1)) for f in out.glob(f"{prefix}_*.{ext}") if (m := pattern.match(f.name))]
    return max(numbers) + 1 if numbers else 1


def virtual_screen(widget):
    """(x, y, width, height) of the whole desktop across all monitors."""
    if IS_WINDOWS:
        gm = ctypes.windll.user32.GetSystemMetrics
        return gm(76), gm(77), gm(78), gm(79)
    return 0, 0, widget.winfo_screenwidth(), widget.winfo_screenheight()


def foreground_window():
    return ctypes.windll.user32.GetForegroundWindow() if IS_WINDOWS else None


def restore_foreground(handle):
    if IS_WINDOWS and handle:
        try:
            ctypes.windll.user32.SetForegroundWindow(handle)
        except Exception:
            pass


def sleep_or_stop(seconds: float, stop: threading.Event) -> bool:
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        if stop.is_set():
            return True
        time.sleep(min(0.05, max(0.0, end - time.monotonic())))
    return stop.is_set()


def capture(o: dict, bbox, log, stop: threading.Event) -> int:
    """Grab bbox from the screen, save, press the key, repeat. Runs in a worker thread."""
    out = Path(o["out"]).expanduser()
    out.mkdir(parents=True, exist_ok=True)
    number = o["start"] if o["start"] is not None else next_start(out, o["prefix"], o["format"])
    until_same = o["mode"] == "until_same"
    total = MAX_UNTIL_SAME if until_same else o["count"]
    mods, key = o["key_parsed"]
    typer = keyboard.Controller()
    taken = 0
    previous = None
    pointer = mouse.Controller() if o.get("click") else None

    def tap(mods, key):
        for m in mods:
            typer.press(m)
        typer.press(key)
        typer.release(key)
        for m in reversed(mods):
            typer.release(m)

    def prepare():
        """What the user asked for before every snapshot: a mouse click at their point, then a key."""
        if pointer is not None:
            x, y, name = o["click"]
            pointer.position = (x, y)
            time.sleep(0.08)                           # let the program under the pointer notice it
            button = {"Right": mouse.Button.right, "Middle": mouse.Button.middle}.get(name, mouse.Button.left)
            pointer.click(button, 2 if "double" in name else 1)
            time.sleep(0.05)
        if o.get("pre_key"):
            tap(*o["pre_key"])
        return bool(pointer is not None or o.get("pre_key")) and sleep_or_stop(o["pre_wait"], stop)

    if sleep_or_stop(o["first_wait"], stop):  # let the dimmed overlay disappear
        return taken

    for i in range(total):
        if stop.is_set() or prepare():
            break
        image = ImageGrab.grab(bbox=bbox, all_screens=True).convert("RGB")
        digest = hashlib.sha256(image.tobytes()).hexdigest()
        if until_same and digest == previous:
            log("Snapshot matches the previous one - nothing left to capture.")
            break
        previous = digest

        path = out / f"{o['prefix']}_{number:0{o['digits']}d}.{o['format']}"
        if o["format"] == "jpg":
            image.save(path, "JPEG", quality=92)
        else:
            image.save(path, "PNG")
        taken += 1
        number += 1
        log(f"  saved {path.name}", progress=(taken, None if until_same else total))
        if taken == 1:
            # How big is the type? Re-typesetting needs letters about 15 pixels high; smaller ones are
            # enlarged later, but enlarging adds no detail - a bigger snapshot is always the better start.
            try:
                tall = _letter_height(np.asarray(image))
            except Exception:
                tall = 0.0
            if 0 < tall < 12:
                grow = int(math.ceil(15.0 / tall * 100 / 25.0)) * 25
                log(f"  NOTE: the letters in this snapshot are only about {tall:.0f} pixels high. For re-typesetting they should be "
                    f"15 or more. Zoom the page in the viewer to about {grow}% of what it is now (Ctrl and +) and snap a larger "
                    "area, if the screen allows - the text will be read and matched far better. (Smaller type still works: "
                    "it is enlarged automatically, but that adds no detail.)")
            elif tall >= 12:
                log(f"  Letters are about {tall:.0f} pixels high - good for re-typesetting.")

        if i < total - 1:
            tap(mods, key)
            if sleep_or_stop(o["delay"], stop):
                break
    return taken


class Overlay(tk.Toplevel if tk else object):
    """Dims the whole desktop and lets the user mark the capture area."""

    def __init__(self, master, fixed_size, on_done, point=False):
        super().__init__(master)
        self.on_done = on_done            # called with bbox (x1, y1, x2, y2) - or (x, y) for a point - or None
        self.fixed = fixed_size           # (w, h) or None
        self.point = point                # just pick one spot on the screen
        self.vx, self.vy, vw, vh = virtual_screen(master)
        self.origin = None
        self.finished = False

        self.overrideredirect(True)
        self.geometry(f"{vw}x{vh}+{self.vx}+{self.vy}")
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", 0.35)
        except tk.TclError:
            pass
        self.canvas = tk.Canvas(self, bg="black", highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)
        self.rect = self.canvas.create_rectangle(0, 0, 0, 0, outline="red", width=2, fill="white", state="hidden")
        self.label = self.canvas.create_text(0, 0, anchor="sw", fill="yellow", font=("Segoe UI", 14, "bold"))
        hint = ("Click to place the top-left corner of the area" if self.fixed
                else "Drag a box over the area to capture")
        if self.point:
            hint = "Click the spot where the mouse should click before each snapshot"
        self.canvas.create_text(vw // 2, 40, fill="white", font=("Segoe UI", 18, "bold"),
                                text=f"{hint}   -   Esc or right-click to cancel")

        if self.point:
            self.canvas.bind("<ButtonPress-1>", lambda e: self._finish((e.x + self.vx, e.y + self.vy)))
        elif self.fixed:
            self.canvas.bind("<Motion>", self._fixed_move)
            self.canvas.bind("<ButtonPress-1>", self._fixed_click)
        else:
            self.canvas.bind("<ButtonPress-1>", self._press)
            self.canvas.bind("<B1-Motion>", self._drag)
            self.canvas.bind("<ButtonRelease-1>", self._release)
        self.canvas.bind("<Button-3>", lambda e: self._finish(None))
        self.bind("<Escape>", lambda e: self._finish(None))
        self.after(50, self._take_focus)

    def _take_focus(self):
        try:
            self.lift()
            self.focus_force()
        except tk.TclError:
            pass

    def _draw(self, x1, y1, x2, y2):
        self.canvas.coords(self.rect, x1, y1, x2, y2)
        self.canvas.itemconfigure(self.rect, state="normal")
        self.canvas.coords(self.label, min(x1, x2), max(min(y1, y2) - 6, 24))
        self.canvas.itemconfigure(self.label, text=f"{abs(x2 - x1)} x {abs(y2 - y1)}")

    # drag mode
    def _press(self, e):
        self.origin = (e.x, e.y)

    def _drag(self, e):
        if self.origin:
            self._draw(*self.origin, e.x, e.y)

    def _release(self, e):
        if not self.origin:
            return
        x1, x2 = sorted((self.origin[0], e.x))
        y1, y2 = sorted((self.origin[1], e.y))
        self.origin = None
        if x2 - x1 < 5 or y2 - y1 < 5:      # a stray click, not a drag: let them try again
            self.canvas.itemconfigure(self.rect, state="hidden")
            self.canvas.itemconfigure(self.label, text="")
            return
        self._finish((x1 + self.vx, y1 + self.vy, x2 + self.vx, y2 + self.vy))

    # fixed-size mode
    def _fixed_move(self, e):
        self._draw(e.x, e.y, e.x + self.fixed[0], e.y + self.fixed[1])

    def _fixed_click(self, e):
        x, y = e.x + self.vx, e.y + self.vy
        self._finish((x, y, x + self.fixed[0], y + self.fixed[1]))

    def _finish(self, bbox):
        if self.finished:
            return
        self.finished = True
        self.destroy()
        self.on_done(bbox)


class SnapTab(ttk.Frame if ttk else object):
    """Tab 1: wait for the hotkey, let the user mark an area, then snapshot / press key / repeat."""

    def __init__(self, master, on_send=None):
        super().__init__(master, padding=12)
        self.top = self.winfo_toplevel()
        self.on_send = on_send            # called with the snapshot folder (Path)
        self.events = queue.Queue()
        self.stop_event = threading.Event()
        self.worker = None
        self.overlay = None
        self.listener = None
        self.state_name = "idle"          # idle | selecting | capturing
        self.target_window = None
        self.pending_options = None
        self.last_folder = None
        self.eta = Eta()

        stored = {}
        try:
            stored = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        except Exception:
            pass
        self.last_bbox = tuple(stored["last_bbox"]) if stored.get("last_bbox") else None
        self.click_point = tuple(stored["click_point"]) if stored.get("click_point") else None
        self.v = {}
        for name, default in SNAP_DEFAULTS.items():
            value = stored.get(name, default)
            self.v[name] = tk.BooleanVar(value=bool(value)) if isinstance(default, bool) else tk.StringVar(value=str(value))

        self._build()
        self._area_changed()
        self._mode_changed()
        self._start_listener()
        self.after(100, self._poll)

    # ---- layout ----
    def _build(self):
        pad = {"padx": 6, "pady": 4}
        root = self
        root.columnconfigure(0, weight=1)

        self.steps = ttk.Label(root, justify="left")
        self.steps.grid(row=0, column=0, sticky="w", padx=6, pady=(0, 6))

        # Area
        f = ttk.LabelFrame(root, text="Area to snapshot", padding=8)
        f.grid(row=1, column=0, sticky="ew")
        ttk.Radiobutton(f, text="Drag a box on screen", variable=self.v["area_mode"], value="drag",
                        command=self._area_changed).grid(row=0, column=0, columnspan=6, sticky="w", **pad)
        ttk.Radiobutton(f, text="Exact size:", variable=self.v["area_mode"], value="fixed",
                        command=self._area_changed).grid(row=1, column=0, sticky="w", **pad)
        self.w_entry = ttk.Entry(f, textvariable=self.v["width"], width=7)
        self.w_entry.grid(row=1, column=1, **pad)
        ttk.Label(f, text="x").grid(row=1, column=2)
        self.h_entry = ttk.Entry(f, textvariable=self.v["height"], width=7)
        self.h_entry.grid(row=1, column=3, **pad)
        ttk.Label(f, text="px  (click on screen to place its top-left corner)").grid(row=1, column=4, sticky="w", **pad)
        ttk.Checkbutton(f, text="Reuse the last area and skip selecting", variable=self.v["reuse"],
                        command=self._update_steps).grid(row=2, column=0, columnspan=4, sticky="w", **pad)
        self.area_label = ttk.Label(f, foreground="#555")
        self.area_label.grid(row=2, column=4, columnspan=2, sticky="w", **pad)

        # Repeat
        f = ttk.LabelFrame(root, text="Repeat", padding=8)
        f.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        ttk.Label(f, text="Key to press").grid(row=0, column=0, sticky="w", **pad)
        ttk.Combobox(f, textvariable=self.v["key"], values=KEY_CHOICES, width=20).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(f, text="Wait after key (s)").grid(row=0, column=2, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.v["delay"], width=6).grid(row=0, column=3, sticky="w", **pad)
        ttk.Radiobutton(f, text="Take", variable=self.v["mode"], value="count",
                        command=self._mode_changed).grid(row=1, column=0, sticky="w", **pad)
        box = ttk.Frame(f)
        box.grid(row=1, column=1, sticky="w", **pad)
        self.count_entry = ttk.Entry(box, textvariable=self.v["count"], width=6)
        self.count_entry.pack(side="left")
        ttk.Label(box, text=" snapshots").pack(side="left")
        ttk.Label(f, text="Wait before first (s)").grid(row=1, column=2, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.v["first_wait"], width=6).grid(row=1, column=3, sticky="w", **pad)
        ttk.Radiobutton(f, text="Keep going until the area stops changing", variable=self.v["mode"],
                        value="until_same", command=self._mode_changed).grid(row=2, column=0, columnspan=4, sticky="w", **pad)

        # Before each snapshot
        f = ttk.LabelFrame(root, text="Before each snapshot (optional)", padding=8)
        f.grid(row=3, column=0, sticky="ew", pady=(8, 0))
        ttk.Checkbutton(f, text="Click the mouse at", variable=self.v["click_on"],
                        command=self._update_steps).grid(row=0, column=0, sticky="w", **pad)
        self.point_label = ttk.Label(f, width=22)
        self.point_label.grid(row=0, column=1, sticky="w", **pad)
        ttk.Button(f, text="Pick the spot...", command=self._pick_point).grid(row=0, column=2, sticky="w", **pad)
        ttk.Label(f, text="Button").grid(row=0, column=3, sticky="w", **pad)
        ttk.Combobox(f, textvariable=self.v["click_button"], values=MOUSE_BUTTONS, state="readonly",
                     width=16).grid(row=0, column=4, sticky="w", **pad)
        ttk.Checkbutton(f, text="Then press this key", variable=self.v["pre_key_on"],
                        command=self._update_steps).grid(row=1, column=0, sticky="w", **pad)
        ttk.Combobox(f, textvariable=self.v["pre_key"], values=PRE_KEY_CHOICES, width=20).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(f, text="any key: type its name, e.g.  F2  or  Ctrl+Shift+L", foreground="#555"
                  ).grid(row=1, column=2, columnspan=2, sticky="w", **pad)
        box = ttk.Frame(f)
        box.grid(row=1, column=4, sticky="w", **pad)
        ttk.Label(box, text="Then wait (s) ").pack(side="left")
        ttk.Entry(box, textvariable=self.v["pre_wait"], width=6).pack(side="left")

        # Files
        f = ttk.LabelFrame(root, text="Files", padding=8)
        f.grid(row=4, column=0, sticky="ew", pady=(8, 0))
        f.columnconfigure(1, weight=1)
        ttk.Label(f, text="Save to folder").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.v["out"]).grid(row=0, column=1, columnspan=6, sticky="ew", **pad)
        ttk.Button(f, text="Browse...", command=self._pick_folder).grid(row=0, column=7, **pad)
        ttk.Label(f, text="Name prefix").grid(row=1, column=0, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.v["prefix"], width=14).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(f, text="Start #").grid(row=1, column=2, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.v["start"], width=6).grid(row=1, column=3, sticky="w", **pad)
        ttk.Label(f, text="Digits").grid(row=1, column=4, sticky="w", **pad)
        ttk.Spinbox(f, textvariable=self.v["digits"], from_=1, to=6, width=4).grid(row=1, column=5, sticky="w", **pad)
        ttk.Combobox(f, textvariable=self.v["format"], values=["png", "jpg"], state="readonly",
                     width=5).grid(row=1, column=6, sticky="w", **pad)
        self.example = ttk.Label(f, foreground="#555")
        self.example.grid(row=2, column=0, columnspan=8, sticky="w", **pad)
        for name in ("prefix", "start", "digits", "format"):
            self.v[name].trace_add("write", lambda *_: self._update_example())
        self._update_example()

        # Hotkey
        f = ttk.Frame(root)
        f.grid(row=5, column=0, sticky="ew", pady=(8, 0))
        ttk.Label(f, text="Hotkey").pack(side="left", padx=6)
        combo = ttk.Combobox(f, textvariable=self.v["hotkey"], values=list(HOTKEYS), state="readonly", width=14)
        combo.pack(side="left", padx=6)
        combo.bind("<<ComboboxSelected>>", lambda e: self._start_listener())
        ttk.Checkbutton(f, text="Minimize this window while snapping",
                        variable=self.v["minimize"]).pack(side="left", padx=12)

        # Buttons
        f = ttk.Frame(root)
        f.grid(row=6, column=0, sticky="ew", pady=(10, 4))
        self.stop_btn = ttk.Button(f, text="Stop", command=self._stop, state="disabled")
        self.stop_btn.pack(side="left", padx=6)
        ttk.Button(f, text="Open folder", command=self._open_folder).pack(side="left", padx=6)
        self.send_btn = ttk.Button(f, text="Remove watermark from these snapshots  >", style="Go.TButton",
                                   command=self._send)
        self.send_btn.pack(side="left", padx=(18, 6))
        self.status = ttk.Label(f, font=("Segoe UI", 10, "bold"))
        self.status.pack(side="right", padx=6)

        self.bar = ttk.Progressbar(root, mode="determinate")
        self.bar.grid(row=7, column=0, sticky="ew", padx=6)

        f = ttk.Frame(root)
        f.grid(row=8, column=0, sticky="nsew", pady=(8, 0))
        root.rowconfigure(8, weight=1)
        f.columnconfigure(0, weight=1)
        f.rowconfigure(0, weight=1)
        self.log_box = tk.Text(f, height=7, state="disabled", wrap="word")
        self.log_box.grid(row=0, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(f, command=self.log_box.yview)
        scroll.grid(row=0, column=1, sticky="ns")
        self.log_box.configure(yscrollcommand=scroll.set)

    # ---- small handlers ----
    def _update_steps(self):
        hk = self.v["hotkey"].get()
        if self.v["reuse"].get() and self.last_bbox:
            pick = "Snapshots of the last area start right away."
        elif self.v["area_mode"].get() == "fixed":
            pick = "Click where the top-left corner of the area goes. Snapshots start right away."
        else:
            pick = "Drag a box over the area to capture. Snapshots start right away."
        self.steps.configure(text=f"1.  Leave this tab showing and open your browser to the first page.\n"
                                  f"2.  Press {hk}.\n"
                                  f"3.  {pick}\n"
                                  f"      Press {hk} again to stop early.")
        if self.state_name == "idle":
            self.status.configure(text=f"Waiting for {hk}")
        self.point_label.configure(text=f"x {self.click_point[0]},  y {self.click_point[1]}" if self.click_point
                                   else "no spot picked yet")
        if self.last_bbox:
            x1, y1, x2, y2 = self.last_bbox
            self.area_label.configure(text=f"Last area: {x2 - x1} x {y2 - y1} at ({x1}, {y1})")
        else:
            self.area_label.configure(text="No area chosen yet")

    def _area_changed(self):
        state = "normal" if self.v["area_mode"].get() == "fixed" else "disabled"
        self.w_entry.configure(state=state)
        self.h_entry.configure(state=state)
        self._update_steps()

    def _mode_changed(self):
        self.count_entry.configure(state="normal" if self.v["mode"].get() == "count" else "disabled")

    def _pick_folder(self):
        path = filedialog.askdirectory(title="Choose the folder to save snapshots in")
        if path:
            self.v["out"].set(path)

    def _pick_point(self):
        """Dim the screen and let the user click the spot the mouse should click before each snapshot."""
        if self.state_name != "idle" or self.overlay is not None:
            return
        self.state_name = "selecting"
        self.status.configure(text="Click the spot...")
        hide = bool(self.v["minimize"].get())
        if hide:
            self.top.iconify()

        def chosen(point):
            self.overlay = None
            self.state_name = "idle"
            if hide:
                self.top.deiconify()
            if point is not None:
                self.click_point = (int(point[0]), int(point[1]))
                self.v["click_on"].set(True)
                self._save_settings()
                self._write_log(f"Mouse click spot: x {self.click_point[0]}, y {self.click_point[1]}")
            self._update_steps()

        def show():
            self.overlay = Overlay(self.top, None, chosen, point=True)

        self.after(350 if hide else 10, show)        # give the window time to get out of the way

    def _update_example(self):
        try:
            digits = int(self.v["digits"].get())
            start = self.v["start"].get().strip()
            n = int(start) if start else 1
            name = f"{self.v['prefix'].get()}_{n:0{digits}d}.{self.v['format'].get()}"
            note = "" if start else "   (Start # blank = continue after the highest number already in the folder)"
            self.example.configure(text=f"Files: {name}, then counting up{note}")
        except ValueError:
            self.example.configure(text="")

    def _open_folder(self):
        folder = Path(self.v["out"].get()).expanduser()
        if not folder.is_dir():
            messagebox.showinfo(APP, f"That folder does not exist yet:\n{folder}")
            return
        if IS_WINDOWS:
            os.startfile(folder)  # noqa: S606
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(folder)])
        else:
            subprocess.Popen(["xdg-open", str(folder)])

    def _send(self):
        """Hand the snapshot folder to the watermark tab."""
        if self.state_name != "idle":
            return
        folder = Path(self.v["out"].get().strip() or ".").expanduser()
        if not folder.is_dir() or not any(is_picture(f) for f in folder.iterdir()):
            messagebox.showinfo(APP, f"There are no snapshots in\n{folder}\n\n"
                                     "Take the snapshots first. (png is the format to keep: jpg blurs the edges of letters.)")
            return
        if self.on_send:
            self.on_send(folder)

    def _write_log(self, text):
        self.log_box.configure(state="normal")
        self.log_box.insert("end", text + "\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    # ---- hotkey ----
    def _start_listener(self):
        if self.listener:
            self.listener.stop()
            self.listener = None
        combo = HOTKEYS.get(self.v["hotkey"].get(), "<f9>")
        try:
            if keyboard is None:
                raise RuntimeError(KEYBOARD_ERROR or "pynput is not available")
            self.listener = keyboard.GlobalHotKeys({combo: lambda: self.events.put(("hotkey",))})
            self.listener.daemon = True
            self.listener.start()
        except Exception as exc:
            self.listener = None
            self._write_log(f"ERROR: could not listen for the hotkey: {exc}")
        self._update_steps()

    def _on_hotkey(self):
        if self.state_name == "capturing":
            self._stop()
            return
        if self.state_name == "selecting":
            return
        if not self.winfo_ismapped() and self.top.state() != "iconic":
            return                        # the other tab is showing: the hotkey is off there
        try:
            options = self._read_options()
        except ValueError as exc:
            self.top.deiconify()
            self.top.lift()
            messagebox.showerror(APP, str(exc))
            return
        self._save_settings()
        self.pending_options = options
        self.target_window = foreground_window()   # the browser: it gets the key presses
        if options["minimize"]:
            self.top.iconify()

        if options["reuse"] and self.last_bbox:
            self._area_chosen(self.last_bbox)
            return
        self.state_name = "selecting"
        self.status.configure(text="Select the area...")
        fixed = (options["width"], options["height"]) if options["area_mode"] == "fixed" else None
        self.overlay = Overlay(self.top, fixed, self._area_chosen)

    def _area_chosen(self, bbox):
        self.overlay = None
        restore_foreground(self.target_window)
        if bbox is None:
            self.state_name = "idle"
            self._write_log("Selection cancelled.")
            self._update_steps()
            if self.pending_options["minimize"]:
                self.top.deiconify()
            return
        self.last_bbox = tuple(int(c) for c in bbox)
        self._save_settings()
        x1, y1, x2, y2 = self.last_bbox
        self._write_log(f"Area: {x2 - x1} x {y2 - y1} at ({x1}, {y1})")
        self._begin_capture(self.pending_options, self.last_bbox)

    # ---- run ----
    def _read_options(self) -> dict:
        g = lambda name: self.v[name].get().strip() if isinstance(self.v[name], tk.StringVar) else self.v[name].get()

        def number(name, label, kind=int, low=None):
            try:
                value = kind(g(name))
            except ValueError:
                raise ValueError(f"{label} must be a number.")
            if low is not None and value < low:
                raise ValueError(f"{label} must be at least {low}.")
            return value

        if not g("out"):
            raise ValueError("Choose a folder to save to.")
        if not g("prefix") or re.search(r'[\\/:*?"<>|]', g("prefix")):
            raise ValueError('Name prefix is required and cannot contain  \\ / : * ? " < > |')
        fixed = g("area_mode") == "fixed"
        click = pre_key = None
        if g("click_on"):
            if mouse is None:
                raise ValueError("The mouse cannot be controlled on this computer (the pynput package did not load its mouse part).")
            if not self.click_point:
                raise ValueError('"Click the mouse at" is ticked, but no spot is picked yet. Press "Pick the spot..." first.')
            click = (self.click_point[0], self.click_point[1], g("click_button"))
        if g("pre_key_on"):
            try:
                pre_key = parse_key(g("pre_key"))
            except ValueError as exc:
                raise ValueError(f"Key to press before each snapshot: {exc}")
        return {
            "click": click, "pre_key": pre_key,
            "pre_wait": number("pre_wait", "Wait after the click / key", float, 0),
            "key_parsed": parse_key(g("key")), "out": g("out"), "prefix": g("prefix"),
            "area_mode": g("area_mode"), "reuse": g("reuse"), "minimize": g("minimize"),
            "width": number("width", "Width", low=5) if fixed else 0,
            "height": number("height", "Height", low=5) if fixed else 0,
            "mode": g("mode"),
            "count": number("count", "Number of snapshots", low=1) if g("mode") == "count" else 0,
            "delay": number("delay", "Wait after key", float, 0),
            "first_wait": number("first_wait", "Wait before first", float, 0.2),
            "start": number("start", "Start #", low=0) if g("start") else None,
            "digits": number("digits", "Digits", low=1),
            "format": g("format"),
        }

    def _save_settings(self):
        try:
            data = {k: var.get() for k, var in self.v.items()}
            data["last_bbox"] = list(self.last_bbox) if self.last_bbox else None
            data["click_point"] = list(self.click_point) if self.click_point else None
            SETTINGS_FILE.write_text(json.dumps(data, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _begin_capture(self, options, bbox):
        self.state_name = "capturing"
        self.eta.reset()
        self.eta.update(0, options["count"] if options["mode"] == "count" else 0)
        self.stop_event.clear()
        self.stop_btn.configure(state="normal")
        self.send_btn.configure(state="disabled")
        self.status.configure(text="Snapping...")
        self.bar.stop()
        self.bar.configure(mode="determinate", value=0, maximum=max(options["count"], 1))
        if options["mode"] == "until_same":
            self.bar.configure(mode="indeterminate")
            self.bar.start(15)

        def work():
            log = lambda text, progress=None: self.events.put(("log", text, progress))
            try:
                taken = capture(options, bbox, log, self.stop_event)
                stopped = " (stopped)" if self.stop_event.is_set() else ""
                self.events.put(("done", f"Done: {taken} snapshot(s){stopped} in {Path(options['out']).expanduser()}"))
            except Exception as exc:
                self.events.put(("done", f"ERROR: {exc}"))

        self.worker = threading.Thread(target=work, daemon=True)
        self.worker.start()

    def _stop(self):
        self.stop_event.set()
        self.status.configure(text="Stopping...")

    def _poll(self):
        try:
            while True:
                event = self.events.get_nowait()
                kind = event[0]
                if kind == "hotkey":
                    self._on_hotkey()
                elif kind == "log":
                    self._write_log(event[1])
                    if event[2]:
                        taken, total = event[2]
                        self.eta.update(taken, total or 0)
                        left = self.eta.text()
                        self.status.configure(text=(f"{taken} of {total}" + (f"   -   {left}" if left else ""))
                                              if total else f"{taken} taken")
                        if total:
                            self.bar.configure(value=taken)
                elif kind == "done":
                    self._write_log(event[1])
                    self.bar.stop()
                    self.bar.configure(mode="determinate")
                    self.stop_btn.configure(state="disabled")
                    self.send_btn.configure(state="normal")
                    self.state_name = "idle"
                    self._update_steps()
                    self.top.bell()
                    if self.pending_options and self.pending_options["minimize"]:
                        self.top.deiconify()
        except queue.Empty:
            pass
        self.after(100, self._poll)

    def shutdown(self):
        self.stop_event.set()
        if self.listener:
            self.listener.stop()
        self._save_settings()


# =============================================================================
# PART 3 - REMOVE-WATERMARK TAB
# =============================================================================

MAX_SAMPLES = 30
ON, OFF = "☑", "☐"


class CleanTab(ttk.Frame if ttk else object):
    """Tab 2: learn the watermark from a folder of PNG pages, review it, save cleaned copies."""

    def __init__(self, master, folder=None):
        super().__init__(master)

        self.files = {}         # (w, h) -> [Path]
        self.models = {}        # (w, h) -> WatermarkModel
        self.checked = {}       # (w, h) -> set of group ids to remove
        self.protect = {}       # (w, h) -> [(x0, y0, x1, y1)]
        self.size = None        # current (w, h)
        self.page = 0
        self.zoom = None        # None = fit to window
        self._z = 1.0
        self._tkimg = None
        self._page_cache = (None, None)
        self._render_job = None
        self._drag = None
        self._busy = False
        self.q = queue.Queue()

        self._build()
        self.after(80, self._poll)
        if folder:
            self.in_var.set(str(Path(folder).resolve()))
            self._default_output()
            self.after(200, self.analyze)

    # ------------------------------------------------------------------ layout

    def _build(self):
        top = ttk.Frame(self, padding=(8, 8, 8, 4))
        top.pack(fill="x")
        top.columnconfigure(1, weight=1)
        self.in_var, self.out_var = tk.StringVar(), tk.StringVar()
        ttk.Label(top, text="Pages folder").grid(row=0, column=0, sticky="w")
        ttk.Entry(top, textvariable=self.in_var).grid(row=0, column=1, sticky="ew", padx=6)
        ttk.Button(top, text="Browse...", command=self._browse_in).grid(row=0, column=2)
        self.analyze_btn = ttk.Button(top, text="Analyze", style="Go.TButton", command=self.analyze)
        self.analyze_btn.grid(row=0, column=3, padx=(8, 0), sticky="ew")
        ttk.Label(top, text="Save cleaned to").grid(row=1, column=0, sticky="w", pady=(4, 0))
        ttk.Entry(top, textvariable=self.out_var).grid(row=1, column=1, sticky="ew", padx=6, pady=(4, 0))
        ttk.Button(top, text="Browse...", command=self._browse_out).grid(row=1, column=2, pady=(4, 0))
        self.run_btn = ttk.Button(top, text="Remove & Save", style="Go.TButton", command=self.run, state="disabled")
        self.run_btn.grid(row=1, column=3, padx=(8, 0), pady=(4, 0), sticky="ew")

        # three short rows of options, so that nothing is cut off in a narrow window
        extra = ttk.Frame(top)
        extra.grid(row=2, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        self.pdf_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(extra, variable=self.pdf_var, command=self._pdf_mode,
                        text="Also save one searchable PDF (OCR)").pack(side="left")
        self.retype_var = tk.BooleanVar(value=False)
        self.retype_chk = ttk.Checkbutton(extra, variable=self.retype_var, state="disabled",
                                          text="Re-typeset text in the PDF (sharp at any zoom)")
        self.retype_chk.pack(side="left", padx=(14, 0))
        extra = ttk.Frame(top)
        extra.grid(row=3, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        self.html_var = tk.BooleanVar(value=False)
        self.docx_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(extra, variable=self.docx_var, text="Also save a Word file (.docx), laid out as").pack(side="left")
        self.layout_box = ttk.Combobox(extra, state="readonly", width=48,
                                       values=["Paragraphs and tables - lines as in the original", "Paragraphs and tables - free-flowing text", "Exact page copy (text boxes)",
                                               "Structured document - headings, lists, flowing text"])
        self.layout_box.current(0)
        self.layout_box.pack(side="left", padx=(6, 0))
        extra = ttk.Frame(top)
        extra.grid(row=4, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        ttk.Label(extra, text="Pages:").pack(side="left", padx=(0, 4))
        self.pages_var = tk.StringVar(value="all")
        ttk.Entry(extra, textvariable=self.pages_var, width=9).pack(side="left")
        ttk.Label(extra, text="all, or a few to test first, e.g. 1-3", foreground="#555").pack(side="left", padx=(6, 0))
        ttk.Label(extra, text="Sharpen text:").pack(side="left", padx=(24, 4))
        self.enh_box = ttk.Combobox(extra, state="readonly", width=24,
                                    values=["Off", "Enlarge 2x and sharpen", "Enlarge 3x and sharpen"])
        self.enh_box.current(0)
        self.enh_box.pack(side="left")
        extra = ttk.Frame(top)
        extra.grid(row=5, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        ttk.Label(extra, text="Text replacement:").pack(side="left", padx=(0, 4))
        self.strict_box = ttk.Combobox(extra, state="readonly", width=48, values=["Strict - only confirmed words (default)", "Balanced - more words, rare errors possible", "Everything the OCR read - errors likely"])
        self.strict_box.current(0)
        self.strict_box.pack(side="left")
        self.dict_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(extra, variable=self.dict_var, text="Use the dictionary").pack(side="left", padx=(14, 0))
        ttk.Label(extra, text="CPU cores:").pack(side="left", padx=(24, 4))
        self.jobs_var = tk.IntVar(value=default_jobs())
        ttk.Spinbox(extra, from_=1, to=max(1, os.cpu_count() or 1), width=3, textvariable=self.jobs_var).pack(side="left")
        extra = ttk.Frame(top)
        extra.grid(row=9, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        ttk.Checkbutton(extra, variable=self.html_var, text="Also save a web page (.html): every paragraph, picture and table a box "
                                                            "you can edit, move and resize in your browser").pack(side="left")
        extra = ttk.Frame(top)
        extra.grid(row=7, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        ttk.Label(extra, text="Unidentified words:").pack(side="left", padx=(0, 4))
        self.mark_docx = tk.BooleanVar(value=True)
        ttk.Checkbutton(extra, text="highlight in the Word file", variable=self.mark_docx).pack(side="left")
        self.mark_pdf = tk.BooleanVar(value=False)
        ttk.Checkbutton(extra, text="highlight in the PDF", variable=self.mark_pdf).pack(side="left", padx=(12, 0))
        self.word_pics = tk.BooleanVar(value=False)
        ttk.Checkbutton(extra, text="Word file: the word's own picture instead of a guess",
                        variable=self.word_pics).pack(side="left", padx=(12, 0))
        extra = ttk.Frame(top)
        extra.grid(row=6, column=1, columnspan=3, sticky="w", padx=6, pady=(4, 0))
        ttk.Label(extra, text="Fonts:").pack(side="left", padx=(0, 4))
        self.fonts_box = ttk.Combobox(extra, state="readonly", width=70, values=["Automatic", "One font throughout - the original typeface is not on this computer", "Match line by line - ordinary fonts (Arial, Times New Roman...)"])
        self.fonts_box.current(0)
        self.fonts_box.pack(side="left")

        body = ttk.Panedwindow(self, orient="horizontal")
        body.pack(fill="both", expand=True, padx=8, pady=4)

        # ---- left: what was found
        left = ttk.Frame(body, width=360)
        body.add(left, weight=0)

        row = ttk.Frame(left)
        row.pack(fill="x")
        ttk.Label(row, text="Page size").pack(side="left")
        self.size_box = ttk.Combobox(row, state="readonly", width=24)
        self.size_box.pack(side="left", padx=6, fill="x", expand=True)
        self.size_box.bind("<<ComboboxSelected>>", lambda e: self._pick_size(self.size_box.current()))

        ttk.Label(left, text="Static elements found (click to toggle)").pack(anchor="w", pady=(8, 2))
        tree_frame = ttk.Frame(left)
        tree_frame.pack(fill="both", expand=True)
        cols = ("rm", "id", "kind", "op", "area")
        self.tree = ttk.Treeview(tree_frame, columns=cols, show="headings", selectmode="none", height=12)
        for c, text, w, anchor in (("rm", "Remove", 72, "center"), ("id", "#", 36, "center"),
                                   ("kind", "Type", 90, "w"), ("op", "Opacity", 64, "center"),
                                   ("area", "Pixels", 70, "e")):
            self.tree.heading(c, text=text)
            self.tree.column(c, width=w, anchor=anchor, stretch=(c == "kind"))
        self.tree.tag_configure("on", foreground="#0a7a0a")
        self.tree.tag_configure("off", foreground="#a05a00")
        sb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.tree.bind("<ButtonRelease-1>", self._tree_click)

        row = ttk.Frame(left)
        row.pack(fill="x", pady=4)
        ttk.Button(row, text="Watermarks only", command=self._check_default).pack(side="left")
        ttk.Button(row, text="None", command=self._check_none).pack(side="left", padx=4)

        opts = ttk.LabelFrame(left, text="Options", padding=6)
        opts.pack(fill="x", pady=(6, 0))
        self.auto_alpha = tk.BooleanVar(value=True)
        ttk.Checkbutton(opts, text="Fit watermark opacity automatically", variable=self.auto_alpha,
                        command=self._alpha_mode).pack(anchor="w")
        row = ttk.Frame(opts)
        row.pack(fill="x")
        self.alpha_var = tk.DoubleVar(value=0.30)
        self.alpha_scale = ttk.Scale(row, from_=0.02, to=MAX_ALPHA, variable=self.alpha_var,
                                     command=lambda v: self.alpha_lbl.config(text=f"{float(v):.2f}"))
        self.alpha_scale.pack(side="left", fill="x", expand=True)
        self.alpha_scale.bind("<ButtonRelease-1>", lambda e: self._apply())
        self.alpha_lbl = ttk.Label(row, text="auto", width=5)
        self.alpha_lbl.pack(side="left")
        self.alpha_scale.state(["disabled"])

        row = ttk.Frame(opts)
        row.pack(fill="x", pady=(6, 0))
        ttk.Label(row, text="Noise tolerance").pack(side="left")
        self.tol_var = tk.DoubleVar(value=2.0)
        tol = ttk.Spinbox(row, from_=0, to=12, increment=0.5, width=5, textvariable=self.tol_var,
                          command=self._schedule_render)
        tol.pack(side="left", padx=6)
        tol.bind("<Return>", lambda e: self._schedule_render())

        keep = ttk.LabelFrame(left, text="Keep-out boxes (never touched)", padding=6)
        keep.pack(fill="x", pady=(6, 0))
        self.draw_mode = tk.BooleanVar(value=False)
        ttk.Checkbutton(keep, text="Draw a keep-out box on the page", variable=self.draw_mode,
                        command=self._cursor).pack(anchor="w")
        row = ttk.Frame(keep)
        row.pack(fill="x", pady=(4, 0))
        self.keep_lbl = ttk.Label(row, text="none")
        self.keep_lbl.pack(side="left")
        ttk.Button(row, text="Clear", command=self._clear_protect).pack(side="right")
        ttk.Button(row, text="Undo", command=self._undo_protect).pack(side="right", padx=4)

        # ---- right: the page
        right = ttk.Frame(body)
        body.add(right, weight=1)
        bar = ttk.Frame(right)
        bar.pack(fill="x", pady=(0, 4))
        self.view = tk.StringVar(value="detect")
        for text, val in (("Detection", "detect"), ("Original", "orig"), ("Cleaned", "clean")):
            ttk.Radiobutton(bar, text=text, value=val, variable=self.view,
                            command=self._schedule_render).pack(side="left", padx=(0, 8))
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=6)
        ttk.Button(bar, text="<", width=3, command=lambda: self._step(-1)).pack(side="left")
        self.page_box = ttk.Combobox(bar, state="readonly", width=28)
        self.page_box.pack(side="left", padx=4)
        self.page_box.bind("<<ComboboxSelected>>", lambda e: self._pick_page(self.page_box.current()))
        ttk.Button(bar, text=">", width=3, command=lambda: self._step(1)).pack(side="left")
        ttk.Button(bar, text="100%", width=6, command=lambda: self._set_zoom(1.0)).pack(side="right")
        ttk.Button(bar, text="Fit", width=5, command=lambda: self._set_zoom(None)).pack(side="right", padx=4)
        ttk.Button(bar, text="+", width=3, command=lambda: self._zoom_by(1.25)).pack(side="right")
        ttk.Button(bar, text="-", width=3, command=lambda: self._zoom_by(0.8)).pack(side="right", padx=(0, 4))

        cf = ttk.Frame(right)
        cf.pack(fill="both", expand=True)
        cf.rowconfigure(0, weight=1)
        cf.columnconfigure(0, weight=1)
        self.canvas = tk.Canvas(cf, bg="#5a5f66", highlightthickness=0)
        vs = ttk.Scrollbar(cf, orient="vertical", command=self.canvas.yview)
        hs = ttk.Scrollbar(cf, orient="horizontal", command=self.canvas.xview)
        self.canvas.configure(xscrollcommand=hs.set, yscrollcommand=vs.set)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        hs.grid(row=1, column=0, sticky="ew")
        c = self.canvas
        c.bind("<Configure>", lambda e: self.zoom is None and self._schedule_render(150))
        c.bind("<ButtonPress-1>", self._press)
        c.bind("<B1-Motion>", self._motion)
        c.bind("<ButtonRelease-1>", self._release)
        c.bind("<MouseWheel>", self._wheel)                       # Windows / macOS
        c.bind("<Button-4>", lambda e: self._wheel(e, 120))       # Linux
        c.bind("<Button-5>", lambda e: self._wheel(e, -120))
        top_win = self.winfo_toplevel()                           # arrow keys page through, when this tab shows
        top_win.bind("<Left>", lambda e: self._arrow(-1), add="+")
        top_win.bind("<Right>", lambda e: self._arrow(1), add="+")

        foot = ttk.Frame(self, padding=(8, 2, 8, 6))
        foot.pack(fill="x")
        self.status = tk.StringVar(value="Choose a folder of page pictures (PNG, JPG, TIFF...) and press Analyze.")
        ttk.Label(foot, textvariable=self.status).pack(side="left", fill="x", expand=True)
        self.open_btn = ttk.Button(foot, text="Open output folder", command=self._open_out, state="disabled")
        self.open_btn.pack(side="right")
        self.review_btn = ttk.Button(foot, text="Review words...", command=lambda: self._review(False))
        self.review_btn.pack(side="right", padx=(0, 6))
        self._last_review = None
        self.eta = Eta()
        self.eta_lbl = ttk.Label(foot, foreground="#444")
        self.prog = ttk.Progressbar(foot, length=200)
        self.prog.pack(side="right", padx=8)
        self.eta_lbl.pack(side="right", padx=(8, 0))

    # ------------------------------------------------------------------ small helpers

    @property
    def model(self):
        return self.models.get(self.size)

    def _default_output(self):
        p = self.in_var.get().strip()
        if p:
            p = Path(p)
            self.out_var.set(str(p.parent / (p.name + "_cleaned")))

    def _browse_in(self):
        d = filedialog.askdirectory(title="Folder of page pictures (PNG, JPG, TIFF, BMP, WebP, GIF)", initialdir=self.in_var.get() or None)
        if d:
            self.in_var.set(str(Path(d)))
            self._default_output()

    def _browse_out(self):
        d = filedialog.askdirectory(title="Folder for cleaned pages", initialdir=self.out_var.get() or None)
        if d:
            self.out_var.set(str(Path(d)))

    def _pdf_mode(self):
        self.retype_chk.config(state="normal" if self.pdf_var.get() else "disabled")

    def _open_out(self):
        p = self.out_var.get()
        if not os.path.isdir(p):
            return
        if sys.platform.startswith("win"):
            os.startfile(p)  # type: ignore[attr-defined]
        else:
            subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", p])

    def _set_busy(self, busy):
        self._busy = busy
        self.analyze_btn.config(state="disabled" if busy else "normal")
        self.run_btn.config(state="normal" if (not busy and self.models) else "disabled")
        self.config(cursor="watch" if busy else "")

    def _cursor(self):
        self.canvas.config(cursor="crosshair" if self.draw_mode.get() else "")

    # ------------------------------------------------------------------ worker plumbing

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                getattr(self, "_on_" + msg[0])(*msg[1:])
        except queue.Empty:
            pass
        if self._busy:
            self.eta_lbl.config(text=self.eta.text())
        self.after(80, self._poll)

    def _on_status(self, text):
        self.status.set(text)

    def _on_progress(self, done, total):
        self.prog.config(maximum=max(total, 1), value=done)
        self.eta.update(done, total)
        self.eta_lbl.config(text=self.eta.text())

    def _on_error(self, text):
        self._set_busy(False)
        self.prog.config(value=0)
        self.eta.reset()
        self.eta_lbl.config(text="")
        self.status.set("Failed.")
        messagebox.showerror(APP, text)

    # ------------------------------------------------------------------ analyze

    def analyze(self):
        if self._busy:
            return
        folder = self.in_var.get().strip()
        if not os.path.isdir(folder):
            messagebox.showwarning(APP, "Choose the folder that holds the page pictures.")
            return
        if not self.out_var.get().strip():
            self._default_output()
        self._set_busy(True)
        self.status.set("Reading pages...")
        threading.Thread(target=self._analyze_worker, args=(folder,), daemon=True).start()

    def _analyze_worker(self, folder):
        try:
            files = _gather([folder])
            if not files:
                raise RuntimeError("No page pictures (PNG, JPG, TIFF, BMP, WebP, GIF) in that folder.")
            by_size = {}
            for f in files:
                by_size.setdefault(picture_size(f), []).append(f)
            models = {}
            learnable = [(s, fl) for s, fl in by_size.items() if len(fl) >= 3]
            take = {size: min(len(fl), sample_limit(size[0], size[1], MAX_SAMPLES)) for size, fl in learnable}
            total = sum(n + 1 for n in take.values())
            done = 0
            for size, fl in sorted(learnable, key=lambda kv: -len(kv[1])):
                self.q.put(("status", f"Learning the watermark from {len(fl)} pages at {size[0]} x {size[1]}..."))
                idx = np.unique(np.linspace(0, len(fl) - 1, take[size]).round().astype(int))
                sample = []
                for i in idx:
                    sample.append(load_png(fl[i])[0])
                    done += 1
                    self.q.put(("progress", done, total))
                models[size] = learn_model(sample)
                del sample
                done += 1
                self.q.put(("progress", done, total))
            self.q.put(("analyzed", by_size, models))
        except Exception as e:  # shown to the user
            log_error("watermark tab")
            self.q.put(("error", friendly(e)))

    def _on_analyzed(self, by_size, models):
        self.files, self.models = by_size, models
        self.checked = {s: {g.id for g in m.groups if g.selected} for s, m in models.items()}
        self.protect = {s: [] for s in models}
        self._page_cache = (None, None)
        self.prog.config(value=0)
        self.eta.reset()
        self.eta_lbl.config(text="")
        self._set_busy(False)
        if not models:
            self.size = None
            self.size_box.config(values=[])
            self.size_box.set("")
            self._fill_tree()
            self._schedule_render()
            self.status.set("Need at least 3 pages of the same pixel size to learn a watermark.")
            return
        sizes = sorted(models, key=lambda s: -len(by_size[s]))
        self._sizes = sizes
        self.size_box.config(values=[f"{w} x {h}  ({len(by_size[(w, h)])} pages)" for w, h in sizes])
        self._pick_size(0)
        skipped = sum(len(fl) for s, fl in by_size.items() if s not in models)
        found = sum(len(self.checked[s]) for s in models)
        text = (f"Found {found} watermark element(s). Check the Detection view, then Remove & Save."
                if found else
                "No translucent watermark found. If one of the listed elements is the watermark, tick it.")
        if skipped:
            text += f"  ({skipped} page(s) in odd sizes will be copied unchanged.)"
        self.status.set(text)

    # ------------------------------------------------------------------ selection

    def _pick_size(self, i):
        self.size = self._sizes[i]
        self.size_box.current(i)
        names = [f.name for f in self.files[self.size]]
        self.page_box.config(values=names)
        self.page = 0
        self.page_box.current(0)
        self.view.set("detect")
        self._fill_tree()
        self._update_keep_label()
        self._schedule_render()

    def _pick_page(self, i):
        self.page = i
        self.page_box.current(i)
        if self.view.get() == "detect":
            self.view.set("clean")
        self._schedule_render()

    def _arrow(self, d):
        if self.winfo_ismapped() and not isinstance(self.focus_get(), (tk.Entry, ttk.Entry)):
            self._step(d)

    def _step(self, d):
        if self.model is None:
            return
        n = len(self.files[self.size])
        self._pick_page((self.page + d) % n)

    def _fill_tree(self):
        self.tree.delete(*self.tree.get_children())
        m = self.model
        if m is None:
            return
        on = self.checked[self.size]
        for g in m.groups:
            kind = {"translucent": "watermark", "opaque": "solid", "mixed": "mixed"}[g.kind]
            op = f"{g.alpha:.2f}" + ("" if g.fitted or g.kind == "opaque" else " ?")
            self.tree.insert("", "end", iid=str(g.id), tags=("on" if g.id in on else "off",),
                             values=(ON if g.id in on else OFF, g.id, kind, op, f"{g.area:,}"))

    def _apply(self):
        """Push the ticked groups / keep-out boxes / opacity into the model and redraw."""
        m = self.model
        if m is None:
            return
        alpha = None if self.auto_alpha.get() else float(self.alpha_var.get())
        m.select(ids=sorted(self.checked[self.size]), protect=self.protect[self.size], alpha=alpha)
        self._fill_tree()
        self._schedule_render()

    def _toggle(self, gid):
        on = self.checked[self.size]
        on.symmetric_difference_update({gid})
        self._apply()

    def _tree_click(self, event):
        iid = self.tree.identify_row(event.y)
        if iid and not self._busy:
            self._toggle(int(iid))

    def _check_default(self):
        if self.model is not None and not self._busy:
            self.checked[self.size] = {g.id for g in self.model.groups if g.kind != "opaque"}
            self._apply()

    def _check_none(self):
        if self.model is not None and not self._busy:
            self.checked[self.size] = set()
            self._apply()

    def _alpha_mode(self):
        self.alpha_scale.state(["disabled"] if self.auto_alpha.get() else ["!disabled"])
        if self.auto_alpha.get():
            self.alpha_lbl.config(text="auto")
        if not self.auto_alpha.get() and self.model is not None:
            sel = [g.alpha for g in self.model.groups if g.selected]
            if sel:
                self.alpha_var.set(max(sel))
                self.alpha_lbl.config(text=f"{max(sel):.2f}")
        self._apply()

    def _update_keep_label(self):
        n = len(self.protect.get(self.size, []))
        self.keep_lbl.config(text="none" if n == 0 else f"{n} box{'es' if n > 1 else ''}")

    def _undo_protect(self):
        if self.protect.get(self.size):
            self.protect[self.size].pop()
            self._update_keep_label()
            self._apply()

    def _clear_protect(self):
        if self.protect.get(self.size):
            self.protect[self.size].clear()
            self._update_keep_label()
            self._apply()

    # ------------------------------------------------------------------ drawing

    def _page_rgb(self):
        path = self.files[self.size][self.page]
        if self._page_cache[0] != path:
            self._page_cache = (path, load_png(path)[0])
        return self._page_cache[1]

    def _tolerance(self):
        try:
            return max(0.0, float(self.tol_var.get()))
        except (tk.TclError, ValueError):
            return 2.0

    def _schedule_render(self, delay=10):
        if self._render_job:
            self.after_cancel(self._render_job)
        self._render_job = self.after(delay, self.render)

    def render(self):
        self._render_job = None
        c = self.canvas
        c.delete("all")
        m = self.model
        if m is None:
            c.config(scrollregion=(0, 0, 1, 1))
            c.create_text(c.winfo_width() // 2, c.winfo_height() // 2, fill="#d8dce0",
                          text="Choose a folder of page pictures and press Analyze", font=("TkDefaultFont", 13))
            return
        view = self.view.get()
        note = ""
        if view == "detect":
            img = m.preview()
        else:
            img = self._page_rgb()
            if view == "clean":
                img, removed = m.remove(img, self._tolerance())
                note = ("watermark removed" if removed else
                        "no watermark detected on this page - it will be saved unchanged")
        h, w = img.shape[:2]
        if self.zoom is None:
            z = min((c.winfo_width() - 4) / w, (c.winfo_height() - 4) / h)
            z = max(0.02, min(z, 1.0))
        else:
            z = self.zoom
        z = min(z, max(0.05, math.sqrt(40e6 / (w * h))))        # a huge enlarged picture would eat the memory
        self._z = z
        pil = Image.fromarray(img)
        if abs(z - 1.0) > 1e-3:
            pil = pil.resize((max(1, round(w * z)), max(1, round(h * z))),
                             Image.LANCZOS if z < 1 else Image.NEAREST)
        self._tkimg = ImageTk.PhotoImage(pil)
        c.create_image(0, 0, anchor="nw", image=self._tkimg)
        c.config(scrollregion=(0, 0, pil.width, pil.height))
        for x0, y0, x1, y1 in self.protect[self.size]:
            c.create_rectangle(x0 * z, y0 * z, x1 * z, y1 * z, outline="#1e6fff", width=2, dash=(6, 4))
        if note and not self._busy:
            self.status.set(f"{self.files[self.size][self.page].name}: {note}")

    def _set_zoom(self, z):
        self.zoom = z
        self._schedule_render()

    def _zoom_by(self, f):
        self.zoom = float(np.clip(self._z * f, 0.05, 6.0))
        self._schedule_render()

    def _wheel(self, event, delta=None):
        delta = event.delta if delta is None else delta
        step = -1 if delta > 0 else 1
        if event.state & 0x4:            # Ctrl
            self._zoom_by(1.15 if delta > 0 else 1 / 1.15)
        elif event.state & 0x1:          # Shift
            self.canvas.xview_scroll(step * 3, "units")
        else:
            self.canvas.yview_scroll(step * 3, "units")

    # ------------------------------------------------------------------ mouse on the page

    def _img_xy(self, event):
        return self.canvas.canvasx(event.x) / self._z, self.canvas.canvasy(event.y) / self._z

    def _press(self, event):
        if self.model is None or self._busy:
            return
        self._drag = {"x": event.x, "y": event.y, "moved": False, "start": self._img_xy(event), "rect": None}
        if self.draw_mode.get():
            cx, cy = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            self._drag["rect"] = self.canvas.create_rectangle(cx, cy, cx, cy, outline="#1e6fff", width=2, dash=(6, 4))
        else:
            self.canvas.scan_mark(event.x, event.y)

    def _motion(self, event):
        d = self._drag
        if not d:
            return
        if abs(event.x - d["x"]) + abs(event.y - d["y"]) > 4:
            d["moved"] = True
        if d["rect"] is not None:
            x0, y0 = d["start"]
            self.canvas.coords(d["rect"], x0 * self._z, y0 * self._z,
                               self.canvas.canvasx(event.x), self.canvas.canvasy(event.y))
        elif d["moved"]:
            self.canvas.scan_dragto(event.x, event.y, gain=1)

    def _release(self, event):
        d, self._drag = self._drag, None
        if not d or self.model is None:
            return
        w, h = self.model.size
        x, y = self._img_xy(event)
        if d["rect"] is not None:
            self.canvas.delete(d["rect"])
            x0, y0 = d["start"]
            box = (int(np.clip(min(x0, x), 0, w)), int(np.clip(min(y0, y), 0, h)),
                   int(np.clip(max(x0, x), 0, w)), int(np.clip(max(y0, y), 0, h)))
            if box[2] - box[0] >= 3 and box[3] - box[1] >= 3:
                self.protect[self.size].append(box)
                self._update_keep_label()
                self._apply()
            return
        if d["moved"] or not (0 <= x < w and 0 <= y < h):
            return
        gid = int(self.model.grp_map[int(y), int(x)])
        if not gid:                                            # click inside a box but off the ink
            hits = [g for g in self.model.groups if g.bbox[0] <= x < g.bbox[2] and g.bbox[1] <= y < g.bbox[3]]
            if not hits:
                return
            gid = min(hits, key=lambda g: (g.bbox[2] - g.bbox[0]) * (g.bbox[3] - g.bbox[1])).id
        self._toggle(gid)

    # ------------------------------------------------------------------ remove & save

    def run(self):
        if self._busy or not self.models:
            return
        out = self.out_var.get().strip()
        if not out:
            messagebox.showwarning(APP, "Choose a folder to save the cleaned pages in.")
            return
        out = Path(out)
        all_files = [f for fl in self.files.values() for f in fl]
        if any(out.resolve() == f.parent.resolve() for f in all_files):
            messagebox.showwarning(APP, "The output folder must be different from the pages folder, "
                                                  "so the originals are never overwritten.")
            return
        wants_doc = self.pdf_var.get() or self.docx_var.get() or self.html_var.get()
        if not any(self.checked[s] for s in self.models) and not wants_doc:
            messagebox.showwarning(APP, "Nothing is ticked for removal, and no PDF or Word file is asked for.")
            return
        ordered = sorted(all_files, key=natural_key)
        try:
            picked = parse_pages(self.pages_var.get(), len(ordered))
        except ValueError as e:
            messagebox.showwarning(APP, str(e))
            return
        chosen = [ordered[i] for i in picked]
        tag = "" if len(chosen) == len(ordered) else "_pages_" + "".join(
            ch if ch.isalnum() or ch == "-" else "_" for ch in self.pages_var.get().strip())
        stem = Path(self.in_var.get().strip()).name + tag
        pdf = (out / (stem + ".pdf")) if self.pdf_var.get() else None
        docx = (out / (stem + ".docx")) if self.docx_var.get() else None
        self._web = (out / (stem + ".html")) if self.html_var.get() else None
        clash = (sum((out / f.name).exists() for f in chosen) + bool(pdf and pdf.exists())
                 + bool(docx and docx.exists()) + bool(self._web and self._web.exists()))
        if clash and not messagebox.askyesno(APP, f"{clash} file(s) in\n{out}\nwill be overwritten. Continue?"):
            return
        for s in self.models:                                   # make sure every size has its current choices
            alpha = None if self.auto_alpha.get() else float(self.alpha_var.get())
            self.models[s].select(ids=sorted(self.checked[s]), protect=self.protect[s], alpha=alpha)
        self._set_busy(True)
        scale = max(1, self.enh_box.current() + 1)
        retype = bool(pdf) and self.retype_var.get()
        try:
            jobs = max(1, int(self.jobs_var.get()))
        except (tk.TclError, ValueError):
            jobs = default_jobs()
        layout = ("flow", "free", "exact", "structured")[max(0, self.layout_box.current())]
        self._marks = (bool(self.mark_docx.get()), bool(self.mark_pdf.get()), bool(self.word_pics.get()))
        strict = ("strict", "balanced", "all")[max(0, self.strict_box.current())]
        self._use_dict = bool(self.dict_var.get())
        set_fonts(FONT_CHOICES[max(0, self.fonts_box.current())])
        threading.Thread(target=self._run_worker, daemon=True,
                         args=(out, self._tolerance(), pdf, scale, retype, jobs, docx, layout, chosen, strict)).start()

    def _run_worker(self, out, tol, pdf=None, scale=1, retype=False, jobs=None, docx=None, layout="flow", chosen=None,
                    strict="strict"):
        try:
            out.mkdir(parents=True, exist_ok=True)
            wanted = None if chosen is None else {Path(f) for f in chosen}
            total = sum(len(fl) for fl in self.files.values()) if wanted is None else len(wanted)
            done = cleaned = 0
            for size, fl in self.files.items():
                model = self.models.get(size)
                for f in fl:
                    if wanted is not None and Path(f) not in wanted:
                        continue
                    self.q.put(("status", f"Cleaning {f.name}  ({done + 1} of {total})"))
                    rgb, info = load_png(f)
                    removed = []
                    if model is not None:
                        rgb, removed = model.remove(rgb, tol)
                    if scale > 1:
                        rgb, info = enhance_page(rgb, info, scale)
                    save_png(out / (f.stem + ".png"), rgb, info)
                    cleaned += bool(removed)
                    done += 1
                    self.q.put(("progress", done, total))
            pdf_note = ""
            web = getattr(self, "_web", None)
            if pdf is not None or docx is not None or web is not None:      # a document problem must not lose the PNGs
                try:
                    self.q.put(("progress", 0, total))
                    self.q.put(("status", "Preparing OCR..."))
                    engine = ensure_ocr_packages(status=lambda t: self.q.put(("status", t)))
                    self.q.put(("status", f"Starting {engine}..."))
                    pages = sorted((out / f.name for fl in self.files.values() for f in fl
                                    if wanted is None or Path(f) in wanted), key=natural_key)
                    matching = retype or docx is not None or web is not None
                    marks = getattr(self, "_marks", (True, False, False))

                    def step(d, t, name):
                        self.q.put(("progress", d, t))
                        if name.startswith("reading text"):
                            self.q.put(("status", f"First pass - {name}  ({d} of {t})"))
                        else:
                            self.q.put(("status", f"{'Re-typesetting' if matching else 'OCR'} {name}  ({d} of {t})"))

                    if matching:
                        self.q.put(("status", "Matching fonts on the first pages (this takes a moment)..."))
                    st = build_documents(pages, pdf_path=pdf, docx_path=docx, html_path=web, retypeset=retype, jobs=jobs,
                                            answers=Path(out) / ANSWERS_FILE, highlight=marks[0],
                                            highlight_pdf=marks[1], word_pictures=marks[2],
                                            progress=step, docx_layout=layout, strictness=strict,
                                            use_dictionary=getattr(self, "_use_dict", True))
                    detail = (f"{st['replaced']:,} of {st['words']:,} words re-typeset as real text" if matching
                              else f"{st['lines']:,} text lines")
                    if st.get("repaired"):
                        detail += f"; {st['repaired']} reading(s) corrected with the dictionary"
                    if st.get("fonts"):
                        detail += f"; fonts: {st['fonts']}"
                    card = graphics_card_lines(st)
                    if card:                            # this tab has no log: it goes in the closing message
                        detail += "; " + card[0].rstrip(".")[0].lower() + card[0].rstrip(".")[1:]
                    if st.get("terms"):
                        detail += f"; {len(st['terms'])} term(s) learned from the document"
                    if st.get("enlarged"):
                        detail += f"; {st['enlarged']} page(s) with small type enlarged for reading"
                    for line in structure_lines(st)[:1]:
                        detail += "; " + line.strip().rstrip(".")
                    if st.get("word_pictured"):
                        detail += f"; {st['word_pictured']} page(s) put into the Word file as pictures (they would not fit as text)"
                    if st.get("failed"):
                        detail += f"; {st['failed']} page(s) could not be re-typeset and were kept as pictures"
                    if st.get("answers"):
                        detail += f"; {st['answers']} word(s) you typed in were used"
                    self._last_review = (st.get("review") or [], Path(out) / ANSWERS_FILE)
                    self._review_due = bool(st.get("review"))
                    made = " and ".join(p.name for p in (pdf, docx, web) if p is not None)
                    pdf_note = f" Also saved {made} ({detail}, {engine})."
                except Exception as e:
                    log_error("PDF / Word step")
                    self.q.put(("pdf_failed", friendly(e)))
                    pdf_note = " The PDF / Word file was NOT created."
            self.q.put(("ran", cleaned, total, str(out), pdf_note))
        except Exception as e:  # shown to the user
            log_error("watermark tab")
            self.q.put(("error", friendly(e)))

    def _review(self, ask):
        """Show the words the last run left as pictures, for typing in; then offer to run again."""
        if self._busy:
            return
        review, path = self._last_review or ([], Path(self.out_var.get().strip() or ".") / ANSWERS_FILE)
        offer_review(self.winfo_toplevel(), review, path, self.run, ask=ask)

    def _on_pdf_failed(self, text):
        messagebox.showerror(APP, "The cleaned PNG pages were saved, but the PDF / Word file "
                                            "could not be created:\n\n" + text[-1200:])

    def _on_ran(self, cleaned, total, out, pdf_note=""):
        self._set_busy(False)
        self.prog.config(value=0)
        self.eta.reset()
        self.eta_lbl.config(text="")
        self.open_btn.config(state="normal")
        same = total - cleaned
        text = f"Done: watermark removed from {cleaned} of {total} page(s)"
        if same:
            text += f"; {same} saved unchanged (no watermark detected or odd size)"
        self.status.set(text + f". Saved to {out}.{pdf_note}")
        try:                                             # the same closing message, kept beside the results
            (Path(out) / "snapclean_run_report.txt").write_text(
                f"{APP} {VERSION} - run report (Remove watermark tab)\n{time.strftime('%Y-%m-%d %H:%M:%S')}\n"
                f"Python {sys.version.split()[0]} on {sys.platform}\n\n{text}. Saved to {out}.{pdf_note}\n", encoding="utf-8")
        except OSError:
            pass
        if getattr(self, "_review_due", False):          # words were left as pictures: offer to type them in
            self._review_due = False
            self.after(300, lambda: self._review(True))



# =============================================================================
# PART 4 - REBUILD-A-PDF TAB
# =============================================================================

class RebuildTab(ttk.Frame if ttk else object):
    """Tab 3: a scanned, rasterised or otherwise poor PDF -> a new PDF and/or Word file."""

    def __init__(self, master, on_send=None):
        super().__init__(master, padding=12)
        self.on_send = on_send            # called with a folder of page pictures (for watermark removal)
        self.q = queue.Queue()
        self._busy = False
        self._report, self._report_to, self._report_t0, self._report_settings = [], None, None, []
        self._build()
        self.after(100, self._poll)

    def _build(self):
        pad = {"padx": 6, "pady": 4}
        self.columnconfigure(0, weight=1)
        ttk.Label(self, justify="left", text=(
            "For a PDF whose pages are pictures (a scan, a 'print to image' export) or whose text is broken - or for\n"
            "page pictures you already have - PNG, JPG, TIFF, BMP, WebP, GIF (pick a few files to try it out, or a whole folder).\n"
            "Each page is read as a picture; text that can be matched to a font on this computer is redrawn as real\n"
            "text in the same place, and everything else - figures, plots, table lines, text that does not match -\n"
            "stays exactly as it looks now.")).grid(row=0, column=0, sticky="w", padx=6, pady=(0, 8))

        f = ttk.LabelFrame(self, text="Files", padding=8)
        f.grid(row=1, column=0, sticky="ew")
        f.columnconfigure(1, weight=1)
        self.pdf_var, self.out_var = tk.StringVar(), tk.StringVar()
        self.png_files = []                # set when PNG files were picked instead of a PDF
        ttk.Label(f, text="PDF or page pictures").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.pdf_var).grid(row=0, column=1, sticky="ew", **pad)
        g = ttk.Frame(f)
        g.grid(row=0, column=2, **pad)
        ttk.Button(g, text="PDF...", width=8, command=self._pick_pdf).pack(side="left")
        ttk.Button(g, text="Pictures...", command=self._pick_pngs).pack(side="left", padx=(4, 0))
        ttk.Label(f, text="Save results to").grid(row=1, column=0, sticky="w", **pad)
        ttk.Entry(f, textvariable=self.out_var).grid(row=1, column=1, sticky="ew", **pad)
        ttk.Button(f, text="Browse...", command=self._pick_out).grid(row=1, column=2, sticky="ew", **pad)
        ttk.Label(f, text="Pages").grid(row=2, column=0, sticky="w", **pad)
        g = ttk.Frame(f)
        g.grid(row=2, column=1, sticky="w", **pad)
        self.pages_var = tk.StringVar(value="all")
        ttk.Entry(g, textvariable=self.pages_var, width=14).pack(side="left")
        ttk.Label(g, foreground="#555", text="all, or a few to test first - for example  1-3  or  2, 5, 9").pack(side="left", padx=8)

        f = ttk.LabelFrame(self, text="What to make", padding=8)
        f.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        self.want_pdf, self.want_docx = tk.BooleanVar(value=True), tk.BooleanVar(value=True)
        self.retype = tk.BooleanVar(value=True)
        ttk.Checkbutton(f, text="New PDF", variable=self.want_pdf).grid(row=0, column=0, sticky="w", **pad)
        ttk.Checkbutton(f, text="Re-typeset its text (sharp at any zoom); untick to keep the page pictures and "
                                "only add hidden search text", variable=self.retype).grid(row=0, column=1, sticky="w", **pad)
        ttk.Checkbutton(f, text="Word file (.docx)", variable=self.want_docx).grid(row=1, column=0, sticky="w", **pad)
        self.want_html = tk.BooleanVar(value=False)
        ttk.Checkbutton(f, text="Web page (.html)", variable=self.want_html).grid(row=5, column=0, sticky="w", **pad)
        ttk.Label(f, foreground="#555", text="every paragraph, picture and table a box you can edit, move and resize in your "
                                             "browser (E = edit text, G = move), then save or print").grid(row=5, column=1, sticky="w", **pad)
        g = ttk.Frame(f)
        g.grid(row=1, column=1, sticky="w", **pad)
        self.layout_box = ttk.Combobox(g, state="readonly", width=48,
                                       values=["Paragraphs and tables - lines as in the original", "Paragraphs and tables - free-flowing text", "Exact page copy (text boxes)",
                                               "Structured document - headings, lists, flowing text"])
        self.layout_box.current(0)
        self.layout_box.pack(side="left")
        self.mark = tk.BooleanVar(value=True)
        ttk.Checkbutton(g, text="Word file: highlight text the checks could not confirm", variable=self.mark).pack(side="left", padx=(14, 0))

        ttk.Label(f, text="Text replacement").grid(row=2, column=0, sticky="w", **pad)
        g = ttk.Frame(f)
        g.grid(row=2, column=1, sticky="w", **pad)
        self.strict_box = ttk.Combobox(g, state="readonly", width=48, values=["Strict - only confirmed words (default)", "Balanced - more words, rare errors possible", "Everything the OCR read - errors likely"])
        self.strict_box.current(0)
        self.strict_box.pack(side="left")
        self.dict_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(g, variable=self.dict_var, text="Use the dictionary (and snapclean_words.txt, if you make one)"
                        ).pack(side="left", padx=(14, 0))

        ttk.Label(f, text="Fonts").grid(row=3, column=0, sticky="w", **pad)
        self.fonts_box = ttk.Combobox(f, state="readonly", width=70, values=["Automatic", "One font throughout - the original typeface is not on this computer", "Match line by line - ordinary fonts (Arial, Times New Roman...)"])
        self.fonts_box.current(0)
        self.fonts_box.grid(row=3, column=1, sticky="w", **pad)

        ttk.Label(f, text="Unidentified words").grid(row=4, column=0, sticky="w", **pad)
        g = ttk.Frame(f)
        g.grid(row=4, column=1, sticky="w", **pad)
        self.word_pics = tk.BooleanVar(value=False)
        ttk.Checkbutton(g, text="Word file: put in the word's own picture instead of a guess",
                        variable=self.word_pics).pack(side="left")
        self.mark_pdf = tk.BooleanVar(value=False)
        ttk.Checkbutton(g, text="PDF: highlight them", variable=self.mark_pdf).pack(side="left", padx=(14, 0))

        f = ttk.Frame(self)
        f.grid(row=3, column=0, sticky="ew", pady=(8, 0))
        ttk.Label(f, text="Read pages at").pack(side="left", padx=6)
        self.dpi_box = ttk.Combobox(f, state="readonly", width=22,
                                    values=["Automatic (150-300 dpi)", "150 dpi (fast)", "200 dpi", "300 dpi (best, slow)"])
        self.dpi_box.current(0)
        self.dpi_box.pack(side="left")
        ttk.Label(f, text="CPU cores:").pack(side="left", padx=(24, 4))
        self.jobs_var = tk.IntVar(value=default_jobs())
        ttk.Spinbox(f, from_=1, to=max(1, os.cpu_count() or 1), width=3, textvariable=self.jobs_var).pack(side="left")

        f = ttk.Frame(self)
        f.grid(row=4, column=0, sticky="ew", pady=(12, 4))
        self.go_btn = ttk.Button(f, text="Rebuild", style="Go.TButton", command=self.run)
        self.go_btn.pack(side="left", padx=6)
        self.wm_btn = ttk.Button(f, text="Remove a watermark from it first  >", command=self.to_watermark)
        self.wm_btn.pack(side="left", padx=6)
        ttk.Button(f, text="Open folder", command=self._open_out).pack(side="left", padx=6)
        self.review_btn = ttk.Button(f, text="Review words...", command=lambda: self._review(False))
        self.review_btn.pack(side="left", padx=6)
        self._last_review = None

        self.eta = Eta()
        f = ttk.Frame(self)
        f.grid(row=5, column=0, sticky="ew", padx=6, pady=(6, 0))
        f.columnconfigure(0, weight=1)
        self.bar = ttk.Progressbar(f, mode="determinate")
        self.bar.grid(row=0, column=0, sticky="ew")
        self.eta_lbl = ttk.Label(f, foreground="#444", width=52, anchor="e")
        self.eta_lbl.grid(row=0, column=1, sticky="e", padx=(10, 0))
        f = ttk.Frame(self)
        f.grid(row=6, column=0, sticky="nsew", pady=(8, 0))
        self.rowconfigure(6, weight=1)
        f.columnconfigure(0, weight=1)
        f.rowconfigure(0, weight=1)
        self.log_box = tk.Text(f, height=8, state="disabled", wrap="word")
        self.log_box.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(f, command=self.log_box.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.log_box.configure(yscrollcommand=sb.set)

    # ---- small handlers
    def _pick_pdf(self):
        p = filedialog.askopenfilename(title="PDF to rebuild", filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")])
        if p:
            self.png_files = []
            self.pdf_var.set(str(Path(p)))
            if not self.out_var.get().strip():
                self.out_var.set(str(Path(p).parent / (Path(p).stem + "_rebuilt")))

    def _pick_pngs(self):
        files = filedialog.askopenfilenames(title="Page pictures (select one or more)",
                                           filetypes=[("Pictures", PICTURE_PATTERNS), ("PNG", "*.png"), ("JPEG", "*.jpg *.jpeg"),
                                                      ("TIFF", "*.tif *.tiff"), ("All files", "*.*")])
        if files:
            self.png_files = expand_pictures(sorted((Path(p) for p in files if is_picture(p)), key=natural_key))
            if not self.png_files:
                messagebox.showwarning(APP, "None of those is a picture this program reads (PNG, JPG, TIFF, BMP, WebP, GIF).")
                return
            folder = Path(files[0]).parent
            self.png_label = f"{len(self.png_files)} page picture(s) in {folder}"
            self.pdf_var.set(self.png_label)
            if not self.out_var.get().strip():
                self.out_var.set(str(folder.parent / (folder.name + "_rebuilt")))

    def _pick_out(self):
        d = filedialog.askdirectory(title="Folder for the results", initialdir=self.out_var.get() or None)
        if d:
            self.out_var.set(str(Path(d)))

    def _open_out(self):
        p = self.out_var.get().strip()
        if not os.path.isdir(p):
            return
        if IS_WINDOWS:
            os.startfile(p)  # noqa: S606
        else:
            subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", p])

    def _log(self, text):
        self.log_box.configure(state="normal")
        self.log_box.insert("end", text + "\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    def _set_busy(self, busy):
        self._busy = busy
        for b in (self.go_btn, self.wm_btn):
            b.config(state="disabled" if busy else "normal")
        self.config(cursor="watch" if busy else "")

    def _inputs(self):
        """(source, output folder, dpi, jobs, page text) or None. source is a PDF path or a list of PNG paths."""
        typed = self.pdf_var.get().strip()
        if self.png_files and typed == getattr(self, "png_label", None):
            src = list(self.png_files)
        elif os.path.isdir(typed):                          # a folder of PNG pages typed or pasted in
            src = expand_pictures(sorted((f for f in Path(typed).iterdir() if is_picture(f)), key=natural_key))
            if not src:
                messagebox.showwarning(APP, "There are no page pictures (PNG, JPG, TIFF, BMP, WebP, GIF) in that folder.")
                return None
        elif os.path.isfile(typed) and typed.lower().endswith(".pdf"):
            src = Path(typed)
        elif os.path.isfile(typed) and is_picture(typed):
            src = expand_pictures([Path(typed)])
        else:
            messagebox.showwarning(APP, "Choose a PDF file, or page pictures, to work on.")
            return None
        if not self.out_var.get().strip():
            first = src if isinstance(src, Path) else Path(typed) if os.path.exists(typed) else src[0].parent
            self.out_var.set(str(first.parent / (first.stem + "_rebuilt")))
        dpi = [None, 150, 200, 300][max(0, self.dpi_box.current())]
        try:
            jobs = max(1, int(self.jobs_var.get()))
        except (tk.TclError, ValueError):
            jobs = default_jobs()
        return src, Path(self.out_var.get().strip()), dpi, jobs, self.pages_var.get()

    def _save_report(self):
        """What this run did, kept as a text file beside its results: the settings, every log line, how
        long it took. It is what to look at - or send - when a run did not come out as hoped."""
        folder, started = getattr(self, "_report_to", None), getattr(self, "_report_t0", None)
        if not folder or not self._report:
            return
        try:
            took = time.time() - started if started else 0
            head = [f"{APP} {VERSION} - run report", time.strftime("%Y-%m-%d %H:%M:%S"),
                    f"Python {sys.version.split()[0]} on {sys.platform}", f"Took {int(took // 60)} min {int(took % 60)} s", ""]
            head += getattr(self, "_report_settings", []) + [""]
            Path(folder).mkdir(parents=True, exist_ok=True)
            (Path(folder) / "snapclean_run_report.txt").write_text("\n".join(head + self._report) + "\n", encoding="utf-8")
        except OSError:
            pass
        self._report = []

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                if msg[0] == "log":
                    self._log(msg[1])
                    self._report.append(msg[1])
                elif msg[0] == "progress":
                    self.bar.config(maximum=max(msg[2], 1), value=msg[1])
                    self.eta.update(msg[1], msg[2])
                elif msg[0] == "done":
                    self._save_report()
                    self._set_busy(False)
                    self.bar.config(value=0)
                    self.eta.reset()
                    self.winfo_toplevel().bell()
                    if msg[1]:
                        msg[1]()
                elif msg[0] == "error":
                    self._set_busy(False)
                    self.bar.config(value=0)
                    self.eta.reset()
                    self._log("FAILED: " + msg[1].splitlines()[0] if msg[1] else "FAILED")
                    self._report.append("FAILED:\n" + (msg[1] or ""))
                    self._save_report()
                    messagebox.showerror(APP, msg[1][-1500:])
        except queue.Empty:
            pass
        self.eta_lbl.config(text=self.eta.text() if self._busy else "")
        self.after(100, self._poll)

    # ---- the work
    def _pages(self, src, out, dpi, which):
        """The pages to work on, as PNG files: read out of the PDF, or the PNG files as they are."""
        engine = ensure_ocr_packages(status=lambda t: self.q.put(("log", t)))
        if isinstance(src, Path):
            import pymupdf as fitz
            with fitz.open(str(src)) as probe:
                wanted = parse_pages(which, len(probe))
                note = "" if len(wanted) == len(probe) else f" (pages {which.strip()} of {len(probe)})"
            self.q.put(("log", f"Reading {src.name} as pictures{note}..."))
            pages = pdf_to_pngs(src, out / (src.stem + "_pages"), dpi=dpi, pages=wanted,
                                progress=lambda d, t, name: self.q.put(("progress", d, t)))
            self.q.put(("log", f"  {len(pages)} page(s) saved in {pages[0].parent}" if pages else "  the PDF has no pages"))
        else:
            pages = [src[i] for i in parse_pages(which, len(src))]
            self.q.put(("log", f"Working on {len(pages)} of {len(src)} page picture(s) in {src[0].parent}"))
        return engine, pages

    def _review(self, ask):
        """Show the words the last run left as pictures, for typing in; then offer to run again."""
        if self._busy:
            return
        review, path = self._last_review or ([], Path(self.out_var.get().strip() or ".") / ANSWERS_FILE)
        self._overwrite_ok = True
        offer_review(self.winfo_toplevel(), review, path, self.run, ask=ask)
        self._overwrite_ok = False

    def run(self):
        got = None if self._busy else self._inputs()
        if not got:
            return
        src, out, dpi, jobs, which = got
        name = src.stem if isinstance(src, Path) else src[0].parent.name
        if which.strip().lower() not in ("", "all", "*"):
            name += "_pages_" + "".join(ch if ch.isalnum() or ch == "-" else "_" for ch in which.strip())
        want_pdf, want_docx, retype = self.want_pdf.get(), self.want_docx.get(), self.retype.get()
        layout, mark = ("flow", "free", "exact", "structured")[max(0, self.layout_box.current())], self.mark.get()
        word_pics, mark_pdf = bool(self.word_pics.get()), bool(self.mark_pdf.get())
        strict = ("strict", "balanced", "all")[max(0, self.strict_box.current())]
        use_dict = bool(self.dict_var.get())
        set_fonts(FONT_CHOICES[max(0, self.fonts_box.current())])
        want_html = bool(self.want_html.get())
        if not (want_pdf or want_docx or want_html):
            messagebox.showwarning(APP, "Tick New PDF, Word file or Web page.")
            return
        pdf = out / (name + "_rebuilt.pdf") if want_pdf else None
        docx = out / (name + "_rebuilt.docx") if want_docx else None
        web = out / (name + "_rebuilt.html") if want_html else None
        self._report, self._report_to, self._report_t0 = [], out, time.time()
        self._report_settings = [f"Source: {src if isinstance(src, Path) else str(src[0].parent) + ' (' + str(len(src)) + ' pictures)'}",
                                 f"Output folder: {out}", f"Pages: {which or 'all'}",
                                 f"Making: {', '.join(n for n, on in (('PDF', want_pdf), ('Word file', want_docx), ('web page', want_html)) if on)}",
                                 f"Re-typeset: {retype}; text replacement: {strict}; Word layout: {layout}; dictionary: {use_dict}; "
                                 f"fonts: {FONT_CHOICES[max(0, self.fonts_box.current())]}",
                                 f"Unidentified words: highlight in Word {mark}, highlight in PDF {mark_pdf}, word pictures {word_pics}"]
        clash = [p.name for p in (pdf, docx, web) if p is not None and p.exists()]
        if clash and not getattr(self, "_overwrite_ok", False) and not messagebox.askyesno(APP, f"{' and '.join(clash)} in\n{out}\nwill be overwritten. Continue?"):
            return
        self._set_busy(True)

        def work():
            try:
                out.mkdir(parents=True, exist_ok=True)
                engine, pages = self._pages(src, out, dpi, which)
                if not pages:
                    raise RuntimeError("There are no pages to work on.")
                self.q.put(("log", f"Recognising text with {engine} and matching fonts..."))
                for line in graphics_card_lines():
                    self.q.put(("log", line))
                self.q.put(("progress", 0, len(pages)))
                st = build_documents(pages, pdf_path=pdf, docx_path=docx, html_path=web, retypeset=retype, jobs=jobs,
                                     docx_layout=layout, highlight=mark, strictness=strict, use_dictionary=use_dict,
                                     word_pictures=word_pics, highlight_pdf=mark_pdf,
                                     answers=out / ANSWERS_FILE,
                                     progress=lambda d, t, name: (self.q.put(("progress", d, t)),
                                                                  self.q.put(("log", f"  reading the text, page {d} of {t}" if name.startswith("reading text") else f"  page {d} of {t}"))))
                if retype or docx is not None or web is not None:
                    self.q.put(("log", f"{st['replaced']:,} of {st['words']:,} words passed the checks and were "
                                       "re-typeset as real text."))
                    if docx is not None and layout != "exact":
                        self.q.put(("log", f"  Word file: {st['confirmed']:,} of {st['words']:,} words confirmed; the rest "
                                           "is included as the OCR read it" +
                                           (", highlighted in yellow - proof-read those." if mark else " - proof-read it.")))
                    else:
                        self.q.put(("log", "  The rest stay as part of the page picture."))
                for line in graphics_card_lines(st):
                    self.q.put(("log", line))
                if st.get("enlarged"):
                    self.q.put(("log", f"  {st['enlarged']} page(s) with small type were enlarged before reading and measuring "
                                       "(the pages keep their size; small type cannot be measured well enough otherwise)."))
                for line in structure_lines(st):
                    self.q.put(("log", line))
                if st.get("word_pictured"):
                    self.q.put(("log", f"  Word file: {st['word_pictured']} page(s) could not be set as text without running over "
                                       "the page, and were put in as a picture of the page instead."))
                if st.get("fonts"):
                    self.q.put(("log", f"  Fonts: {st['fonts']}."))
                if st.get("why"):
                    self.q.put(("log", "  Left as pictures, and why: " + ", ".join(
                        f"{k} {r}" for r, k in sorted(st["why"].items(), key=lambda x: -x[1])) + "."))
                if st.get("terms"):
                    shown = ", ".join(st["terms"][:30]) + (" ..." if len(st["terms"]) > 30 else "")
                    self.q.put(("log", f"  Learned from the document itself: {len(st['terms'])} term(s) - {shown}."))
                if st.get("dictionary"):
                    self.q.put(("log", f"  Dictionary: {st['dictionary']:,} words; {st['repaired']} reading(s) corrected with it."))
                elif use_dict:
                    self.q.put(("log", "  No word list is installed, so the dictionary was not used."))
                if st.get("failed"):
                    self.q.put(("log", f"{st['failed']} page(s) could not be re-typeset and were kept as pictures."))
                if st.get("parallel_failed"):
                    self.q.put(("log", "Note: working on several pages at once failed part-way (often low memory), so "
                                       "the rest were done one at a time. A lower 'CPU cores' setting avoids this."))
                if st.get("answers"):
                    self.q.put(("log", f"  Used {st['answers']} word(s) you typed in ({ANSWERS_FILE} in the output folder)."))
                for p in (pdf, docx, web):
                    if p is not None:
                        self.q.put(("log", f"Saved {p}"))
                if web is not None:
                    self.q.put(("log", "  Web page: open it in Chrome or Edge. E edits text in place, G moves and resizes anything, "
                                       "O shows the original page behind, Ctrl+S saves your changes, Ctrl+P prints at the real page size."))
                self._last_review = (st.get("review") or [], out / ANSWERS_FILE)
                self.q.put(("done", (lambda: self._review(True)) if st.get("review") else None))
            except ValueError as e:                     # a page list that does not fit: just say so
                self.q.put(("error", str(e)))
            except Exception as e:
                log_error("rebuild tab")
                self.q.put(("error", friendly(e)))

        threading.Thread(target=work, daemon=True).start()

    def to_watermark(self):
        """Save the pages as pictures and hand them to the watermark tab."""
        got = None if self._busy else self._inputs()
        if not got:
            return
        src, out, dpi, _, which = got
        self._set_busy(True)

        def work():
            try:
                _, pages = self._pages(src, out, dpi, which)
                folder = pages[0].parent if pages else None
                self.q.put(("done", (lambda: self.on_send(folder)) if folder and self.on_send else None))
            except ValueError as e:
                self.q.put(("error", str(e)))
            except Exception as e:
                log_error("rebuild tab")
                self.q.put(("error", friendly(e)))

        threading.Thread(target=work, daemon=True).start()


# ---- help: what every tab and every option does ----------------------------------------------------------
#
# Each topic: (title, text). In the text a line starting "# " is a sub-heading, "- " a bullet point,
# "> " a line set apart (a name on the screen, a file name); a blank line ends a paragraph.

HELP = [
    ("Start here", """
SnapClean turns pages you can only look at - screen snapshots, scans, a PDF whose pages are pictures - into a document you can search, copy from and edit. It has three tabs, and they are the three steps, in order:

- 1 Snapshot: take a picture of each page off the screen, turning the pages by itself.
- 2 Remove watermark: find what is printed on every page (a watermark, a stamp) and take it out.
- 3 Make PDF / Word / HTML: read the text and write a searchable PDF, a Word file and/or a web page.

You do not have to use all three. Pages you already have as pictures go straight to tab 2 or tab 3; a PDF goes straight to tab 3.

# Pictures the program takes
PNG, JPG / JPEG, TIFF, BMP, WebP and GIF. A TIFF that holds several pages is taken as that many pages. A photograph taken sideways is turned upright. PNG and TIFF are the ones to prefer: JPG blurs the edges of letters, and that costs accuracy. Cleaned pages are always saved as PNG.

# The usual way through
- Tab 1: choose the area of the screen, the key that turns the page, how many pages, and a folder. Press the hotkey (F9 unless you change it) to start.
- Press "Remove watermark from these snapshots >". Tab 2 opens on that folder. Press Analyze, look at what it found, then "Remove & Save".
- Tick what you want made (PDF, Word file, web page) - either on tab 2, so it is made as the pages are cleaned, or afterwards on tab 3 from the cleaned pages.
- When it has finished, go through the words it was not sure of ("Review words...") and run it once more so your answers are used.

# Try a few pages first
Reading the text takes time - roughly a few seconds a page. Both tab 2 and tab 3 have a Pages box: put 1-3 or 2, 5, 9 in it and look at the result before you run the whole document.

# The line at the bottom of the window
It shows which Python the program is running in and which text reader it will use. Setup > "How this program is running..." shows the full report.

# What the program cannot do
- It reads print. Handwriting, and text over a busy picture, will mostly stay as a picture.
- It is only as good as the pictures: letters about 16 pixels high or more read well; under 12 pixels a lot is lost. Zoom the document in before you snapshot it.
- It does not check itself against the original for you. Words it is unsure of are highlighted in yellow in the Word file - proof-read those.
"""),
    ("Tab 1 - Snapshot", """
Takes a picture of the same part of the screen again and again, pressing a key in between so that the next page comes up each time.

# Area to snapshot
- Drag a box on screen: when you start, the screen dims and you drag a rectangle round the page. Esc or a right-click cancels.
- Exact size: type a width and a height in pixels, then click once on the screen where its top-left corner goes. Use this when every run must be exactly the same size.
- Reuse the last area and skip selecting: the area you chose last time is used straight away, with no selecting.

# Repeat
- Key to press: the key sent after each snapshot to turn the page - Page Down, Right arrow, Space and so on.
- Wait after key (s): how long to wait, in seconds, after the key before the next snapshot, so the new page has time to appear. Make it longer if you get half-drawn pages or the same page twice.
- Take ... snapshots: stop after this many.
- Keep going until the area stops changing: stop by itself when the key no longer changes what is on the screen - the end of the document.
- Wait before first (s): a pause before the first snapshot, to give you time to click on the document's window.

# Before each snapshot (optional)
For viewers that need a nudge before each picture - a toolbar that must be hidden, a page that must be clicked.
- Click the mouse at: clicks at a spot of your choosing first. "Pick the spot..." lets you click it once on the screen; Button says which mouse button.
- Then press this key: presses a key after that. Choose one from the list or type its name, such as F2 or Ctrl+Shift+L.
- Then wait (s): a pause after the click and the key, before the snapshot.

# Files
- Save to folder: where the pictures go.
- Name prefix, Start #, Digits: how the files are named. Prefix snap, start 1, 3 digits gives snap_001, snap_002 ... The line underneath shows an example.
- Format: png or jpg. Use png for anything you will take through tabs 2 and 3 - jpg blurs the edges of letters.

# Starting and stopping
- Hotkey: the key that starts the run, from anywhere - the program does not need to be in front. Press it again to stop early. F9 unless you choose another.
- Minimize this window while snapping: gets the program's own window out of the picture.
- Stop: stops the run.
- Open folder: shows the folder the snapshots went to.
- Remove watermark from these snapshots >: opens tab 2 on that folder.

# Getting good snapshots
- Size matters more than anything else. After the first snapshot the log says how tall the letters are; if it advises you to zoom in, do - zoom the document until the body text is 16 pixels or more.
- Keep the mouse pointer and any pop-ups out of the area.
- Turn off anything that moves or fades in the viewer (animated page turns, toolbars that appear on their own), or use the click / key options to get rid of them.
"""),
    ("Tab 2 - Remove watermark", """
Works on a folder of page pictures (PNG, JPG, TIFF, BMP, WebP, GIF). It compares the pages, finds whatever is in the same place on all of them - a watermark, a logo, a stamp - and takes it out, putting back the text that was underneath where it can.

It needs several pages to learn from: what makes a watermark a watermark is that it is on every page. A handful will do; more is better.

# The top row
- Pages folder / Browse...: the folder of page pictures.
- Analyze: studies the pages. Do this first; nothing is changed yet.
- Save cleaned to / Browse...: where the cleaned pages go. Unless you change it, a folder beside the original with _cleaned added to its name. Your originals are never altered.
- Remove & Save: cleans the pages and writes whatever else is ticked below.

# What else to save
These are the same options as on tab 3 - see "Tab 3 - Make PDF / Word / HTML" and "The Word layouts" for what each means.
- Also save one searchable PDF (OCR): one PDF of all the cleaned pages, with the text findable.
- Re-typeset text in the PDF (sharp at any zoom): draw the words again as real text instead of leaving them as part of the page picture.
- Also save a Word file (.docx), laid out as: a Word file, in the layout chosen in the list.
- Also save a web page (.html): a page for your browser in which everything can be edited and moved.
- Pages: all, or a few to try first - 1-3, or 2, 5, 9.
- Sharpen text: Off, or enlarge the cleaned pictures 2 or 3 times and sharpen them. This changes the saved PNG pages; it is for pages you will read as pictures.
- Text replacement, Use the dictionary, Unidentified words, Fonts: as on tab 3.
- CPU cores: how many pages to work on at once.

# Page size
If the folder holds pages of more than one size, each size is studied on its own; this list switches between them.

# Static elements found
The list of things found on every page. Click a row to switch it between removing and keeping.
- Remove: whether it will be taken out.
- Type: what the program takes it for - watermark (something see-through lying over the page), solid (something that hides what is under it, such as a logo or a border), or mixed.
- Opacity: how strongly it covers what is under it. A ? after the number means it could not be measured from text crossing the watermark and is an estimate.
- Pixels: how big it is.
- Watermarks only: ticks the watermarks and nothing else - the usual choice.
- None: unticks everything. (You can still press Remove & Save, to make a PDF or Word file from pages that have no watermark.)

# Options
- Fit watermark opacity automatically: the program works out how see-through the watermark is from the text that crosses it. Untick it to set the strength yourself with the slider, when the automatic value leaves a ghost of the watermark (too low) or eats into the text (too high).
- Noise tolerance: differences smaller than this are ignored. Raise it if specks are being taken for part of the watermark; lower it if a faint watermark is being missed.

# Keep-out boxes
- Draw a keep-out box on the page: tick it, then drag a box on the preview over anything that must not be touched - a figure the watermark runs across, say. Nothing inside a box is changed.
- Undo removes the last box, Clear removes them all.

# The preview
Three views of the page, chosen above it:
- Detection: everything found, boxed and numbered - green will be removed, orange kept. Clicking a box switches it, the same as clicking its row in the list.
- Original: the page as it is.
- Cleaned: the page as it will be saved. Flip between Original and Cleaned to check a page.
< and > (or the Left and Right arrow keys) turn the pages, and the list jumps to one. -, +, Fit and 100% set the zoom. The mouse wheel scrolls (with Shift, sideways; with Ctrl, it zooms), and dragging moves the page about.

# Afterwards
- Open output folder: shows the results.
- Review words...: go through the words that were left as pictures - see "Reviewing words".
"""),
    ("Tab 3 - Make PDF / Word / HTML", """
For a PDF whose pages are pictures, or for page pictures you already have. Each page is read as a picture; text that can be matched to a font on this computer is drawn again as real text in the same place, and everything else - figures, table lines, text that could not be matched - stays as it looks now.

# Files
- PDF... : choose a PDF.
- Pictures... : choose picture files (PNG, JPG, TIFF, BMP, WebP, GIF) - a few, or all the pages in a folder.
- Save results to: the folder for the results. Unless you change it, one beside the original with _rebuilt added to the name; the files in it are named the same way (name_rebuilt.pdf, .docx, .html).
- Pages: all, or a few to try first - 1-3, or 2, 5, 9.

# What to make
- New PDF: a PDF that looks like the original, with text you can search and copy.
- Re-typeset its text: draws each confirmed word again as real type, so it is sharp however far you zoom in. Unticked, the pages stay as pictures and the text is only laid invisibly behind them, for searching.
- Word file (.docx): a Word document. The list beside it chooses the layout - see "The Word layouts".
- Word file: highlight text the checks could not confirm: marks in yellow the words the program is not sure of, so you know what to proof-read.
- Web page (.html): one file that opens in your browser, in which every paragraph, picture and table is a box you can edit, move and resize - see "The web page".

# Text replacement
How sure the program must be before it replaces the picture of a word with real text.
- Strict - only confirmed words: a word is replaced only when the readings agree and it passes the checks (a dictionary word, a plain number, and so on). Fewest mistakes; more words stay as pictures. The one to use for anything that matters.
- Balanced - more words, rare errors possible: also takes words that are very probably right.
- Everything the OCR read - errors likely: replaces all of it. For a rough draft.
- Use the dictionary: counts a word as confirmed when it is a known word. The dictionary is English with engineering terms, plus your own words in snapclean_words.txt beside the program (one word a line; "Review words..." can add to it for you).

# Fonts
- Automatic: the program decides which of the two below suits the document.
- One font throughout: for a document whose typeface is not on this computer. One substitute is used everywhere, with bold and italic where the original has them, so the result is even.
- Match line by line: each line is set in whichever ordinary font on this computer fits it best.
Setup > "Get free look-alike fonts" fetches Libre Baskerville, a free typeface close to many book faces.

# Unidentified words
What happens to words that were not confirmed.
- Word file: put in the word's own picture instead of a guess: the word appears as a small picture cut from the page - exactly as printed, but not text you can search or edit. Unticked, the program's best reading is typed in (and highlighted, if highlighting is on).
- PDF: highlight them: marks them in the PDF as well.

# Reading
- Read pages at (for a PDF): the resolution its pages are turned into pictures at. Automatic chooses between 150 and 300 dpi; 300 is best and slowest.
- CPU cores: how many pages to work on at once. More is faster and uses more memory.

# The buttons
- Rebuild: do it.
- Remove a watermark from it first >: sends the pages to tab 2.
- Open folder: shows the results.
- Review words...: go through the words left as pictures - see "Reviewing words".

# What is written to the folder
- The files you ticked.
- snapclean_run_report.txt: what was done, how many words were confirmed, whether a graphics card was used. Worth sending along if you ask for help.
- snapclean_answers.json: the words you typed in when reviewing, kept for the next run of this document.
"""),
    ("The Word layouts", """
There are four ways to lay out the Word file. The first three copy the pages; the fourth does not.

# Paragraphs and tables - lines as in the original
An ordinary Word document - paragraphs, real tables, pictures - laid out to follow the original: same page size, each block where it was, and every line ending at the word it ended on. It looks most like the original page for page. Editing is possible but stiff, because the line ends are fixed.

# Paragraphs and tables - free-flowing text
The same, but the words run on within each paragraph and Word breaks the lines. It still follows the pages closely, and is easier to edit. Line ends may differ a little from the original.

# Exact page copy (text boxes)
Each page is its own picture with the confirmed words set over it in text boxes. It is an exact copy of how the page looks; the text can be searched and copied, but it is not a document you would want to edit.

# Structured document - headings, lists, flowing text
The content as a document rather than a copy of its pages:
- titles become real Heading styles, so Word's Navigation pane (View > Navigation Pane) shows an outline and a table of contents can be made;
- columns are read in order and written as one column;
- paragraphs cut by the end of a column or a page are joined again, and words divided at a line end are made whole;
- running heads and page numbers are taken out of the text, and the footer gets a page number of its own;
- list items get a hanging indent; captions, tables and pictures keep their place in the reading order;
- small print is set at a readable size.
It does not match the original page for page - that is the point of it. Choose it when you want to reuse or rework the text. Read it through: what counts as a heading is judged from size and weight, and now and then a paragraph is joined to the next by mistake.

# In all of them
- Centred and right-aligned text is set that way in Word, and justified text is justified.
- A page that will not fit as text (a full-page form or drawing) is put in as a picture of itself.
- Figures, formulas, and tables without ruled lines are pictures.
"""),
    ("The web page", """
One .html file that opens in any browser, with nothing else needed. Every paragraph, picture and table is a box. It is cleaned up the same way as the re-typeset PDF: confirmed words are real text, the rest is marked.

# The two modes
- Edit text (E): click in any text and type.
- Move / resize (G): drag a box to move it, drag its corner to resize it. Click a box to select it, Shift+click or drag a band round several to take them together. The arrow keys nudge. Guide lines appear when edges line up.

# Font, size, bold and italic
These are in the bar in both modes, and they show what the text you are on is set in.
- What they change: in Edit text, the words you have selected - or, when no words are selected, the whole box you are in. In Move / resize, every box you have selected.
- Font: the list. The fonts the document is already set in come first.
- Size: the number box, in points. Type a size and press Enter. A- and A+ step it down and up.
- B, I, U: bold, italic, underline - on, or off again. Ctrl+B, Ctrl+I and Ctrl+U do the same. The buttons light up when the text you are on has them.
- T: plain - takes bold, italic and underline off.
- Colour, and left / centre / right / justified.
A box whose size or font you change is switched to flowing text, since its printed line ends no longer fit. Ctrl+Z in Move / resize takes a change back.

# In Move / resize
- duplicate (Ctrl+D), delete (Del), put back (Backspace) - puts a box back where it was.
- The four arrows bring a box forward or send it back when boxes overlap.

# Text that re-wraps
- Flow: lets the text of the chosen box run on and re-wrap, instead of keeping the printed line ends. Do this before you rewrite a paragraph.
- Flow all: the same for every box.

# Adding things
- + text: click it, then click on a page, for a new text box.
- + note: a note to yourself. Notes are never printed.
- + picture: a picture from a file.

# The rest of the bar
- Undo (Ctrl+Z).
- Original (O): shows the original page faintly behind, to compare against.
- Marks: shows or hides the yellow marks on words the program was not sure of.
- Notes: shows or hides your notes.
- Find (Ctrl+F): find and replace in all the text.
- Print / PDF (Ctrl+P): prints at the real page size; choose "Save as PDF" there for a PDF.
- W Word: saves the text and pictures as a file Word opens (.doc) - flowing text in reading order, not the exact layout.
- Save (Ctrl+S): saves the page with your changes.

Your changes are in the page only once you press Save.
"""),
    ("Reviewing words", """
Words the program could not confirm are left as pictures (or typed in and highlighted). Reviewing is how you settle them: you see each one as printed and say what it is.

After a run that left words over, the program asks whether you want to go through them. You can also do it later with "Review words..." on tab 2 or tab 3.

# New words first
If some of the leftovers look like real words or abbreviations the dictionary simply does not have, you get a list of those first. Tick the ones that are right; they are added to snapclean_words.txt and are known from then on, in every document.

# Then the rest
For the others you type what each word says. You are asked which way you want to do it:

- A list (fastest): each row shows the word as it is on the page (in a red box) with the program's guess beside it. Leave the right ones, correct the wrong ones; Enter moves down. "Accept this screen and go on" (Ctrl+Enter) takes every row as shown, "Skip this screen" leaves those words as pictures, "< Back" goes back, "Finish" stops.
- One at a time: each word is shown in its place on the page, with a preview of the page as it will be redrawn (green box). Enter uses what you typed, Esc skips the word and leaves it a picture, "< Back" goes back, "Finish" stops.

Type exactly what the boxed word says, with its punctuation - one word, no spaces. The most frequent readings come first, so a few minutes settles most of them, and you can stop whenever you like; what you have done is kept.

# Afterwards
Your answers are saved in snapclean_answers.json in the output folder. Run the document again and they are used: those words become real text. The same reading is answered everywhere it occurs.
"""),
    ("The Setup menu and settings", """
# How this program is running...
Shows which Python is running the program, which text reader was found, whether a graphics card is being used, and what was set up. The same report is saved as snapclean_setup_report.txt beside the program each time it starts.

# Settings...
These take effect the next time the program starts.
- Text reader: Automatic uses RapidOCR and Tesseract together when both are there - each word is read several times and the readings vote, which is what makes Strict replacement dependable. Or use one alone.
- Graphics card: use it when there is one, or never. Reading is several times faster on a card.
- Which graphics card: for a computer with two (a laptop with built-in graphics and a separate card). Automatic tries the high-performance one first.
- Reading models: larger, more accurate models when a graphics card is there, or the standard ones always.
- Extra readings: a second reading of every page and a second look at doubtful words. On with a graphics card; can be forced on (slow without a card) or off.
- Small type: pages with small letters are enlarged before reading (the saved pages keep their size). Automatic, never, or always 2 or 3 times.
- Python: whether the program may restart itself in a second Python when the one it was started with cannot run the better text reader.

# Put a shortcut on the desktop
Makes an icon that starts the program.

# Get free look-alike fonts (Libre Baskerville)...
Fetches a free typeface close to many book faces and keeps it in a snapclean_fonts folder beside the program, for the re-typeset text. Needs the internet once.

# Set up the text reader and graphics card again
Forgets what was found and looks again. Use it after installing a new graphics driver, or when setup went wrong the first time.

# Test the graphics card...
Tries each graphics card on its own - first the underlying engine, then the text reader - and shows what happens, with the reason for anything that fails. The result is saved as snapclean_gpu_test.txt beside the program. Use it when the log says a card was detected but the reader could not start on it.

# Which Python
- Python 3.12 or 3.13 is what the program is made for and tested on. Get it from python.org.
- A newer Python (3.14 and later) also works on Windows: the better text reader has no version for it yet, so the first time it starts the program installs Python 3.13 beside yours and restarts itself in that. Nothing of yours is changed.
- Python older than 3.10 is refused with a message.
- The line at the bottom of the window, and Setup > "How this program is running...", say which Python is in use.

# What the program installs by itself
The first time it starts it fetches what it needs: the Python packages it uses, the Tesseract text reader, and - if the Python it was started with is too new for the RapidOCR reader - a second Python to run in. This happens once and can take a few minutes.
"""),
    ("Getting the best result", """
- Make the letters big. Zoom the document in before taking snapshots, so body text is 16 pixels high or more. Nothing else makes as much difference.
- Use PNG, not JPG.
- Try three pages before you run three hundred.
- Keep Text replacement on Strict, then use "Review words..." and run again. That is quicker than proof-reading a Balanced run.
- Add the document's own terms to the dictionary when the review offers them. The second run confirms many more words.
- If the type in the result looks wrong, try the other Fonts choice, or fetch the look-alike fonts from the Setup menu.
- For a document you want to rework, make the Structured Word document; for one you want to look the same, the first layout or the PDF.
- Proof-read anything that matters. The yellow highlights show where to look first, but a confirmed word can still, rarely, be wrong - most often a figure: 1 for l, 0 for O.
"""),
    ("When something goes wrong", """
# It is very slow
- Look at the bottom line of the window or the log: is a graphics card in use? If not, see below.
- Lower "Read pages at", or run fewer pages at a time.
- Settings > Extra readings > Off.

# The graphics card is not used
- Setup > "How this program is running..." says what was found and why.
- On a laptop with two cards, choose the card yourself in Settings > Which graphics card.
- Update the graphics driver, then Setup > "Set up the text reader and graphics card again".
- When the log says the card was detected but the reader could NOT start on it, the lines under it say why, card by card. Setup > "Test the graphics card..." goes further and saves a report.
- If the card keeps failing the program steps down by itself and finishes on the processor; the log says so.

# Many words are left as pictures
- The letters are too small - zoom in and take the snapshots again.
- A watermark still crosses the text - clean the pages on tab 2 first.
- The document is full of terms the dictionary does not know - review, approve them, and run again.

# The watermark is not found, or text is damaged
- Use more pages for Analyze.
- Change Noise tolerance; set the opacity by hand; draw keep-out boxes over what must not be touched.

# The Word file does not match the page
- Try "free-flowing text", or the Exact page copy.
- Pages that could not be set as text are put in as pictures; the log says how many.

# Asking for help
Send snapclean_run_report.txt from the output folder and snapclean_setup_report.txt from the program's folder. Between them they say what the program did and what it was running on.
"""),
    ("From the command line", """
The program can also be run without its window:

> python snapclean.py analyze FOLDER
> python snapclean.py run FOLDER OUTPUT [--pdf FILE.pdf] [--retypeset] ...
> python snapclean.py pdf ...
> python snapclean.py rebuild FILE.pdf OUTPUT [--docx] [--html] [--pages 1-3] ...
> python snapclean.py selftest

Add --help after any of them for its options, for example:

> python snapclean.py run --help

Among them: --retypeset, --structured-docx, --exact-docx, --no-highlight, --no-dictionary, --strictness strict|balanced|all, --jobs N.
"""),
]


ABOUT_SITE = "www.nerxpower.com"
ABOUT_MAIL = "douglas.millner@nerxpower.com"
ABOUT = [
    "This was created by Doug Millner of NERX Power Consultants LLC.",
    "Power engineering and training services offered.",
    "It was made with the goal of breathing new life into old documents, putting them into a ready PDF / HTML / DOCX format.",
    "In addition, it can flip through online documents, take an image of each page, and use those images to "
    "recreate a clean-looking PDF / HTML / DOCX file.",
]
HELP.append(("About", "\n\n".join([ABOUT[0], "> " + ABOUT_SITE, "> " + ABOUT_MAIL] + ABOUT[1:])))


class AboutWindow(tk.Toplevel if tk else object):
    def __init__(self, master):
        super().__init__(master)
        self.title(f"About {APP}")
        self.resizable(False, False)
        self.transient(master)
        f = ttk.Frame(self, padding=(26, 20, 26, 16))
        f.pack(fill="both", expand=True)
        ttk.Label(f, text=APP, font=("Segoe UI", 20, "bold")).pack(anchor="w")
        ttk.Label(f, text=f"Version {VERSION}", foreground="#555").pack(anchor="w", pady=(0, 12))
        ttk.Label(f, text=ABOUT[0], wraplength=470, justify="left", font=("Segoe UI", 10, "bold")).pack(anchor="w")
        for text, target in ((ABOUT_SITE, "https://" + ABOUT_SITE), (ABOUT_MAIL, "mailto:" + ABOUT_MAIL)):
            link = tk.Label(f, text=text, fg="#0b57d0", cursor="hand2", font=("Segoe UI", 10, "underline"))
            link.pack(anchor="w", pady=(2, 0))
            link.bind("<Button-1>", lambda e, target=target: self._open(target))
        for i, line in enumerate(ABOUT[1:]):
            ttk.Label(f, text=line, wraplength=470, justify="left").pack(anchor="w", pady=(12 if i == 0 else 8, 0))
        ttk.Button(f, text="Close", command=self.destroy).pack(anchor="e", pady=(18, 0))
        self.bind("<Escape>", lambda e: self.destroy())
        self.bind("<Return>", lambda e: self.destroy())
        self.update_idletasks()
        try:
            x = master.winfo_rootx() + (master.winfo_width() - self.winfo_width()) // 2
            y = master.winfo_rooty() + (master.winfo_height() - self.winfo_height()) // 3
            self.geometry(f"+{max(0, x)}+{max(0, y)}")
        except Exception:
            pass

    @staticmethod
    def _open(target):
        import webbrowser
        webbrowser.open(target)


def _help_html():
    """The help as one web page (for printing, or reading beside the program)."""
    import html as _h
    out = ['<!doctype html><html><head><meta charset="utf-8"><title>' + APP + ' - help</title><style>'
           'body{font:15px/1.5 Segoe UI,Arial,sans-serif;max-width:820px;margin:28px auto;padding:0 18px;color:#222}'
           'h1{font-size:26px}h2{font-size:21px;margin-top:38px;border-bottom:1px solid #ccc;padding-bottom:4px}'
           'h3{font-size:16px;margin:22px 0 4px}li{margin:3px 0}pre{background:#f3f3f3;padding:6px 10px;margin:4px 0}'
           'nav a{display:block;margin:2px 0}@media print{nav{display:none}}</style></head><body>',
           f'<h1>{APP} {VERSION} - help</h1><nav>'
           + "".join(f'<a href="#t{i}">{_h.escape(t)}</a>' for i, (t, _) in enumerate(HELP)) + '</nav>']
    for i, (title, text) in enumerate(HELP):
        out.append(f'<h2 id="t{i}">{_h.escape(title)}</h2>')
        in_list = False
        for line in text.strip().split("\n"):
            line = line.strip()
            if in_list and not line.startswith("- "):
                out.append("</ul>")
                in_list = False
            if line.startswith("# "):
                out.append(f"<h3>{_h.escape(line[2:])}</h3>")
            elif line.startswith("- "):
                if not in_list:
                    out.append("<ul>")
                    in_list = True
                out.append(f"<li>{_h.escape(line[2:])}</li>")
            elif line.startswith("> "):
                out.append(f"<pre>{_h.escape(line[2:])}</pre>")
            elif line:
                out.append(f"<p>{_h.escape(line)}</p>")
        if in_list:
            out.append("</ul>")
    out.append("</body></html>")
    return "\n".join(out)


class HelpWindow(tk.Toplevel if tk else object):
    """The help: topics down the left, the chosen one on the right, a box to search them all."""

    def __init__(self, master, topic=0):
        super().__init__(master)
        self.title(f"{APP} - help")
        self.geometry("1000x700")
        self.minsize(640, 400)
        left = ttk.Frame(self, padding=(8, 8, 4, 8))
        left.pack(side="left", fill="y")
        ttk.Label(left, text="Find").pack(anchor="w")
        self.find_var = tk.StringVar()
        entry = ttk.Entry(left, textvariable=self.find_var, width=26)
        entry.pack(fill="x", pady=(0, 6))
        entry.bind("<Return>", lambda e: self._find())
        self.topics = tk.Listbox(left, exportselection=False, activestyle="none", width=30, height=len(HELP) + 1,
                                 font=("Segoe UI", 10))
        for title, _ in HELP:
            self.topics.insert("end", "  " + title)
        self.topics.pack(fill="y", expand=True)
        self.topics.bind("<<ListboxSelect>>", lambda e: self._show(self.topics.curselection()[0]) if self.topics.curselection() else None)
        ttk.Button(left, text="Open as a web page (to print)", command=self._web).pack(fill="x", pady=(8, 0))
        ttk.Button(left, text="Close", command=self.destroy).pack(fill="x", pady=(4, 0))
        right = ttk.Frame(self, padding=(4, 8, 8, 8))
        right.pack(side="left", fill="both", expand=True)
        self.text = tk.Text(right, wrap="word", font=("Segoe UI", 10), padx=18, pady=12, relief="flat", bg="white",
                            spacing1=2, spacing3=4, cursor="arrow")
        bar = ttk.Scrollbar(right, orient="vertical", command=self.text.yview)
        self.text.configure(yscrollcommand=bar.set)
        bar.pack(side="right", fill="y")
        self.text.pack(side="left", fill="both", expand=True)
        t = self.text
        t.tag_configure("h1", font=("Segoe UI", 17, "bold"), spacing3=10)
        t.tag_configure("h2", font=("Segoe UI", 11, "bold"), spacing1=14, spacing3=3, foreground="#134a8e")
        t.tag_configure("li", lmargin1=18, lmargin2=34)
        t.tag_configure("name", font=("Segoe UI", 10, "bold"))
        t.tag_configure("code", font=("Consolas", 10), background="#f1f1f1", lmargin1=18, lmargin2=18)
        t.tag_configure("hit", background="#ffe14d")
        self.bind("<Escape>", lambda e: self.destroy())
        self._show(topic)

    def _show(self, n, mark=None):
        n = max(0, min(len(HELP) - 1, int(n)))
        self.topics.selection_clear(0, "end")
        self.topics.selection_set(n)
        self.topics.see(n)
        title, body = HELP[n]
        t = self.text
        t.configure(state="normal")
        t.delete("1.0", "end")
        t.insert("end", title + "\n", "h1")
        for line in body.strip().split("\n"):
            line = line.strip()
            if line.startswith("# "):
                t.insert("end", line[2:] + "\n", "h2")
            elif line.startswith("- "):
                item = line[2:]
                cut = item.rfind(": ", 0, 64)            # "Name of the option: what it does"
                head, colon, rest = (item[:cut], ": ", item[cut + 2:]) if cut > 0 else (item, "", "")
                t.insert("end", "•  ", "li")
                if colon:
                    t.insert("end", head, ("li", "name"))
                    t.insert("end", ": " + rest + "\n", "li")
                else:
                    t.insert("end", item + "\n", "li")
            elif line.startswith("> "):
                t.insert("end", line[2:] + "\n", "code")
            elif line:
                t.insert("end", line + "\n")
            else:
                t.insert("end", "\n", ("gap",))
        t.tag_configure("gap", font=("Segoe UI", 3))
        if mark:
            start = "1.0"
            first = None
            while True:
                at = t.search(mark, start, "end", nocase=True)
                if not at:
                    break
                end = f"{at}+{len(mark)}c"
                t.tag_add("hit", at, end)
                first = first or at
                start = end
            if first:
                t.see(first)
        t.configure(state="disabled")

    def _find(self):
        """The next topic, after the one showing, that has the words in it."""
        what = self.find_var.get().strip()
        if not what:
            return
        now = self.topics.curselection()[0] if self.topics.curselection() else 0
        order = list(range(now + 1, len(HELP))) + list(range(0, now + 1))
        for n in order:
            if what.lower() in (HELP[n][0] + "\n" + HELP[n][1]).lower():
                self._show(n, mark=what)
                return
        messagebox.showinfo(APP, f"'{what}' is not in the help.", parent=self)

    def _web(self):
        try:
            path = HERE / "snapclean_help.html"
            path.write_text(_help_html(), encoding="utf-8")
        except OSError:
            import tempfile
            path = Path(tempfile.gettempdir()) / "snapclean_help.html"
            path.write_text(_help_html(), encoding="utf-8")
        import webbrowser
        webbrowser.open(path.as_uri())


# =============================================================================
# PART 5 - THE WINDOW
# =============================================================================

class MainApp(tk.Tk if tk else object):
    def __init__(self, folder=None):
        super().__init__()
        self.title(f"{APP} {VERSION}  -  Python {PYVER}")
        self.geometry("1280x900")
        self.minsize(980, 740)
        style = ttk.Style(self)
        if "vista" not in style.theme_names() and "clam" in style.theme_names():
            style.theme_use("clam")
        style.configure("Go.TButton", font=("TkDefaultFont", 10, "bold"))
        style.configure("TNotebook.Tab", padding=(16, 6), font=("TkDefaultFont", 10, "bold"))

        menu = tk.Menu(self)
        about = tk.Menu(menu, tearoff=0)
        about.add_command(label="How this program is running...", command=self._about)
        about.add_command(label="Settings...", command=self._settings)
        about.add_command(label="Put a shortcut on the desktop", command=self._shortcut)
        about.add_command(label="Get free look-alike fonts (Libre Baskerville)...", command=self._get_fonts)
        about.add_command(label="Set up the text reader and graphics card again", command=self._setup_again)
        about.add_command(label="Test the graphics card...", command=self._card_test)
        menu.add_cascade(label="Setup", menu=about)
        helper = tk.Menu(menu, tearoff=0)
        helper.add_command(label="How to use this program...", accelerator="F1", command=self._help)
        helper.add_separator()
        for n, (title, _) in enumerate(HELP):
            helper.add_command(label=title, command=lambda n=n: self._help(n))
        helper.add_separator()
        helper.add_command(label=f"About {APP}...", command=lambda: AboutWindow(self))
        menu.add_cascade(label="Help", menu=helper)
        self.bind("<F1>", lambda e: self._help(self._help_topic()))
        self.configure(menu=menu)
        # always in view: which Python this is and which text reader it will use
        self.running = ttk.Label(self, anchor="w", padding=(10, 3), relief="sunken", text=self._running_line())
        self.running.pack(side="bottom", fill="x")
        self.book = ttk.Notebook(self)
        self.book.pack(fill="both", expand=True, padx=6, pady=6)
        self.snap = SnapTab(self.book, on_send=self.send_to_clean)
        self.clean = CleanTab(self.book, folder)
        self.book.add(self.snap, text="  1   Snapshot  ")
        self.rebuild = RebuildTab(self.book, on_send=self.send_to_clean)
        self.book.add(self.clean, text="  2   Remove watermark  ")
        self.book.add(self.rebuild, text="  3   Make PDF / Word / HTML  ")
        if folder:
            self.book.select(self.clean)
        self.protocol("WM_DELETE_WINDOW", self._close)
        threading.Thread(target=self._save_report, daemon=True).start()

    def _save_report(self):
        try:
            text = self._report()
            (HERE / "snapclean_setup_report.txt").write_text(text, encoding="utf-8")
            card = "GRAPHICS CARD DETECTED" in text
            if "RapidOCR" in self._reader()[0]:
                note = "   |   Graphics card: " + ("detected" if card else "NOT detected")
                self.after(0, lambda: self.running.configure(text=self._running_line().replace(
                    "   |   Setup menu", note + "   |   Setup menu")))
        except Exception:
            pass

    def send_to_clean(self, folder):
        self.clean.in_var.set(str(folder))
        self.clean._default_output()
        self.book.select(self.clean)
        self.clean.analyze()

    @staticmethod
    def _reader():
        """Which text reader will be used, without loading it."""
        tess = _find_tesseract()
        if os.environ.get("DEWATERMARK_OCR") not in ("tesseract", "windows") and _have("rapidocr", "onnxruntime"):
            return "RapidOCR" + (" with Tesseract as a second opinion" if tess else " (Tesseract not found)"), True
        if tess:
            return "Tesseract only", False
        return ("Windows' built-in reader" if IS_WINDOWS else "none found"), False

    def _running_line(self):
        reader, _ = self._reader()
        how = "restarted in this Python by the setup" if os.environ.get("SNAPCLEAN_RESTARTED") else "started directly"
        return f"Running on Python {PYVER} ({how})   |   Text reader: {reader}   |   Setup menu has the details"

    def _report(self):
        return "\n".join(self._report_lines())

    def _card_test(self):
        """Try each graphics card on its own, show what happens and save it beside the program."""
        win = tk.Toplevel(self)
        win.title(f"{APP} - graphics card test")
        win.geometry("980x560")
        box = tk.Text(win, wrap="none", font=("Consolas", 9), padx=10, pady=8)
        bar = ttk.Scrollbar(win, orient="horizontal", command=box.xview)
        box.configure(xscrollcommand=bar.set)
        foot = ttk.Label(win, padding=(10, 6), text="Testing - this takes up to a minute...")
        foot.pack(side="bottom", fill="x")
        bar.pack(side="bottom", fill="x")
        box.pack(fill="both", expand=True)
        lines = queue.Queue()

        def work():
            try:
                text = graphics_card_test(lines.put)
            except Exception:
                text = "The test itself failed:\n" + traceback.format_exc()
                lines.put(text)
            lines.put(("done", text))

        def poll():
            try:
                while True:
                    item = lines.get_nowait()
                    if isinstance(item, tuple):
                        where = ""
                        try:
                            (HERE / "snapclean_gpu_test.txt").write_text(item[1] + "\n", encoding="utf-8")
                            where = f"  Saved as snapclean_gpu_test.txt in {HERE}"
                        except OSError:
                            pass
                        if win.winfo_exists():
                            foot.configure(text="Done." + where)
                        return
                    if win.winfo_exists():
                        box.insert("end", str(item) + "\n")
                        box.see("end")
            except queue.Empty:
                pass
            self.after(150, poll)

        threading.Thread(target=work, daemon=True).start()
        poll()

    def _help_topic(self):
        """The help topic for the tab that is showing."""
        try:
            return 1 + self.book.index(self.book.select())
        except Exception:
            return 0

    def _help(self, topic=0):
        win = getattr(self, "_help_win", None)
        if win is not None and win.winfo_exists():
            win._show(topic)
            win.lift()
            win.focus_set()
            return
        self._help_win = HelpWindow(self, topic)

    def _about(self):
        text = self._report()
        try:
            (HERE / "snapclean_setup_report.txt").write_text(text, encoding="utf-8")
            text += f"\n\n(Also saved as snapclean_setup_report.txt in {HERE})"
        except OSError:
            pass
        messagebox.showinfo(f"{APP} - how this program is running", text, parent=self)

    def _report_lines(self):
        state = _setup_state()
        reader, rapid = self._reader()
        lines = [f"{APP} {VERSION}", "",
                 f"Python:  {sys.version.split()[0]}",
                 f"    {_python_exe()}",
                 "    " + ("restarted here by the setup, from the Python it was started with"
                           if os.environ.get("SNAPCLEAN_RESTARTED") else "this is the Python the program was started with"),
                 "", f"Text reader:  {reader}"]
        cards = _video_cards()
        lines += ["", "Graphics card(s) in this computer:  " + ("; ".join(cards) if cards else "none reported")]
        if rapid:
            got = _card_support()
            names = {"DmlExecutionProvider": "DirectML (graphics card)", "CUDAExecutionProvider": "CUDA (NVIDIA graphics card)",
                     "CPUExecutionProvider": "processor"}
            lines.append("The text reader can run on:  " + (", ".join(names.get(p, p) for p in got["providers"]) or "unknown"))
            lines.append("    installed: " + (", ".join(got["packages"]) or "no onnxruntime package found"))
            if got["card"]:
                lines.append("    GRAPHICS CARD DETECTED - it will be used.")
            else:
                lines.append("    GRAPHICS CARD NOT DETECTED by the reader - it will run on the processor.")
                why = got["error"] or state.get("card_problem") or ""
                if os.environ.get("DEWATERMARK_GPU", "1") == "0":
                    why = "DEWATERMARK_GPU=0 is set."
                if why:
                    lines.append("    " + str(why).strip().replace("\n", "\n    ")[:600])
        else:
            lines.append("The text reader in use (Tesseract) cannot use a graphics card; RapidOCR can.")
        tess = _find_tesseract()
        lines.append(f"Tesseract:  {tess or 'not found'}")
        if not rapid:
            lines.append("")
            if state.get("other_python_failed"):
                lines += ["The better reader (RapidOCR) could not be set up in a second Python:",
                          "    " + str(state.get("other_python_problem", "")).strip().replace("\n", "\n    ")[:700]]
            elif os.environ.get("SNAPCLEAN_ONE_PYTHON") == "1":
                lines.append("SNAPCLEAN_ONE_PYTHON=1 is set, so the program stays in this Python.")
            elif state.get("rapid_failed") == PYVER:
                lines.append(f"RapidOCR has no build for Python {PYVER}.")
        if state.get("other_python"):
            lines += ["", f"Second Python set up for the better reader:\n    {state['other_python']}"]
        lines += ["", f"Setup notes are kept in {SETUP_FILE}"]
        return lines

    def _shortcut(self):
        """A desktop shortcut that starts this file with the Python it is running in now, without a console window."""
        exe = _python_exe()
        quiet = os.path.join(os.path.dirname(exe), "pythonw.exe")
        exe = quiet if os.path.exists(quiet) else exe
        me = os.path.abspath(__file__)
        try:
            if IS_WINDOWS:
                script = ("$d=[Environment]::GetFolderPath('Desktop');$s=(New-Object -ComObject WScript.Shell).CreateShortcut("
                          f"(Join-Path $d '{APP}.lnk'));$s.TargetPath='{exe}';$s.Arguments='\"{me}\"';"
                          f"$s.WorkingDirectory='{os.path.dirname(me)}';$s.Description='{APP}';$s.Save();Write-Output (Join-Path $d '{APP}.lnk')")
                ok, out = _run_quiet(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", script], 60)
                if not ok:
                    raise OSError(out.strip()[-300:] or "PowerShell could not make the shortcut")
                where = out.strip().splitlines()[-1] if out.strip() else "the desktop"
            else:
                desk = Path.home() / "Desktop"
                desk.mkdir(exist_ok=True)
                where = desk / f"{APP}.desktop"
                where.write_text(f"[Desktop Entry]\nType=Application\nName={APP}\nExec=\"{exe}\" \"{me}\"\nTerminal=false\n", encoding="utf-8")
                os.chmod(where, 0o755)
            messagebox.showinfo(APP, f"Shortcut made:\n{where}\n\nIt starts this file:\n{me}\n\nIf you replace the program with a newer "
                                     "version under another name, make the shortcut again from the new one.", parent=self)
        except Exception as e:
            messagebox.showerror(APP, f"The shortcut could not be made:\n{friendly(e)}", parent=self)

    def _get_fonts(self):
        """Fetch the free fonts the program can use as closer stand-ins (kept in a folder beside it)."""
        if not messagebox.askokcancel(APP, "This fetches Libre Baskerville (a free typeface, SIL Open Font License) from the Google Fonts "
                                           "collection on GitHub and keeps it in the folder\n\n" + str(fonts_folder()) + "\n\n"
                                           "The program then tries it like any other font when it matches a document, and uses it where "
                                           "it fits best. It is built into the PDF and the web page. For the Word file to show it, "
                                           "install the four .ttf files in that folder in Windows (select them, right-click, Install).",
                                      parent=self):
            return
        self.running.configure(text="Fetching fonts...")

        def work():
            try:
                made = get_free_fonts(lambda text: None)
                note = f"{len(made)} font file(s) are ready in {fonts_folder()}. They are used from the next run on."
            except Exception as e:
                log_error("fetching fonts")
                note = f"The fonts could not be fetched: {friendly(e)}"
            self.after(0, lambda: (self.running.configure(text=self._running_line()), messagebox.showinfo(APP, note, parent=self)))

        threading.Thread(target=work, daemon=True).start()

    def _settings(self):
        """The switches for the reader, the graphics card and small type, in one place (they are kept in the
        setup notes and take effect the next time the program starts)."""
        state = _setup_state()
        saved = state.get("settings") or {}
        win = tk.Toplevel(self)
        win.title(f"{APP} - settings")
        win.transient(self)
        win.resizable(False, False)
        boxes = {}
        ttk.Label(win, padding=(14, 12, 14, 4), text="These take effect the next time the program starts.").grid(row=0, column=0, columnspan=2, sticky="w")
        for row, (name, (var, choices, label)) in enumerate(SETTINGS.items(), start=1):
            ttk.Label(win, text=label + ":", padding=(14, 4, 6, 4)).grid(row=row, column=0, sticky="w")
            box = ttk.Combobox(win, state="readonly", width=62, values=list(choices))
            now = saved.get(name, "")
            box.current(max(0, list(choices.values()).index(now)) if now in choices.values() else 0)
            box.grid(row=row, column=1, sticky="w", padx=(0, 14), pady=3)
            if os.environ.get(var) and os.environ[var] != now:
                ttk.Label(win, foreground="#a00", text=f"(set outside the program: {var}={os.environ[var]} - that wins)").grid(
                    row=row, column=2, sticky="w", padx=(0, 14))
            boxes[name] = (box, choices)

        def keep():
            state2 = _setup_state()
            state2["settings"] = {name: list(choices.values())[max(0, box.current())] for name, (box, choices) in boxes.items()}
            for key in ("card_tried", "card_ok", "card_problem"):       # the card is looked for afresh
                state2.pop(key, None)
            try:
                SETUP_FILE.write_text(json.dumps(state2, indent=2), encoding="utf-8")
            except OSError as e:
                messagebox.showerror(APP, f"Could not save the settings in {SETUP_FILE}:\n{e}", parent=win)
                return
            win.destroy()
            messagebox.showinfo(APP, "Saved. Close the program and start it again for the settings to take effect.", parent=self)

        row = ttk.Frame(win, padding=(14, 10, 14, 12))
        row.grid(row=len(SETTINGS) + 1, column=0, columnspan=3, sticky="e")
        ttk.Button(row, text="Save", style="Go.TButton", command=keep).pack(side="right")
        ttk.Button(row, text="Cancel", command=win.destroy).pack(side="right", padx=8)
        self._settings_win = win

    def _setup_again(self):
        state = _setup_state()
        for key in ("other_python_failed", "other_python_problem", "other_python", "rapid_failed", "winget_tried",
                    "card_tried", "card_ok", "card_problem"):
            state.pop(key, None)
        try:
            SETUP_FILE.write_text(json.dumps(state, indent=2), encoding="utf-8")
        except OSError as e:
            messagebox.showerror(APP, f"Could not change {SETUP_FILE}:\n{e}", parent=self)
            return
        messagebox.showinfo(APP, "The setup will run again the next time the program starts.\n\n"
                                 "Close the program and start it again.", parent=self)

    def _close(self):
        self.snap.shutdown()
        self.destroy()


def main():
    if CLI_MODE:
        return cli_main()
    try:
        app = MainApp(sys.argv[1] if len(sys.argv) > 1 else None)
    except Exception:
        _fatal(f"{APP} - could not start", traceback.format_exc())

    def on_error(exc, val, tb):                 # errors after startup: report, keep the window open
        text = "".join(traceback.format_exception(exc, val, tb))
        print(text, file=sys.stderr)
        try:
            with open(LOG, "a", encoding="utf-8") as fh:
                fh.write(f"\n--- {time.strftime('%Y-%m-%d %H:%M:%S')}  {APP} {VERSION}  window\n{text}")
        except OSError:
            pass
        messagebox.showerror(APP, friendly(val) if isinstance(val, MemoryError) else text[-1500:])

    def thread_error(args):                     # a background thread died without handling its error
        text = "".join(traceback.format_exception(args.exc_type, args.exc_value, args.exc_traceback))
        try:
            with open(LOG, "a", encoding="utf-8") as fh:
                fh.write(f"\n--- {time.strftime('%Y-%m-%d %H:%M:%S')}  {APP} {VERSION}  background\n{text}")
        except OSError:
            pass
        print(text, file=sys.stderr)

    threading.excepthook = thread_error

    app.report_callback_exception = on_error
    app.mainloop()
    return 0


if __name__ == "__main__":
    sys.exit(main())
