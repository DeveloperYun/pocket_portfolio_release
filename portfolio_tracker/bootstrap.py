from __future__ import annotations

import os
import sys


def patch_noconsole_stdout_stderr() -> None:
    # PyInstaller --noconsole 환경에서 sys.stdout/stderr가 None일 수 있다.
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")


def patch_imagetk_photoimage_fallback() -> None:
    """
    PyInstaller(onefile) 환경에서 Pillow Tk 브릿지가 실패할 때
    Tk 기본 PhotoImage로 자동 fallback 시킨다.
    """
    try:
        import tkinter as tk
    except Exception:
        return

    try:
        from PIL import ImageTk  # type: ignore
    except Exception:
        ImageTk = None

    if ImageTk is None:
        return

    original_photoimage = getattr(ImageTk, "PhotoImage", None)
    if original_photoimage is None:
        return

    if getattr(original_photoimage, "_portfolio_safe_wrapper", False):
        return

    def safe_photoimage(*args, **kwargs):
        try:
            return original_photoimage(*args, **kwargs)
        except tk.TclError as err:
            if "PyImagingPhoto" in str(err):
                return tk.PhotoImage(*args, **kwargs)
            raise

    safe_photoimage._portfolio_safe_wrapper = True  # type: ignore[attr-defined]
    ImageTk.PhotoImage = safe_photoimage


def bootstrap_runtime_patches() -> None:
    patch_noconsole_stdout_stderr()
    patch_imagetk_photoimage_fallback()

