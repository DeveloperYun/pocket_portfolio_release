from __future__ import annotations

import datetime
import json
import math
import os
import signal
import sys
import traceback
import tkinter as tk
from collections import defaultdict
from tkinter import filedialog, messagebox, ttk
from typing import TYPE_CHECKING, List

import numpy as np
import pandas as pd
import requests
import yfinance as yf
from bs4 import BeautifulSoup

import matplotlib

from portfolio_tracker.version import __version__
from portfolio_tracker.realized_pnl import SellRecord, apply_sell_to_portfolio, summarize_realized_pnl
from portfolio_tracker.utils import (
    currency_formatter,
    current_os,
    date_with_weekday_kr as _date_with_weekday_kr,
    get_asset_category,
    get_history_file_path,
    resolve_portfolio_history_file_path,
    save_portfolio_history_file_path,
    get_realized_pnl_records_file_path,
    is_kr_business_day as _is_kr_business_day,
    is_korean_ticker,
    kr_holiday_date_set as _kr_holiday_date_set,
    count_kr_business_days_after_prev as _count_kr_bdays_after_prev,
    normalize_account_cash_entry as _normalize_account_cash_entry,
)


def _configure_matplotlib_for_tk() -> None:
    if current_os == "Linux":
        matplotlib.use("TkAgg")

    import matplotlib.dates as mdates
    import matplotlib.font_manager as fm
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    from matplotlib.ticker import FuncFormatter

    # publish to module globals (used by PortfolioApp methods)
    globals()["mdates"] = mdates
    globals()["fm"] = fm
    globals()["plt"] = plt
    globals()["FigureCanvasTkAgg"] = FigureCanvasTkAgg
    globals()["FuncFormatter"] = FuncFormatter

    plt.style.use("dark_background")

    # PyInstaller에서만 PIL Tk 브릿지 대신 tk.PhotoImage로 바꿈. 일반 Linux에서는
    # 네이티브 코드와 충돌해 세그폴트가 날 수 있어 frozen 빌드에 한정한다.
    if getattr(sys, "frozen", False):
        try:
            import matplotlib.backends._backend_tk as backend_tk

            backend_tk.ImageTk.PhotoImage = tk.PhotoImage
        except Exception:
            pass

    if current_os == "Windows":
        plt.rcParams["font.family"] = "Malgun Gothic"
    elif current_os == "Darwin":
        plt.rcParams["font.family"] = "AppleGothic"
    elif current_os == "Linux":
        font_path = "/usr/share/fonts/truetype/nanum/NanumGothic.ttf"
        if os.path.exists(font_path):
            try:
                fe = fm.FontEntry(fname=font_path, name="NanumGothic")
                fm.fontManager.ttflist.insert(0, fe)
                plt.rcParams["font.family"] = "NanumGothic"
            except Exception:
                pass

    plt.rcParams["font.size"] = 11
    plt.rcParams["axes.unicode_minus"] = False


if TYPE_CHECKING:
    import matplotlib.dates as mdates  # noqa: F401
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # noqa: F401
    from matplotlib.ticker import FuncFormatter  # noqa: F401


class PortfolioApp:
    def __init__(self, root):
        self.root = root
        self.root.title(f"실시간 포트폴리오 트래커 v{__version__} ({current_os} 모드)")
        self.root.geometry("580x860")

        self.BG = "#101317"
        self.FG = "#E6EDF3"
        self.BTN_BG = "#2B3440"
        self.ENTRY_BG = "#1B2430"
        self.CARD_BG = "#151C24"
        self.BORDER = "#273243"
        self.ACCENT = "#57A6FF"
        self.ACCENT_ALT = "#7EE787"
        self.MUTED = "#8B949E"
        self.FONT_TITLE = ("Helvetica" if current_os == "Linux" else "Malgun Gothic", 16, "bold")
        self.FONT_MAIN = ("Helvetica" if current_os == "Linux" else "Malgun Gothic", 11)
        self.FONT_CAPTION = (self.FONT_MAIN[0], 9)

        self.root.configure(bg=self.BG)
        self._setup_styles()

        self.portfolio = []
        # 계좌별 예수금: [{"account": str, "cash_krw": float, "cash_usd": float}, ...]
        self.account_cash = []
        # 실현손익(매도) 기록(누적 저장): [{"sell_date": "...", "account": "...", ...}, ...]
        self.sell_records = self._load_sell_records_from_disk()
        # 마지막으로 불러온/저장한 포트폴리오 JSON 경로(덮어쓰기 저장에 사용)
        self.portfolio_json_path: str | None = None

        self.current_alpha = 0.1
        self.chart_win = None
        self.chart_auto_refresh_job = None
        self.chart_auto_refresh_interval_ms = 30000
        self.current_chart_view_mode = "일간"
        self.daily_window_size = 20
        self.daily_window_start = 0
        self.daily_window_max_start = 0
        self.daily_window_follow_latest = True
        self.daily_window_scale = None
        self.daily_window_label = None
        self._updating_daily_window_scale = False
        self.report_text_widget = None
        self.current_report_data = []
        self.current_exchange_rate = 1400.0
        self.rebalance_enabled = tk.BooleanVar(value=False)
        self.target_ratios = {"주식": 20.0, "채권": 20.0, "금": 20.0, "원자재": 20.0, "현금성 자산": 20.0}

        # 일별 수익률/스냅샷 JSON — 사용자가 메인 화면 상단에서 경로 지정(설정에 저장)
        self.portfolio_history_path = resolve_portfolio_history_file_path()

        self.create_widgets()
        self.bind_escape_to_close(self.root)
        self.apply_transparency()
        # 일부 환경에서는 초기 맵핑 직후 alpha가 무시되어 한 번 더 적용이 필요하다.
        self.root.after(50, self.apply_transparency)
        self.root.after(200, self.apply_transparency)

    def _get_portfolio_name_by_account_ticker(self, account: str, ticker: str) -> str | None:
        """
        특정 계좌의 ticker에 대응하는 기존 종목명을 찾는다(없으면 None).
        ticker는 대소문자/공백을 정규화해 비교한다.
        """
        acc = str(account or "").strip() or "일반 계좌"
        t = str(ticker or "").strip()
        if not t:
            return None
        t_up = t.upper()
        for item in self.portfolio:
            try:
                item_acc = str(item.get("account", "")).strip() or "일반 계좌"
                if item_acc != acc:
                    continue
                item_ticker = str(item.get("ticker", "")).strip()
                if not item_ticker:
                    continue
                if item_ticker.upper() != t_up:
                    continue
                name = str(item.get("name", "")).strip()
                return name or None
            except Exception:
                continue
        return None

    def _parse_ticker_from_combo_value(self, raw: str) -> str:
        """
        종목코드/티커 콤보박스 값에서 ticker만 추출한다.
        표시 포맷: "TICKER | 종목명" (또는 사용자가 직접 입력한 ticker)
        """
        s = str(raw or "").strip()
        if not s:
            return ""
        if "|" in s:
            s = s.split("|", 1)[0].strip()
        return s

    def _find_portfolio_holding(self, account: str, ticker: str):
        """
        포트폴리오 리스트에서 (account, ticker) 매칭되는 holding(dict)과 인덱스를 반환.
        없으면 (None, None).
        """
        acc = str(account or "").strip() or "일반 계좌"
        t = str(ticker or "").strip().upper()
        if not t:
            return None, None
        for i, item in enumerate(self.portfolio or []):
            try:
                item_acc = str(item.get("account", "")).strip() or "일반 계좌"
                item_t = str(item.get("ticker", "")).strip().upper()
                if item_acc == acc and item_t == t:
                    return item, i
            except Exception:
                continue
        return None, None

    def _set_buy_ex_enabled(self, enabled: bool) -> None:
        """
        매입 환율 입력칸을 해외 종목에서만 활성화한다.
        """
        if not hasattr(self, "ent_buy_ex"):
            return
        try:
            self.ent_buy_ex.config(state=("normal" if enabled else "disabled"))
        except Exception:
            pass
        if hasattr(self, "lbl_buy_ex"):
            try:
                self.lbl_buy_ex.config(fg=(self.FG if enabled else self.MUTED))
            except Exception:
                pass

    def _sync_buy_ex_enabled_from_ticker(self) -> None:
        """
        현재 티커 값 기준으로 매입 환율 입력칸 활성/비활성 상태를 동기화한다.
        """
        try:
            ticker = self._parse_ticker_from_combo_value(str(self.ent_ticker.get()))
        except Exception:
            ticker = ""
        # 국내(6자리)면 환율 입력 불필요 → disable
        self._set_buy_ex_enabled(not is_korean_ticker(ticker))

    def _setup_styles(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure(
            "Modern.TCombobox",
            fieldbackground=self.ENTRY_BG,
            background=self.BTN_BG,
            foreground=self.FG,
            bordercolor=self.BORDER,
            arrowcolor=self.FG,
            insertcolor=self.FG,
            relief="flat",
            padding=6,
        )
        style.map(
            "Modern.TCombobox",
            fieldbackground=[("readonly", self.ENTRY_BG), ("disabled", "#2A313C")],
            foreground=[("disabled", self.MUTED)],
            arrowcolor=[("disabled", self.MUTED)],
        )

    def _build_card_frame(self, parent):
        frame = tk.Frame(
            parent,
            bg=self.CARD_BG,
            highlightbackground=self.BORDER,
            highlightthickness=1,
            bd=0,
            padx=14,
            pady=12,
        )
        return frame

    def _make_label(self, parent, text):
        return tk.Label(parent, text=text, bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN)

    def _make_entry(self, parent, width=None):
        kwargs = {
            "bg": self.ENTRY_BG,
            "fg": self.FG,
            "insertbackground": self.FG,
            "font": self.FONT_MAIN,
            "relief": "flat",
            "highlightthickness": 1,
            "highlightbackground": self.BORDER,
            "highlightcolor": self.ACCENT,
        }
        if width is not None:
            kwargs["width"] = width
        return tk.Entry(parent, **kwargs)

    def _make_button(self, parent, text, command, bg=None, fg=None, bold=False, pad=(8, 5)):
        font = (self.FONT_MAIN[0], 10, "bold" if bold else "normal")
        btn = tk.Button(
            parent,
            text=text,
            command=command,
            bg=bg or self.BTN_BG,
            fg=fg or self.FG,
            activebackground="#3B4656",
            activeforeground=self.FG,
            relief="flat",
            bd=0,
            cursor="hand2",
            padx=pad[0],
            pady=pad[1],
            font=font,
        )
        return btn

    def _setup_text_tags(self, txt, title_size=14, title_color=None, body_size=11):
        title_color = title_color or self.ACCENT
        txt.tag_config("title", font=(self.FONT_MAIN[0], title_size, "bold"), foreground=title_color)
        txt.tag_config("up", foreground="#FF6B6B", font=(self.FONT_MAIN[0], body_size, "bold"))
        txt.tag_config("down", foreground="#4D96FF", font=(self.FONT_MAIN[0], body_size, "bold"))
        txt.tag_config("flat", foreground=self.FG)
        # account popup 전용 태그(없는 곳에서 사용해도 무해)
        txt.tag_config("acc_title", font=(self.FONT_MAIN[0], 12, "bold"), foreground="#00FFFF")

    def _get_lowest_main_button_top(self):
        """
        메인 화면의 "아래 버튼 3개" 중 최하단 버튼의 top y좌표(스크린 기준)를 반환.
        """
        tops = []
        for attr in ("btn_main_calc", "btn_main_reset", "alpha_scale"):
            if hasattr(self, attr):
                try:
                    tops.append(getattr(self, attr).winfo_rooty())
                except Exception:
                    pass
        return max(tops) if tops else None

    def _resize_and_place_chart_win(self, win, desired_w=1100, desired_h=650, reserve_bottom=130):
        """
        차트 팝업이 열릴 때 메인 화면 아래 버튼 3개가 가려지지 않도록
        화면 여유분(아래 여백)을 남겨서 크기/위치를 조정한다.
        """
        try:
            self.root.update_idletasks()
            win.update_idletasks()

            sw = win.winfo_screenwidth()
            sh = win.winfo_screenheight()

            root_x = self.root.winfo_rootx()
            root_y = self.root.winfo_rooty()
            root_w = self.root.winfo_width()
            root_h = self.root.winfo_height()

            # 우선 메인 창 옆으로 배치해서 겹침 자체를 피한다.
            margin = 12
            usable_w = max(420, sw - 20)
            usable_h = max(320, sh - 20)
            w = min(desired_w, usable_w)
            h = min(desired_h, usable_h)

            right_x = root_x + root_w + margin
            left_x = root_x - w - margin
            top = max(10, min(root_y, sh - h - 10))

            if right_x + w <= sw - 10:
                # 메인 오른쪽에 충분한 공간
                left = right_x
                win.geometry(f"{w}x{h}+{left}+{top}")
            elif left_x >= 10:
                # 메인 왼쪽에 충분한 공간
                left = left_x
                win.geometry(f"{w}x{h}+{left}+{top}")
            else:
                # 좌우 공간이 모두 부족하면, 기존처럼 위쪽에 최대한 올려서 버튼 가림 최소화
                popup_top = root_y + 40
                lowest_btn_top = self._get_lowest_main_button_top()
                if lowest_btn_top is not None:
                    popup_max_bottom = lowest_btn_top - 6
                else:
                    popup_max_bottom = root_y + root_h - reserve_bottom
                available_h = popup_max_bottom - popup_top
                if available_h > 0:
                    h = min(h, available_h)
                left = max(10, min(root_x + 20, sw - w - 10))
                win.geometry(f"{w}x{h}+{left}+{popup_top}")

            win.update_idletasks()
        except Exception:
            # 최악의 경우, 기본 크기만 적용
            try:
                win.geometry(f"{desired_w}x{desired_h}")
            except Exception:
                pass

    def create_widgets(self):
        outer = tk.Frame(self.root, bg=self.BG)
        outer.pack(fill='both', expand=True)

        v_scroll = tk.Scrollbar(outer, orient='vertical')
        v_scroll.pack(side='right', fill='y')

        self.main_canvas = tk.Canvas(
            outer,
            bg=self.BG,
            highlightthickness=0,
            yscrollcommand=v_scroll.set
        )
        self.main_canvas.pack(side='left', fill='both', expand=True)
        v_scroll.config(command=self.main_canvas.yview)

        self.main_content = tk.Frame(self.main_canvas, bg=self.BG)
        self.main_canvas_window = self.main_canvas.create_window(
            (0, 0), window=self.main_content, anchor='nw'
        )

        def _on_content_configure(_event=None):
            self.main_canvas.configure(scrollregion=self.main_canvas.bbox("all"))

        def _on_canvas_configure(event):
            self.main_canvas.itemconfigure(self.main_canvas_window, width=event.width)

        self.main_content.bind("<Configure>", _on_content_configure)
        self.main_canvas.bind("<Configure>", _on_canvas_configure)

        def _on_mousewheel(event):
            # Windows/macOS
            if getattr(event, "delta", 0):
                self.main_canvas.yview_scroll(int(-event.delta / 120), "units")
            # Linux
            elif getattr(event, "num", None) == 4:
                self.main_canvas.yview_scroll(-1, "units")
            elif getattr(event, "num", None) == 5:
                self.main_canvas.yview_scroll(1, "units")

        for target in (self.main_canvas, self.main_content):
            target.bind("<MouseWheel>", _on_mousewheel)
            target.bind("<Button-4>", _on_mousewheel)
            target.bind("<Button-5>", _on_mousewheel)

        # 엔트리/리스트박스 등 내부 위젯에 포커스가 있어도 휠 스크롤 동작하도록 전역 바인딩
        self.root.bind_all("<MouseWheel>", _on_mousewheel, add="+")
        self.root.bind_all("<Button-4>", _on_mousewheel, add="+")
        self.root.bind_all("<Button-5>", _on_mousewheel, add="+")

        tk.Label(
            self.main_content,
            text="실시간 자산 & 수익률 계산기",
            font=self.FONT_TITLE,
            bg=self.BG,
            fg=self.FG
        ).pack(pady=(14, 10))

        frame_input = self._build_card_frame(self.main_content)
        frame_input.pack(pady=6, fill='x', padx=20)
        frame_input.columnconfigure(1, weight=1)

        # 거래 기준 계좌(매수/매도 팝업에서 기본값으로 사용)
        self._make_label(frame_input, "계좌명").grid(row=0, column=0, sticky='w')
        self.ent_account = ttk.Combobox(
            frame_input,
            font=self.FONT_MAIN,
            state="normal",
            values=["일반 계좌"],
            style="Modern.TCombobox"
        )
        self.ent_account.grid(row=0, column=1, pady=5, padx=(10, 0), sticky="ew")
        self.ent_account.set("일반 계좌")

        tk.Label(
            frame_input,
            text="매수/매도 입력은 아래 버튼의 별도 팝업에서 처리합니다.",
            bg=self.CARD_BG,
            fg=self.MUTED,
            font=self.FONT_CAPTION,
        ).grid(row=1, column=0, columnspan=2, sticky="w", pady=(2, 4))

        trade_btn_row = tk.Frame(frame_input, bg=self.CARD_BG)
        trade_btn_row.grid(row=2, column=0, columnspan=2, pady=(8, 4), sticky="ew")
        self._make_button(
            trade_btn_row,
            text="🟢 매수 입력창",
            command=self.open_buy_trade_window,
            bg=self.ACCENT,
            fg="#0D1117",
            bold=True,
        ).pack(side="left", fill="x", expand=True)
        self._make_button(
            trade_btn_row,
            text="🔴 매도 입력창",
            command=self.open_sell_trade_window,
            bg="#E5534B",
            fg="white",
            bold=True,
        ).pack(side="left", fill="x", expand=True, padx=(10, 0))

        frame_cash = self._build_card_frame(self.main_content)
        frame_cash.pack(pady=6, fill='x', padx=20)
        frame_cash.columnconfigure(1, weight=1)

        self._make_label(frame_cash, "원화 예수금(KRW)").grid(row=0, column=0, sticky='w')
        self.ent_krw = self._make_entry(frame_cash)
        self.ent_krw.grid(row=0, column=1, pady=5, padx=(10, 0), sticky="ew")

        self._make_label(frame_cash, "달러 예수금(USD)").grid(row=1, column=0, sticky='w')
        self.ent_usd = self._make_entry(frame_cash)
        self.ent_usd.grid(row=1, column=1, pady=5, padx=(10, 0), sticky="ew")

        self._make_button(
            frame_cash,
            text="현금 자산 추가하기",
            command=self.add_cash,
            bg=self.ACCENT_ALT,
            fg="#0D1117",
            bold=True
        ).grid(row=2, column=0, columnspan=2, pady=(10, 4), sticky="ew")
        tk.Label(
            frame_cash,
            text="(위「계좌명」칸의 계좌에 예수금이 반영됩니다)",
            bg=self.CARD_BG,
            fg=self.MUTED,
            font=self.FONT_CAPTION
        ).grid(row=3, column=0, columnspan=2, sticky='w')

        frame_hist = self._build_card_frame(self.main_content)
        frame_hist.pack(pady=6, fill="x", padx=20)
        tk.Label(
            frame_hist,
            text="포트폴리오 히스토리 (일별 스냅샷) 파일",
            font=(self.FONT_MAIN[0], 12, "bold"),
            bg=self.CARD_BG,
            fg=self.FG,
        ).pack(anchor="w")
        tk.Label(
            frame_hist,
            text="「계산 및 차트/수익률 보기」 실행 시 이 JSON에 누적 저장됩니다. 사용할 파일을 고릅니다. 아직 파일이 없으면 해당 위치에 빈 .json을 만든 뒤 선택하세요.",
            bg=self.CARD_BG,
            fg=self.MUTED,
            font=self.FONT_CAPTION,
            wraplength=520,
            justify="left",
        ).pack(anchor="w", pady=(2, 8))
        hist_row = tk.Frame(frame_hist, bg=self.CARD_BG)
        hist_row.pack(fill="x")
        self.lbl_portfolio_history_path = tk.Label(
            hist_row,
            text="",
            bg=self.CARD_BG,
            fg=self.ACCENT_ALT,
            font=self.FONT_CAPTION,
            anchor="w",
            justify="left",
            wraplength=400,
        )
        self.lbl_portfolio_history_path.pack(side="left", fill="x", expand=True)
        self._make_button(
            hist_row,
            text="파일 선택…",
            command=self.choose_portfolio_history_path,
            bg="#304B67",
            bold=True,
            pad=(10, 6),
        ).pack(side="right", padx=(8, 0))
        self._refresh_portfolio_history_path_label()

        frame_file = tk.Frame(self.main_content, bg=self.BG)
        frame_file.pack(pady=6, padx=20, fill="x")

        self._make_button(
            frame_file,
            text="📂 JSON 불러오기",
            command=self.load_from_json,
            bg="#304B67",
            bold=True
        ).pack(side='left', padx=(0, 8))
        self._make_button(
            frame_file,
            text="💾 저장(덮어쓰기)",
            command=self.save_to_current_json,
            bg="#2E5A47",
            bold=True
        ).pack(side='left', padx=8)
        self._make_button(
            frame_file,
            text="💾 JSON 내보내기",
            command=self.save_to_json,
            bg="#2F6F5A",
            bold=True
        ).pack(side='left', padx=8)
        self._make_button(
            frame_file,
            text="🧾 실현손익 리포트",
            command=self.open_realized_pnl_report,
            bg="#5B3B8C",
            bold=True
        ).pack(side='left', padx=8)

        frame_rebal = self._build_card_frame(self.main_content)
        frame_rebal.pack(pady=6, fill='x', padx=20)

        tk.Checkbutton(
            frame_rebal,
            text="리밸런싱 가이드 ON/OFF",
            variable=self.rebalance_enabled,
            bg=self.CARD_BG,
            fg=self.FG,
            selectcolor=self.ENTRY_BG,
            activebackground=self.CARD_BG,
            activeforeground=self.FG,
            font=self.FONT_MAIN
        ).grid(row=0, column=0, columnspan=5, sticky='w', pady=(0, 6))

        self._make_label(frame_rebal, "주식").grid(row=1, column=0, padx=3, sticky='w')
        self.ent_ratio_stock = self._make_entry(frame_rebal, width=5)
        self.ent_ratio_stock.grid(row=1, column=1, padx=3)
        self.ent_ratio_stock.insert(0, "20")

        self._make_label(frame_rebal, "채권").grid(row=1, column=2, padx=3, sticky='w')
        self.ent_ratio_bond = self._make_entry(frame_rebal, width=5)
        self.ent_ratio_bond.grid(row=1, column=3, padx=3)
        self.ent_ratio_bond.insert(0, "20")

        self._make_label(frame_rebal, "금").grid(row=2, column=0, padx=3, sticky='w')
        self.ent_ratio_gold = self._make_entry(frame_rebal, width=5)
        self.ent_ratio_gold.grid(row=2, column=1, padx=3)
        self.ent_ratio_gold.insert(0, "20")

        self._make_label(frame_rebal, "원자재").grid(row=2, column=2, padx=3, sticky='w')
        self.ent_ratio_comm = self._make_entry(frame_rebal, width=5)
        self.ent_ratio_comm.grid(row=2, column=3, padx=3)
        self.ent_ratio_comm.insert(0, "20")

        self._make_label(frame_rebal, "현금").grid(row=3, column=0, padx=3, sticky='w')
        self.ent_ratio_cash = self._make_entry(frame_rebal, width=5)
        self.ent_ratio_cash.grid(row=3, column=1, padx=3)
        self.ent_ratio_cash.insert(0, "20")

        self.listbox = tk.Listbox(
            self.main_content,
            bg=self.ENTRY_BG,
            fg=self.FG,
            font=(self.FONT_MAIN[0], 10),
            height=7,
            selectbackground="#2F81F7",
            selectforeground=self.FG,
            relief="flat",
            highlightthickness=1,
            highlightbackground=self.BORDER,
            highlightcolor=self.ACCENT
        )
        self.listbox.pack(fill='both', padx=20, pady=6)

        self.lbl_status = tk.Label(
            self.main_content,
            text="자산을 추가하거나 JSON 파일을 불러오세요.",
            bg=self.BG,
            fg=self.MUTED,
            font=self.FONT_MAIN
        )
        self.lbl_status.pack(pady=5)

        frame_bottom = tk.Frame(self.main_content, bg=self.BG)
        frame_bottom.pack(pady=10, padx=20, fill="x")

        self.btn_main_calc = self._make_button(
            frame_bottom,
            text="📊 계산 및 차트/수익률 보기",
            command=self.calculate_and_draw,
            bg="#1F6FEB",
            bold=True,
            pad=(12, 7)
        )
        self.btn_main_calc.pack(side='left', padx=(0, 6))

        self.btn_main_reset = self._make_button(
            frame_bottom,
            text="초기화",
            command=self.clear_all,
            bg="#6E2E2E"
        )
        self.btn_main_reset.pack(side='left', padx=6)

        alpha_wrap = tk.Frame(frame_bottom, bg=self.BG)
        alpha_wrap.pack(side='left', padx=(8, 0), fill='x', expand=True)
        self.lbl_alpha = tk.Label(
            alpha_wrap,
            text="투명도: 100%",
            bg=self.BG,
            fg="#7EE787",
            font=self.FONT_MAIN
        )
        self.lbl_alpha.pack(side='left', padx=(0, 8))
        self.alpha_scale = tk.Scale(
            alpha_wrap,
            from_=5,
            to=100,
            orient='horizontal',
            resolution=5,
            showvalue=False,
            command=self.on_alpha_slider_change,
            bg=self.BG,
            fg=self.FG,
            troughcolor=self.ENTRY_BG,
            highlightthickness=0,
            activebackground=self.ACCENT,
            font=self.FONT_CAPTION,
            length=160
        )
        self.alpha_scale.set(int(round(self.current_alpha * 100)))
        self.alpha_scale.pack(side='left', fill='x', expand=True)

    def refresh_account_options(self, preferred_account=None):
        if not hasattr(self, "ent_account"):
            return
        accounts = set()
        for item in self.portfolio:
            acc = str(item.get("account", "")).strip() or "일반 계좌"
            accounts.add(acc)
        for ent in self.account_cash:
            acc = str(ent.get("account", "")).strip() or "일반 계좌"
            accounts.add(acc)
        accounts.add("일반 계좌")

        current_value = str(self.ent_account.get()).strip()
        if current_value:
            accounts.add(current_value)

        sorted_accounts = sorted(accounts)
        self.ent_account["values"] = sorted_accounts

        target = str(preferred_account or "").strip() or current_value or "일반 계좌"
        self.ent_account.set(target)

    def refresh_ticker_options(self, preferred_account: str | None = None):
        """
        현재(또는 preferred_account) 계좌에 포함된 종목 ticker를 콤보박스 후보로 갱신한다.
        """
        if not hasattr(self, "ent_ticker"):
            return
        account = str(preferred_account or "").strip() or str(self.ent_account.get()).strip() or "일반 계좌"
        try:
            current_ticker = self._parse_ticker_from_combo_value(str(self.ent_ticker.get() or ""))
        except Exception:
            current_ticker = ""

        choices = []
        try:
            # (ticker, name, qty) 목록을 활용
            for t, n, _q in self._portfolio_choices_for_account(account):
                ts = str(t or "").strip()
                ns = str(n or "").strip()
                if ts:
                    label = f"{ts} | {ns}" if ns else ts
                    choices.append((ts, label))
        except Exception:
            choices = []

        # ticker 기준 중복 제거 + 정렬
        uniq_by_ticker = {}
        for t, label in choices:
            uniq_by_ticker[str(t).upper()] = label
        labels = [uniq_by_ticker[k] for k in sorted(uniq_by_ticker.keys())]
        try:
            self.ent_ticker["values"] = labels
        except Exception:
            pass

        if current_ticker and any(current_ticker.upper() == self._parse_ticker_from_combo_value(v).upper() for v in labels):
            # 사용자가 이미 입력/선택한 값 유지
            return
        # 계좌 변경 직후에는 티커칸을 비워서 오입력 방지
        try:
            self.ent_ticker.set("")
        except Exception:
            try:
                self.ent_ticker.delete(0, tk.END)
            except Exception:
                pass
        self._sync_buy_ex_enabled_from_ticker()

    def _autofill_name_from_ticker(self):
        """
        계좌/티커 기준으로 기존 종목명을 찾아 종목명 입력칸에 자동 반영한다.
        """
        account = str(self.ent_account.get()).strip() or "일반 계좌"
        ticker = self._parse_ticker_from_combo_value(str(self.ent_ticker.get()))
        holding, _idx = self._find_portfolio_holding(account, ticker)
        if not holding:
            return
        try:
            name = str(holding.get("name", "")).strip()
            if name:
                self.ent_name.delete(0, tk.END)
                self.ent_name.insert(0, name)
        except Exception:
            pass
        # 보유 수량/평단도 함께 표시(추가매수 시 바로 덮어쓰기 쉽게 전체 선택)
        try:
            qty = holding.get("qty", "")
            avg = holding.get("avg_price", "")
            if qty != "":
                self.ent_qty.delete(0, tk.END)
                self.ent_qty.insert(0, f"{float(qty):g}")
                self.ent_qty.selection_range(0, tk.END)
            if avg != "":
                self.ent_avg.delete(0, tk.END)
                # KR은 원단위일 수 있어 불필요한 .0 제거
                try:
                    av = float(avg)
                    self.ent_avg.insert(0, f"{av:g}")
                except Exception:
                    self.ent_avg.insert(0, str(avg))
                self.ent_avg.selection_range(0, tk.END)
        except Exception:
            pass
        # 해외 종목이면 매입 환율도 자동 표시
        try:
            if not is_korean_ticker(ticker):
                bex = holding.get("buy_exchange_rate", "")
                if bex != "":
                    self.ent_buy_ex.delete(0, tk.END)
                    try:
                        self.ent_buy_ex.insert(0, f"{float(bex):g}")
                    except Exception:
                        self.ent_buy_ex.insert(0, str(bex))
                    self.ent_buy_ex.selection_range(0, tk.END)
        except Exception:
            pass

    def _show_pie_detail_popup(self, parent, title, body):
        if not body or not str(body).strip():
            return
        win = tk.Toplevel(parent)
        win.title(title)
        win.geometry("480x420")
        win.configure(bg=self.BG)
        self.bind_escape_to_close(win)
        try:
            win.attributes('-alpha', self.current_alpha)
            win.after(100, lambda: win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass
        scrollbar = tk.Scrollbar(win)
        scrollbar.pack(side='right', fill='y')
        txt = tk.Text(
            win,
            bg=self.ENTRY_BG,
            fg=self.FG,
            font=(self.FONT_MAIN[0], 10),
            wrap=tk.WORD,
            yscrollcommand=scrollbar.set,
            padx=12,
            pady=12,
        )
        txt.pack(side='left', fill='both', expand=True)
        scrollbar.config(command=txt.yview)
        txt.insert(tk.END, body)
        txt.config(state='disabled')

    def _format_macro_category_breakdown(self, category):
        """대분류 자산군에 포함된 예수금·종목과 평가금액을 텍스트로 정리한다."""
        rows = []
        total_cat = float(self.current_macro_alloc.get(category, 0.0))
        ex = float(getattr(self, "current_exchange_rate", 1400.0))
        cash_krw_total = 0.0
        cash_usd_total = 0.0
        cash_usd_val_krw_total = 0.0
        cash_krw_by_account = defaultdict(float)
        cash_usd_by_account = defaultdict(float)

        if category == "현금성 자산":
            for ent in self.account_cash:
                acc = str(ent.get("account", "")).strip() or "일반 계좌"
                ck = float(ent.get("cash_krw", 0) or 0)
                cu = float(ent.get("cash_usd", 0) or 0)
                cash_krw_total += ck
                cash_usd_total += cu
                cash_usd_val_krw_total += (cu * ex)
                if ck > 0:
                    cash_krw_by_account[acc] += ck
                if cu > 0:
                    cash_usd_by_account[acc] += cu
                if ck > 0:
                    rows.append((f"예수금 (KRW) · {acc}", ck))
                if cu > 0:
                    rows.append((f"예수금 (USD→원화) · {acc}", cu * ex))

        for d in self.current_report_data:
            name = d.get("name", "")
            if d.get("is_fixed"):
                cat = get_asset_category(name, "")
            else:
                ticker = str(d.get("ticker", "")).strip()
                cat = get_asset_category(name, ticker)
            if cat != category:
                continue
            val = float(d.get("val", 0))
            if d.get("is_fixed"):
                desc = f"{name} [실물/고정]"
            else:
                ticker = str(d.get("ticker", "")).strip()
                acc = d.get("account", "")
                desc = f"{name} ({ticker})" if ticker else name
                if acc:
                    desc += f" · {acc}"
                # 현금성 자산 통화 분해: 해외 종목은 외화로, 나머지는 원화로 본다.
                if category == "현금성 자산":
                    if d.get("is_us"):
                        qty = float(d.get("qty", 0) or 0)
                        cur_p = float(d.get("cur_p", 0) or 0)
                        usd_amt = qty * cur_p
                        if usd_amt > 0:
                            cash_usd_total += usd_amt
                            cash_usd_val_krw_total += val
                    else:
                        cash_krw_total += val
            rows.append((desc, val))

        rows.sort(key=lambda x: -x[1])
        lines = [f"【{category}】 포함 종목 · 평가금액", "=" * 40, ""]
        if category == "현금성 자산":
            lines.append(f"원화 자산 합계: {int(round(cash_krw_total)):,}원")
            lines.append(f"외화 자산 합계: {cash_usd_total:,.2f} USD (원화환산 {int(round(cash_usd_val_krw_total)):,}원)")
            if cash_krw_by_account:
                lines.append("원화 현금(계좌별):")
                for acc, amount in sorted(cash_krw_by_account.items(), key=lambda x: -x[1]):
                    lines.append(f"  - {acc}: {int(round(amount)):,}원")
            if cash_usd_by_account:
                lines.append("외화 현금(계좌별):")
                for acc, amount in sorted(cash_usd_by_account.items(), key=lambda x: -x[1]):
                    lines.append(f"  - {acc}: {amount:,.2f} USD (원화환산 {int(round(amount * ex)):,}원)")
            lines.append("")
        if not rows:
            lines.append("(해당 자산군에 표시할 항목이 없습니다.)")
        else:
            for desc, val in rows:
                pct = (val / total_cat * 100) if total_cat > 0 else 0.0
                lines.append(f"• {desc}")
                lines.append(f"    {int(val):,}원 ({pct:.1f}%)")
            lines.append("")
            lines.append(f"합계 (자산군): {int(round(total_cat)):,}원")
        return "\n".join(lines)

    def _format_stock_pie_slice_breakdown(self, slice_label, slice_total):
        """종목별 원형 차트의 한 조각(이름 또는 '현금 및 현금성 자산')에 대한 내역."""
        slice_total = float(slice_total)
        if slice_label == "현금 및 현금성 자산":
            return self._format_macro_category_breakdown("현금성 자산")

        rows = []
        for d in self.current_report_data:
            name = d.get("name", "")
            if d.get("is_fixed"):
                if name != slice_label:
                    continue
                val = float(d.get("val", 0))
                rows.append((f"{name} [실물/고정]", val))
            else:
                if name != slice_label:
                    continue
                val = float(d.get("val", 0))
                ticker = str(d.get("ticker", "")).strip()
                acc = d.get("account", "")
                desc = f"{name} ({ticker})" if ticker else name
                if acc:
                    desc += f" · {acc}"
                rows.append((desc, val))

        rows.sort(key=lambda x: -x[1])
        lines = [f"【{slice_label}】 보유 내역", "=" * 40, ""]
        if not rows:
            lines.append("(표시할 항목이 없습니다.)")
        else:
            for desc, val in rows:
                pct = (val / slice_total * 100) if slice_total > 0 else 0.0
                lines.append(f"• {desc}")
                lines.append(f"    {int(val):,}원 ({pct:.1f}%)")
            lines.append("")
            lines.append(f"조각 합계: {int(round(slice_total)):,}원")
        return "\n".join(lines)

    def _setup_pie_hover(self, canvas, fig, ax, wedges, labels, sizes, parent_win=None, on_wedge_click=None):
        total = sum(sizes)
        annot = ax.annotate(
            "",
            xy=(0, 0),
            fontsize=11,
            fontweight='bold',
            color='white',
            ha='center',
            va='center',
            bbox=dict(boxstyle="round,pad=0.4", fc=self.BTN_BG, ec="white", lw=1.5, alpha=0.95),
        )
        annot.set_visible(False)

        prev_idx = [None]

        def on_hover(event):
            if event.inaxes != ax:
                if annot.get_visible():
                    annot.set_visible(False)
                    for w in wedges:
                        w.set_alpha(1.0)
                    canvas.draw_idle()
                    prev_idx[0] = None
                return

            for i, w in enumerate(wedges):
                hit, _ = w.contains(event)
                if hit:
                    if prev_idx[0] == i:
                        return
                    prev_idx[0] = i
                    pct = sizes[i] / total * 100
                    text = f"{labels[i]}\n{int(sizes[i]):,}원 ({pct:.1f}%)"
                    theta = (w.theta1 + w.theta2) / 2
                    r = 0.5
                    x = r * math.cos(math.radians(theta))
                    y = r * math.sin(math.radians(theta))
                    annot.xy = (x, y)
                    annot.set_text(text)
                    annot.set_visible(True)
                    for j, ww in enumerate(wedges):
                        ww.set_alpha(0.4 if j != i else 1.0)
                    canvas.draw_idle()
                    return

            if annot.get_visible():
                annot.set_visible(False)
                for w in wedges:
                    w.set_alpha(1.0)
                canvas.draw_idle()
                prev_idx[0] = None

        def on_click(event):
            if on_wedge_click is None or parent_win is None:
                return
            if event.inaxes != ax or event.button != 1:
                return
            for i, w in enumerate(wedges):
                hit, _ = w.contains(event)
                if hit:
                    on_wedge_click(i)
                    return

        fig.canvas.mpl_connect('motion_notify_event', on_hover)
        fig.canvas.mpl_connect('button_press_event', on_click)

    def _disconnect_line_chart_hovers(self):
        for cid in getattr(self, "_line_chart_hover_cids", []):
            try:
                self.canvas_line.mpl_disconnect(cid)
            except Exception:
                pass
        self._line_chart_hover_cids = []

    def _setup_line_series_hover(self, ax, dates, y_values, build_tooltip, pick_px=22.0):
        """단일 Y 꺾은선: 가까운 마커에 대해 build_tooltip(i) 문자열을 툴팁으로 표시."""
        n = len(dates)
        if n == 0 or not hasattr(self, "canvas_line"):
            return

        canvas = self.canvas_line
        if not hasattr(self, "_line_chart_hover_cids"):
            self._line_chart_hover_cids = []

        annot = ax.annotate(
            "",
            xy=(0, 0),
            xytext=(10, 10),
            textcoords="offset points",
            fontsize=9,
            color="white",
            ha="left",
            va="bottom",
            bbox=dict(boxstyle="round,pad=0.35", fc=self.BTN_BG, ec="white", lw=1, alpha=0.95),
            zorder=100,
        )
        annot.set_clip_on(False)
        annot.set_visible(False)

        x_nums = mdates.date2num(pd.DatetimeIndex(dates))
        yv = np.asarray(y_values, dtype=float)
        prev_idx = [None]

        def on_hover(event):
            if event.inaxes != ax:
                if annot.get_visible():
                    annot.set_visible(False)
                    canvas.draw_idle()
                    prev_idx[0] = None
                return

            best_i = None
            best_d = pick_px + 1.0
            for i in range(n):
                try:
                    px, py = ax.transData.transform((x_nums[i], yv[i]))
                except Exception:
                    continue
                dist = math.hypot(event.x - px, event.y - py)
                if dist < best_d:
                    best_d = dist
                    best_i = i

            if best_i is None or best_d > pick_px:
                if annot.get_visible():
                    annot.set_visible(False)
                    canvas.draw_idle()
                    prev_idx[0] = None
                return

            if prev_idx[0] == best_i and annot.get_visible():
                return
            prev_idx[0] = best_i

            annot.xy = (x_nums[best_i], yv[best_i])
            annot.set_text(build_tooltip(best_i))

            x0, x1 = ax.get_xlim()
            span = (x1 - x0) or 1.0
            x_frac = (x_nums[best_i] - x0) / span
            _off = ((-12, 10) if x_frac > 0.62 else (12, 10))
            if hasattr(annot, "xyann"):
                annot.xyann = _off
            else:
                annot.xytext = _off
            annot.set_ha("right" if x_frac > 0.62 else "left")
            annot.set_visible(True)
            canvas.draw_idle()

        cid = canvas.mpl_connect("motion_notify_event", on_hover)
        self._line_chart_hover_cids.append(cid)

    def _setup_line_chart_val_hover(self, ax_val, dates, prins, vals):
        """
        자산 규모(원금·평가금) 꺾은선이 겹쳐 보일 때, 마우스 근처 시점의 원금·평가금을 툴팁으로 표시한다.
        """
        n = len(dates)
        if n == 0 or not hasattr(self, "canvas_line"):
            return

        canvas = self.canvas_line
        if not hasattr(self, "_line_chart_hover_cids"):
            self._line_chart_hover_cids = []

        annot = ax_val.annotate(
            "",
            xy=(0, 0),
            xytext=(10, 10),
            textcoords="offset points",
            fontsize=9,
            color="white",
            ha="left",
            va="bottom",
            bbox=dict(boxstyle="round,pad=0.35", fc=self.BTN_BG, ec="white", lw=1, alpha=0.95),
            zorder=100,
        )
        annot.set_clip_on(False)
        annot.set_visible(False)

        x_nums = mdates.date2num(pd.DatetimeIndex(dates))
        pr = np.asarray(prins, dtype=float)
        va = np.asarray(vals, dtype=float)
        prev_idx = [None]
        pick_px = 22.0

        def on_hover(event):
            if event.inaxes != ax_val:
                if annot.get_visible():
                    annot.set_visible(False)
                    canvas.draw_idle()
                    prev_idx[0] = None
                return

            best_i = None
            best_d = pick_px + 1.0
            for i in range(n):
                for y in (pr[i], va[i]):
                    try:
                        px, py = ax_val.transData.transform((x_nums[i], y))
                    except Exception:
                        continue
                    d = math.hypot(event.x - px, event.y - py)
                    if d < best_d:
                        best_d = d
                        best_i = i

            if best_i is None or best_d > pick_px:
                if annot.get_visible():
                    annot.set_visible(False)
                    canvas.draw_idle()
                    prev_idx[0] = None
                return

            if prev_idx[0] == best_i and annot.get_visible():
                return
            prev_idx[0] = best_i

            dstr = _date_with_weekday_kr(dates[best_i])
            annot.xy = (x_nums[best_i], max(pr[best_i], va[best_i]))
            annot.set_text(f"{dstr}\n투자원금: {int(pr[best_i]):,}원\n평가금: {int(va[best_i]):,}원")
            x0, x1 = ax_val.get_xlim()
            span = (x1 - x0) or 1.0
            x_frac = (x_nums[best_i] - x0) / span
            _off = ((-12, 10) if x_frac > 0.62 else (12, 10))
            if hasattr(annot, "xyann"):
                annot.xyann = _off
            else:
                annot.xytext = _off
            annot.set_ha("right" if x_frac > 0.62 else "left")
            annot.set_visible(True)
            canvas.draw_idle()

        cid = canvas.mpl_connect("motion_notify_event", on_hover)
        self._line_chart_hover_cids.append(cid)

    def on_alpha_slider_change(self, value):
        try:
            raw = float(value)
            snapped = int(round(raw / 5.0) * 5)
            snapped = min(100, max(5, snapped))
            if abs(raw - snapped) > 0.01:
                # Scale 콜백 값은 실수일 수 있어 5 단위로 강제 스냅한다.
                self.alpha_scale.set(snapped)
                return
            self.current_alpha = snapped / 100.0
        except Exception:
            return
        self.apply_transparency()

    def _set_window_alpha(self, window) -> None:
        alpha = float(getattr(self, "current_alpha", 1.0))
        try:
            window.attributes("-alpha", alpha)
            return
        except Exception:
            pass
        try:
            window.wm_attributes("-alpha", alpha)
            return
        except Exception:
            pass
        # 일부 Tk/WM 조합은 문자열 파라미터만 받는다.
        try:
            window.attributes("-alpha", str(alpha))
            return
        except Exception:
            pass
        try:
            window.wm_attributes("-alpha", str(alpha))
        except Exception:
            pass

    def _schedule_alpha_sync_for_window(self, window) -> None:
        def _apply(_event=None):
            self._set_window_alpha(window)

        try:
            window.bind("<Map>", _apply, add="+")
            window.bind("<Visibility>", _apply, add="+")
            window.bind("<FocusIn>", _apply, add="+")
            window.after_idle(_apply)
            for ms in (30, 100, 250, 500, 1000):
                window.after(ms, _apply)
        except Exception:
            pass

    def apply_transparency(self):
        try:
            self._set_window_alpha(self.root)
            alpha_percent = int(round(self.current_alpha * 100))
            alpha_percent = min(100, max(5, alpha_percent))
            if hasattr(self, "lbl_alpha"):
                self.lbl_alpha.config(text=f"투명도: {alpha_percent}%")
            if hasattr(self, "alpha_scale") and int(self.alpha_scale.get()) != alpha_percent:
                self.alpha_scale.set(alpha_percent)
            for child in self.root.winfo_children():
                if isinstance(child, tk.Toplevel):
                    self._set_window_alpha(child)
        except Exception:
            pass

    def bind_escape_to_close(self, window):
        try:
            window.bind("<Escape>", lambda event, w=window: w.destroy())
        except Exception:
            pass

    def _cancel_chart_auto_refresh(self):
        if self.chart_auto_refresh_job and self.root.winfo_exists():
            try:
                self.root.after_cancel(self.chart_auto_refresh_job)
            except Exception:
                pass
        self.chart_auto_refresh_job = None

    def _schedule_chart_auto_refresh(self):
        self._cancel_chart_auto_refresh()
        if not (self.chart_win and self.chart_win.winfo_exists()):
            return
        self.chart_auto_refresh_job = self.root.after(
            self.chart_auto_refresh_interval_ms,
            self._on_chart_auto_refresh
        )

    def _on_chart_auto_refresh(self):
        self.chart_auto_refresh_job = None
        if not (self.chart_win and self.chart_win.winfo_exists()):
            return
        try:
            self.lbl_status.config(text="그래프 자동 갱신 중... (30초 주기)", fg="#87CEFA")
            self.calculate_and_draw(in_place_refresh=True)
        except Exception:
            self.lbl_status.config(text="자동 갱신 실패 - 다음 주기에 재시도", fg="#FF6B6B")
            self._schedule_chart_auto_refresh()

    def _close_chart_window(self):
        self._cancel_chart_auto_refresh()
        try:
            if self.chart_win and self.chart_win.winfo_exists():
                self.chart_win.destroy()
        except Exception:
            pass
        self.chart_win = None
        self.report_text_widget = None
        self.daily_window_scale = None
        self.daily_window_label = None

    def _on_daily_window_scroll(self, value):
        if self._updating_daily_window_scale:
            return
        try:
            start = int(float(value))
        except Exception:
            start = 0
        start = max(0, min(start, int(getattr(self, "daily_window_max_start", 0))))
        self.daily_window_start = start
        self.daily_window_follow_latest = (start >= int(getattr(self, "daily_window_max_start", 0)))
        if getattr(self, "current_chart_view_mode", "일간") == "일간":
            self.update_line_chart("일간")

    def _show_loading_overlay(self):
        if not (self.chart_win and self.chart_win.winfo_exists()):
            return
        self._loading_overlay = tk.Frame(self.chart_win, bg="#0D1117")
        self._loading_overlay.place(relx=0, rely=0, relwidth=1, relheight=1)

        inner = tk.Frame(self._loading_overlay, bg="#161B22", bd=0, highlightthickness=1, highlightbackground="#30363D")
        inner.place(relx=0.5, rely=0.5, anchor="center")

        tk.Label(
            inner, text="⏳", font=("Segoe UI Emoji", 32), bg="#161B22", fg="#58A6FF"
        ).pack(pady=(24, 4))
        tk.Label(
            inner, text="보고서 갱신 중...", font=(self.FONT_MAIN[0], 16, "bold"),
            bg="#161B22", fg="#58A6FF"
        ).pack()
        tk.Label(
            inner, text="실시간 시세를 불러오고 있습니다. 잠시만 기다려주세요.",
            font=(self.FONT_MAIN[0], 11), bg="#161B22", fg="#8B949E"
        ).pack(pady=(4, 24), padx=32)

        self._loading_overlay.lift()
        self.chart_win.update_idletasks()

    def _hide_loading_overlay(self):
        overlay = getattr(self, "_loading_overlay", None)
        if overlay:
            try:
                overlay.destroy()
            except Exception:
                pass
            self._loading_overlay = None

    def refresh_report_on_click(self):
        if not (self.chart_win and self.chart_win.winfo_exists()):
            self.lbl_status.config(text="보고서 창이 열려있지 않습니다.", fg="#FF6B6B")
            return
        try:
            self.lbl_status.config(text="보고서 수동 갱신 중...", fg="#87CEFA")
            self._show_loading_overlay()
            self.root.update_idletasks()
            self.calculate_and_draw(in_place_refresh=True)
        except Exception:
            self.lbl_status.config(text="수동 갱신 실패", fg="#FF6B6B")
        finally:
            self._hide_loading_overlay()

    def _auto_save_loaded_portfolio_json(self) -> bool:
        """
        현재 불러온 JSON 경로가 있으면 변경사항을 조용히 덮어쓰기 저장한다.
        """
        path = self.portfolio_json_path
        if not path:
            return False
        try:
            self.update_rebalance_config_from_gui()
            rebalance_ratios = dict(self.target_ratios)
            data = {
                "account_cash": self.account_cash,
                "portfolio": self.portfolio,
                "sell_records": self.sell_records,
                "rebalance_enabled": bool(self.rebalance_enabled.get()),
                "target_ratios": rebalance_ratios,
                "rebalance_ratios": rebalance_ratios,
            }
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)
            return True
        except Exception:
            return False

    def _get_or_create_account_cash(self, account: str) -> dict:
        acc = str(account or "").strip() or "일반 계좌"
        for row in self.account_cash:
            if (str(row.get("account", "")).strip() or "일반 계좌") == acc:
                if "cash_krw" not in row:
                    row["cash_krw"] = 0.0
                if "cash_usd" not in row:
                    row["cash_usd"] = 0.0
                if "usd_cost_krw" not in row:
                    row["usd_cost_krw"] = 0.0
                return row
        row = {"account": acc, "cash_krw": 0.0, "cash_usd": 0.0, "usd_cost_krw": 0.0}
        self.account_cash.append(row)
        return row

    def _round_avg_price(self, price: float, is_us: bool) -> float:
        # 추매 계산 시 과도한 소수 자릿수를 줄여 저장값을 안정화한다.
        return round(float(price), 2 if is_us else 0)

    def open_buy_trade_window(self):
        win = tk.Toplevel(self.root)
        win.title("🟢 매수 입력")
        win.geometry("620x520")
        win.configure(bg=self.BG)
        try:
            win.transient(self.root)
        except Exception:
            pass
        self.bind_escape_to_close(win)
        try:
            self._set_window_alpha(win)
            win.after(50, lambda: self._set_window_alpha(win))
            win.after(200, lambda: self._set_window_alpha(win))
        except Exception:
            pass

        card = self._build_card_frame(win)
        card.pack(fill="both", expand=True, padx=12, pady=12)
        card.columnconfigure(1, weight=1)

        tk.Label(card, text="계좌", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=0, column=0, sticky="w")
        ent_acc = ttk.Combobox(
            card,
            font=self.FONT_MAIN,
            state="normal",
            values=list(self.ent_account["values"]) if hasattr(self, "ent_account") else [],
            style="Modern.TCombobox",
        )
        ent_acc.grid(row=0, column=1, sticky="ew", pady=4, padx=(8, 0))
        ent_acc.set(str(self.ent_account.get()).strip() or "일반 계좌")

        mode_var = tk.StringVar(value="existing")
        mode_row = tk.Frame(card, bg=self.CARD_BG)
        mode_row.grid(row=1, column=0, columnspan=2, sticky="w", pady=(4, 6))
        tk.Radiobutton(mode_row, text="기존 종목 추매", variable=mode_var, value="existing", bg=self.CARD_BG, fg=self.FG, selectcolor=self.ENTRY_BG, font=self.FONT_MAIN).pack(side="left")
        tk.Radiobutton(mode_row, text="신규 종목 매수", variable=mode_var, value="new", bg=self.CARD_BG, fg=self.FG, selectcolor=self.ENTRY_BG, font=self.FONT_MAIN).pack(side="left", padx=(10, 0))

        tk.Label(card, text="종목코드/티커", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=2, column=0, sticky="w")
        ent_ticker = ttk.Combobox(card, font=self.FONT_MAIN, state="normal", values=[], style="Modern.TCombobox")
        ent_ticker.grid(row=2, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="종목명", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=3, column=0, sticky="w")
        ent_name = self._make_entry(card)
        ent_name.grid(row=3, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="수량", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=4, column=0, sticky="w")
        ent_qty = self._make_entry(card)
        ent_qty.grid(row=4, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="단가(국내 KRW / 미국 USD)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=5, column=0, sticky="w")
        ent_price = self._make_entry(card)
        ent_price.grid(row=5, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="매수 수수료(원)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=6, column=0, sticky="w")
        ent_buy_fee = self._make_entry(card)
        ent_buy_fee.grid(row=6, column=1, sticky="ew", pady=4, padx=(8, 0))
        ent_buy_fee.insert(0, "0")

        lbl_buy_ex = tk.Label(card, text="매입 환율(KRW/USD, 미국만)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN)
        lbl_buy_ex.grid(row=7, column=0, sticky="w")
        ent_buy_ex = self._make_entry(card)
        ent_buy_ex.grid(row=7, column=1, sticky="ew", pady=4, padx=(8, 0))
        try:
            ent_buy_ex.insert(0, f"{self.get_exchange_rate():.2f}")
        except Exception:
            ent_buy_ex.insert(0, "1400")

        tk.Label(card, text="(신규 선택 시) 단위중량(g, 선택)", bg=self.CARD_BG, fg=self.MUTED, font=self.FONT_CAPTION).grid(row=8, column=0, sticky="w")
        ent_unit_weight = self._make_entry(card)
        ent_unit_weight.grid(row=8, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="(신규 선택 시) price_source (선택)", bg=self.CARD_BG, fg=self.MUTED, font=self.FONT_CAPTION).grid(row=9, column=0, sticky="w")
        ent_price_source = self._make_entry(card)
        ent_price_source.grid(row=9, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="(신규 선택 시) naver category (선택)", bg=self.CARD_BG, fg=self.MUTED, font=self.FONT_CAPTION).grid(row=10, column=0, sticky="w")
        ent_naver_category = self._make_entry(card)
        ent_naver_category.grid(row=10, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="(신규 선택 시) naver reutersCode (선택)", bg=self.CARD_BG, fg=self.MUTED, font=self.FONT_CAPTION).grid(row=11, column=0, sticky="w")
        ent_naver_reuters = self._make_entry(card)
        ent_naver_reuters.grid(row=11, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="(신규 선택 시) naver unit_price (선택)", bg=self.CARD_BG, fg=self.MUTED, font=self.FONT_CAPTION).grid(row=12, column=0, sticky="w")
        ent_naver_unit = self._make_entry(card)
        ent_naver_unit.grid(row=12, column=1, sticky="ew", pady=4, padx=(8, 0))

        info_var = tk.StringVar(value="기존 종목이면 '추매 수량/매수단가'로 자동 반영됩니다.")
        tk.Label(card, textvariable=info_var, bg=self.CARD_BG, fg=self.ACCENT_ALT, font=self.FONT_CAPTION).grid(row=13, column=0, columnspan=2, sticky="w", pady=(6, 0))

        def _refresh_tickers():
            acc = str(ent_acc.get()).strip() or "일반 계좌"
            choices = self._portfolio_choices_for_account(acc)
            ent_ticker["values"] = [f"{t} | {n} | 보유 {q:g}" for (t, n, q) in choices]

        def _parse_ticker() -> str:
            return self._parse_ticker_from_combo_value(str(ent_ticker.get())).strip().upper()

        def _sync_buy_ex_state(*_args):
            ticker = _parse_ticker()
            is_us = bool(ticker) and (not is_korean_ticker(ticker))
            ent_buy_ex.config(state=("normal" if is_us else "disabled"))
            lbl_buy_ex.config(fg=(self.FG if is_us else self.MUTED))
            acc = str(ent_acc.get()).strip() or "일반 계좌"
            holding, _ = self._find_portfolio_holding(acc, ticker)
            if holding and mode_var.get() == "existing":
                h_qty = float(holding.get("qty", 0) or 0)
                h_avg = float(holding.get("avg_price", 0) or 0)
                info_var.set(f"기존 보유: {h_qty:g}주 / 평단 {h_avg:g}{'$' if is_us else '원'}")
                name = str(holding.get("name", "")).strip()
                if name and not str(ent_name.get()).strip():
                    ent_name.insert(0, name)
                if is_us and holding.get("buy_exchange_rate"):
                    try:
                        ent_buy_ex.delete(0, tk.END)
                        ent_buy_ex.insert(0, f"{float(holding.get('buy_exchange_rate')):g}")
                    except Exception:
                        pass
            elif holding and mode_var.get() == "new":
                info_var.set("같은 계좌에 동일 티커가 이미 있습니다. 신규보다 추매 모드를 권장합니다.")
            elif mode_var.get() == "new":
                info_var.set("신규 종목 매수: test2.json 포맷 필드를 입력 후 반영합니다.")
            else:
                info_var.set("기존 종목을 선택하면 추매 수량/매수단가로 반영됩니다.")

        def _confirm_buy():
            try:
                account = str(ent_acc.get()).strip() or "일반 계좌"
                ticker = _parse_ticker()
                name = str(ent_name.get()).strip()
                qty = float(str(ent_qty.get()).strip().replace(",", ""))
                price = float(str(ent_price.get()).strip().replace(",", ""))
                buy_fee_krw = float(str(ent_buy_fee.get()).strip().replace(",", "") or "0")
                if qty <= 0 or price <= 0:
                    messagebox.showwarning("입력 오류", "수량/단가는 0보다 커야 합니다.")
                    return
                if buy_fee_krw < 0:
                    messagebox.showwarning("입력 오류", "매수 수수료는 0 이상이어야 합니다.")
                    return
                if not ticker:
                    messagebox.showwarning("입력 오류", "종목코드/티커를 입력하세요.")
                    return

                holding, _ = self._find_portfolio_holding(account, ticker)
                is_us = not is_korean_ticker(ticker)
                cash_row = self._get_or_create_account_cash(account)

                if mode_var.get() == "existing":
                    if not holding:
                        messagebox.showwarning("대상 없음", "해당 계좌의 기존 종목을 찾지 못했습니다. 신규 모드를 사용하세요.")
                        return
                    old_qty = float(holding.get("qty", 0) or 0)
                    old_avg = float(holding.get("avg_price", 0) or 0)
                    new_qty = old_qty + qty
                    if new_qty <= 0:
                        messagebox.showwarning("입력 오류", "반영 후 수량이 0 이하입니다.")
                        return

                    if is_us:
                        old_buy_ex = float(holding.get("buy_exchange_rate", 0) or 0)
                        buy_ex_str = str(ent_buy_ex.get()).strip()
                        buy_ex = float(buy_ex_str.replace(",", "")) if buy_ex_str else float(self.get_exchange_rate())
                        if buy_ex <= 0:
                            messagebox.showwarning("입력 오류", "미국 종목은 매입 환율이 필요합니다.")
                            return
                        if old_buy_ex <= 0:
                            old_buy_ex = buy_ex
                        total_usd_cost = old_qty * old_avg + qty * price
                        total_krw_cost = old_qty * old_avg * old_buy_ex + qty * price * buy_ex
                        holding["qty"] = new_qty
                        holding["avg_price"] = self._round_avg_price(total_usd_cost / new_qty, is_us=True)
                        holding["buy_exchange_rate"] = (total_krw_cost / total_usd_cost) if total_usd_cost > 0 else buy_ex
                        cash_row["cash_usd"] = float(cash_row.get("cash_usd", 0) or 0) - (qty * price)
                        cash_row["cash_krw"] = float(cash_row.get("cash_krw", 0) or 0) - buy_fee_krw
                    else:
                        holding["qty"] = new_qty
                        holding["avg_price"] = self._round_avg_price(((old_qty * old_avg) + (qty * price)) / new_qty, is_us=False)
                        cash_row["cash_krw"] = float(cash_row.get("cash_krw", 0) or 0) - ((qty * price) + buy_fee_krw)
                    if name:
                        holding["name"] = name
                    self.listbox.insert(tk.END, f"[매수-추매] [{account}] {holding.get('name', ticker)} ({ticker}) | +{qty:g}주")
                else:
                    if holding:
                        messagebox.showwarning("중복 종목", "같은 계좌에 동일 티커가 이미 존재합니다. 추매 모드를 사용하세요.")
                        return
                    if not name:
                        messagebox.showwarning("입력 오류", "신규 종목은 종목명이 필요합니다.")
                        return
                    asset = {"account": account, "ticker": ticker, "name": name, "qty": qty, "avg_price": price}
                    if is_us:
                        buy_ex_str = str(ent_buy_ex.get()).strip()
                        buy_ex = float(buy_ex_str.replace(",", "")) if buy_ex_str else float(self.get_exchange_rate())
                        if buy_ex <= 0:
                            messagebox.showwarning("입력 오류", "미국 신규 종목은 매입 환율이 필요합니다.")
                            return
                        asset["buy_exchange_rate"] = buy_ex
                        cash_row["cash_usd"] = float(cash_row.get("cash_usd", 0) or 0) - (qty * price)
                        cash_row["cash_krw"] = float(cash_row.get("cash_krw", 0) or 0) - buy_fee_krw
                    else:
                        cash_row["cash_krw"] = float(cash_row.get("cash_krw", 0) or 0) - ((qty * price) + buy_fee_krw)
                    unit_weight = str(ent_unit_weight.get()).strip()
                    if unit_weight:
                        asset["unit_weight_g"] = float(unit_weight.replace(",", ""))
                    price_source = str(ent_price_source.get()).strip()
                    if price_source:
                        asset["price_source"] = price_source
                    n_cat = str(ent_naver_category.get()).strip()
                    n_reu = str(ent_naver_reuters.get()).strip()
                    n_unit = str(ent_naver_unit.get()).strip()
                    if n_cat or n_reu or n_unit:
                        asset["naver_marketindex"] = {}
                        if n_cat:
                            asset["naver_marketindex"]["category"] = n_cat
                        if n_reu:
                            asset["naver_marketindex"]["reutersCode"] = n_reu
                        if n_unit:
                            asset["naver_marketindex"]["unit_price"] = n_unit
                    self.portfolio.append(asset)
                    self.listbox.insert(tk.END, f"[매수-신규] [{account}] {name} ({ticker}) | {qty:g}주")

                self.refresh_account_options(preferred_account=account)
                saved = self._auto_save_loaded_portfolio_json()
                messagebox.showinfo("반영 완료", "매수 내역을 포트폴리오 JSON 데이터에 반영했습니다." + ("\n(불러온 JSON 파일에도 자동 저장됨)" if saved else ""))
                win.destroy()
            except Exception as e:
                messagebox.showerror("매수 반영 실패", f"매수 입력 반영 중 오류가 발생했습니다.\n\n{e}")

        ent_acc.bind("<<ComboboxSelected>>", lambda _e=None: (_refresh_tickers(), _sync_buy_ex_state()))
        ent_ticker.bind("<<ComboboxSelected>>", lambda _e=None: _sync_buy_ex_state())
        ent_ticker.bind("<FocusOut>", lambda _e=None: _sync_buy_ex_state())
        mode_var.trace_add("write", lambda *_: _sync_buy_ex_state())
        _refresh_tickers()
        _sync_buy_ex_state()

        btn_row = tk.Frame(win, bg=self.BG)
        btn_row.pack(fill="x", padx=12, pady=(0, 12))
        self._make_button(btn_row, "확인", _confirm_buy, bg=self.ACCENT, fg="#0D1117", bold=True, pad=(12, 7)).pack(side="left")
        self._make_button(btn_row, "닫기", win.destroy, bg=self.BTN_BG, fg=self.FG, bold=False, pad=(12, 7)).pack(side="left", padx=(8, 0))
        self._schedule_alpha_sync_for_window(win)
        self.apply_transparency()

    def open_sell_trade_window(self):
        win = tk.Toplevel(self.root)
        win.title("🔴 매도 입력")
        win.geometry("620x360")
        win.configure(bg=self.BG)
        try:
            win.transient(self.root)
        except Exception:
            pass
        self.bind_escape_to_close(win)
        try:
            self._set_window_alpha(win)
            win.after(50, lambda: self._set_window_alpha(win))
            win.after(200, lambda: self._set_window_alpha(win))
        except Exception:
            pass

        card = self._build_card_frame(win)
        card.pack(fill="both", expand=True, padx=12, pady=12)
        card.columnconfigure(1, weight=1)

        tk.Label(card, text="계좌", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=0, column=0, sticky="w")
        ent_acc = ttk.Combobox(
            card,
            font=self.FONT_MAIN,
            state="readonly",
            values=list(self.ent_account["values"]) if hasattr(self, "ent_account") else [],
            style="Modern.TCombobox",
        )
        ent_acc.grid(row=0, column=1, sticky="ew", pady=4, padx=(8, 0))
        ent_acc.set(str(self.ent_account.get()).strip() or "일반 계좌")

        tk.Label(card, text="종목", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=1, column=0, sticky="w")
        ent_ticker = ttk.Combobox(card, font=self.FONT_MAIN, state="readonly", values=[], style="Modern.TCombobox")
        ent_ticker.grid(row=1, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="매도 수량", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=2, column=0, sticky="w")
        ent_qty = self._make_entry(card)
        ent_qty.grid(row=2, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="매도 단가(국내 KRW / 미국 USD)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=3, column=0, sticky="w")
        ent_price = self._make_entry(card)
        ent_price.grid(row=3, column=1, sticky="ew", pady=4, padx=(8, 0))

        tk.Label(card, text="매도 수수료(원)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=4, column=0, sticky="w")
        ent_sell_fee = self._make_entry(card)
        ent_sell_fee.grid(row=4, column=1, sticky="ew", pady=4, padx=(8, 0))
        ent_sell_fee.insert(0, "0")

        lbl_sell_ex = tk.Label(card, text="매도 환율(KRW/USD, 미국만)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN)
        lbl_sell_ex.grid(row=5, column=0, sticky="w")
        ent_sell_ex = self._make_entry(card)
        ent_sell_ex.grid(row=5, column=1, sticky="ew", pady=4, padx=(8, 0))
        try:
            ent_sell_ex.insert(0, f"{self.get_exchange_rate():.2f}")
        except Exception:
            ent_sell_ex.insert(0, "1400")

        def _parse_ticker() -> str:
            raw = str(ent_ticker.get() or "").strip()
            if not raw:
                return ""
            return raw.split("|", 1)[0].strip().upper()

        def _find_holding(account: str, ticker: str):
            for item in self.portfolio:
                acc = str(item.get("account", "")).strip() or "일반 계좌"
                t = str(item.get("ticker", "")).strip().upper()
                if acc == account and t == ticker:
                    return item
            return None

        def _refresh_ticker_choices(*_args):
            acc = str(ent_acc.get()).strip() or "일반 계좌"
            choices = self._portfolio_choices_for_account(acc)
            ent_ticker["values"] = [f"{t} | {n} | 보유 {q:g}" for (t, n, q) in choices]
            if choices:
                ent_ticker.set(ent_ticker["values"][0])
            else:
                ent_ticker.set("")
            _sync_sell_ex_state()

        def _sync_sell_ex_state(*_args):
            ticker = _parse_ticker()
            is_us = bool(ticker) and (not is_korean_ticker(ticker))
            ent_sell_ex.config(state=("normal" if is_us else "disabled"))
            lbl_sell_ex.config(fg=(self.FG if is_us else self.MUTED))

        def _confirm_sell():
            try:
                account = str(ent_acc.get()).strip() or "일반 계좌"
                ticker = _parse_ticker()
                if not ticker:
                    messagebox.showwarning("입력 오류", "매도할 종목을 선택하세요.")
                    return
                holding = _find_holding(account, ticker)
                if not holding:
                    messagebox.showwarning("대상 없음", "해당 계좌/종목 보유 내역을 찾지 못했습니다.")
                    return
                qty = float(str(ent_qty.get()).strip().replace(",", ""))
                price = float(str(ent_price.get()).strip().replace(",", ""))
                sell_fee_krw = float(str(ent_sell_fee.get()).strip().replace(",", "") or "0")
                if qty <= 0 or price <= 0:
                    messagebox.showwarning("입력 오류", "수량/단가는 0보다 커야 합니다.")
                    return
                if sell_fee_krw < 0:
                    messagebox.showwarning("입력 오류", "매도 수수료는 0 이상이어야 합니다.")
                    return
                name = str(holding.get("name", "")).strip() or ticker
                is_us = not is_korean_ticker(ticker)
                sell_ex = None
                if is_us:
                    sell_ex = float(str(ent_sell_ex.get()).strip().replace(",", ""))
                    if sell_ex <= 0:
                        messagebox.showwarning("입력 오류", "미국 종목은 매도 환율이 필요합니다.")
                        return

                rec = SellRecord(
                    sell_date=datetime.date.today().strftime("%Y-%m-%d"),
                    account=account,
                    ticker=ticker,
                    name=name,
                    qty=qty,
                    sell_price=price,
                    is_us=is_us,
                    sell_exchange_rate=sell_ex,
                    fee_krw=sell_fee_krw,
                    memo="",
                ).normalized()

                old_qty = float(holding.get("qty", 0) or 0)
                if rec.qty > old_qty + 1e-12:
                    messagebox.showwarning("수량 오류", f"매도 수량이 보유 수량을 초과합니다.\n보유: {old_qty:g} / 매도: {rec.qty:g}")
                    return

                self.sell_records.append(rec.to_json())
                self._merge_and_persist_sell_records([])
                self.portfolio = apply_sell_to_portfolio(self.portfolio, rec)
                cash_row = self._get_or_create_account_cash(account)
                if is_us:
                    cash_row["cash_usd"] = float(cash_row.get("cash_usd", 0) or 0) + (qty * price)
                    cash_row["cash_krw"] = float(cash_row.get("cash_krw", 0) or 0) - sell_fee_krw
                else:
                    cash_row["cash_krw"] = float(cash_row.get("cash_krw", 0) or 0) + (qty * price) - sell_fee_krw
                self.listbox.insert(tk.END, f"[매도] [{account}] {name} ({ticker}) | {rec.qty:g}주")
                self.refresh_account_options(preferred_account=account)
                saved = self._auto_save_loaded_portfolio_json()
                messagebox.showinfo("반영 완료", "매도 내역을 포트폴리오 JSON 데이터에 반영했습니다." + ("\n(불러온 JSON 파일에도 자동 저장됨)" if saved else ""))
                win.destroy()
            except Exception as e:
                messagebox.showerror("매도 반영 실패", f"매도 입력 반영 중 오류가 발생했습니다.\n\n{e}")

        ent_acc.bind("<<ComboboxSelected>>", _refresh_ticker_choices)
        ent_ticker.bind("<<ComboboxSelected>>", _sync_sell_ex_state)
        _refresh_ticker_choices()

        btn_row = tk.Frame(win, bg=self.BG)
        btn_row.pack(fill="x", padx=12, pady=(0, 12))
        self._make_button(btn_row, "확인", _confirm_sell, bg="#E5534B", fg="white", bold=True, pad=(12, 7)).pack(side="left")
        self._make_button(btn_row, "닫기", win.destroy, bg=self.BTN_BG, fg=self.FG, bold=False, pad=(12, 7)).pack(side="left", padx=(8, 0))
        self._schedule_alpha_sync_for_window(win)
        self.apply_transparency()

    # [수정] 자산 추가 시 '계좌명' 항목 포함
    def add_asset(self):
        account = self.ent_account.get().strip() or "일반 계좌"
        ticker = self._parse_ticker_from_combo_value(str(self.ent_ticker.get()))
        name = self.ent_name.get().strip()
        qty_str = self.ent_qty.get().strip()
        avg_str = self.ent_avg.get().strip()
        if not ticker or not name or not qty_str or not avg_str:
            return
        try:
            qty = float(qty_str.replace(',', ''))
            avg_price = float(avg_str.replace(',', ''))
            buy_ex_input = None
            try:
                bex_str = str(getattr(self, "ent_buy_ex", None).get() if hasattr(self, "ent_buy_ex") else "").strip()
                if bex_str:
                    buy_ex_input = float(bex_str.replace(",", ""))
            except Exception:
                buy_ex_input = None

            holding, idx = self._find_portfolio_holding(account, ticker)
            is_buy_mode = bool(getattr(self, "add_buy_mode", tk.BooleanVar(value=False)).get())

            # 기존 보유 종목이면: 입력값을 "추가 매수수량/매수가"로 보고 평단/수량 자동 갱신
            if is_buy_mode and holding is not None and idx is not None:
                old_qty = float(holding.get("qty", 0) or 0)
                old_avg = float(holding.get("avg_price", 0) or 0)
                buy_qty = qty
                buy_price = avg_price
                if buy_qty <= 0 or buy_price <= 0:
                    return
                new_qty = old_qty + buy_qty
                if new_qty <= 0:
                    return

                if is_korean_ticker(ticker):
                    new_avg = (old_qty * old_avg + buy_qty * buy_price) / new_qty
                    holding["qty"] = new_qty
                    holding["avg_price"] = new_avg
                else:
                    # US: avg_price(USD), buy_exchange_rate(KRW/USD)
                    old_buy_ex = float(holding.get("buy_exchange_rate", 0) or 0)
                    buy_ex = float(buy_ex_input or 0) if buy_ex_input else float(self.get_exchange_rate() or 0)
                    if old_buy_ex <= 0:
                        old_buy_ex = buy_ex if buy_ex > 0 else 0.0
                    if buy_ex <= 0:
                        buy_ex = old_buy_ex if old_buy_ex > 0 else 0.0

                    total_usd_cost = old_qty * old_avg + buy_qty * buy_price
                    new_avg = total_usd_cost / new_qty if new_qty > 0 else 0.0
                    total_krw_cost = old_qty * old_avg * old_buy_ex + buy_qty * buy_price * buy_ex
                    new_buy_ex = (total_krw_cost / total_usd_cost) if total_usd_cost > 0 else buy_ex

                    holding["qty"] = new_qty
                    holding["avg_price"] = new_avg
                    holding["buy_exchange_rate"] = new_buy_ex

                # 종목명은 기존 것을 우선 유지(사용자가 바꿨다면 업데이트)
                if name and name != str(holding.get("name", "")).strip():
                    holding["name"] = name

                unit = "원" if is_korean_ticker(ticker) else "$"
                self.listbox.insert(
                    tk.END,
                    f"[{account}] [추가매수] {holding.get('name','')} ({ticker}) | +{buy_qty:g}주 @ {buy_price:g}{unit} → "
                    f"총 {float(holding.get('qty',0) or 0):g}주 / 평단 {float(holding.get('avg_price',0) or 0):g}{unit}",
                )
            else:
                asset = {'account': account, 'ticker': ticker, 'name': name, 'qty': qty, 'avg_price': avg_price}
                if not is_korean_ticker(ticker):
                    # 해외 종목은 매입 환율 입력값이 있으면 우선 사용
                    asset['buy_exchange_rate'] = float(buy_ex_input or 0) if buy_ex_input else self.get_exchange_rate()
                self.portfolio.append(asset)
                unit = "원" if is_korean_ticker(ticker) else "$"
                self.listbox.insert(tk.END, f"[{account}] {name} ({ticker}) | {qty}주 | 평단: {avg_price}{unit}")

            try:
                self.ent_ticker.set("")
            except Exception:
                self.ent_ticker.delete(0, tk.END)
            self.ent_name.delete(0, tk.END)
            self.ent_qty.delete(0, tk.END)
            self.ent_avg.delete(0, tk.END)
            try:
                self.ent_buy_ex.delete(0, tk.END)
                self.ent_buy_ex.insert(0, f"{float(getattr(self, 'current_exchange_rate', 1400.0)):g}")
            except Exception:
                pass
            self.refresh_account_options(preferred_account=account)
        except Exception:
            pass

    def add_cash(self):
        try:
            account = self.ent_account.get().strip() or "일반 계좌"
            krw_str = self.ent_krw.get().strip() or "0"
            usd_str = self.ent_usd.get().strip() or "0"
            krw = float(krw_str.replace(',', ''))
            usd = float(usd_str.replace(',', ''))
            if krw == 0 and usd == 0:
                return
            ex = self.get_exchange_rate() if usd != 0 else 0.0
            merged = None
            for e in self.account_cash:
                if e.get("account") == account:
                    e["cash_krw"] = float(e.get("cash_krw", 0)) + krw
                    e["cash_usd"] = float(e.get("cash_usd", 0)) + usd
                    e["usd_cost_krw"] = float(e.get("usd_cost_krw", 0)) + (usd * ex)
                    merged = e
                    break
            if merged is None:
                merged = {"account": account, "cash_krw": krw, "cash_usd": usd, "usd_cost_krw": usd * ex}
                self.account_cash.append(merged)
            self.ent_krw.delete(0, tk.END)
            self.ent_usd.delete(0, tk.END)
            self.listbox.insert(
                tk.END,
                f"[예수금] {account} | 누적 KRW {merged['cash_krw']:,.0f} / USD {merged['cash_usd']:,.2f}"
            )
            self.refresh_account_options(preferred_account=account)
        except Exception:
            pass

    def clear_all(self):
        self.portfolio.clear()
        self.account_cash = []
        # sell_records는 누적 데이터이므로 clear_all에서 지우지 않는다.
        self.listbox.delete(0, tk.END)
        # 입력칸도 함께 초기화(UI 리프래시)
        try:
            self.ent_account.set("일반 계좌")
        except Exception:
            pass
        try:
            self.ent_ticker.set("")
        except Exception:
            try:
                self.ent_ticker.delete(0, tk.END)
            except Exception:
                pass
        for ent in ("ent_name", "ent_qty", "ent_avg", "ent_krw", "ent_usd"):
            try:
                w = getattr(self, ent, None)
                if w is not None:
                    w.delete(0, tk.END)
            except Exception:
                pass
        try:
            if hasattr(self, "ent_buy_ex"):
                self.ent_buy_ex.config(state="normal")
                self.ent_buy_ex.delete(0, tk.END)
                self.ent_buy_ex.insert(0, f"{float(getattr(self, 'current_exchange_rate', 1400.0)):g}")
        except Exception:
            pass
        self.refresh_account_options(preferred_account="일반 계좌")
        self._sync_buy_ex_enabled_from_ticker()

    def save_to_json(self):
        filepath = filedialog.asksaveasfilename(defaultextension=".json", initialfile="my_portfolio.json")
        if not filepath:
            return
        self.update_rebalance_config_from_gui()
        rebalance_ratios = dict(self.target_ratios)
        data = {
            "account_cash": self.account_cash,
            "portfolio": self.portfolio,
            # 실현손익 기록은 별도 누적 JSON로 관리하지만, 내보내기에는 포함(백업 용도)
            "sell_records": self.sell_records,
            "rebalance_enabled": bool(self.rebalance_enabled.get()),
            "target_ratios": rebalance_ratios,
            # input JSON 호환성을 위해 별칭 키도 함께 저장한다.
            "rebalance_ratios": rebalance_ratios
        }
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=4)
            # 내보낸 경로도 “현재 경로”로 간주(이후 덮어쓰기 저장 가능)
            self.portfolio_json_path = filepath
            messagebox.showinfo("저장 완료", "포트폴리오가 저장되었습니다.")
        except Exception:
            pass

    def save_to_current_json(self):
        """
        마지막으로 불러온/저장한 JSON 파일로 덮어쓰기 저장한다.
        (경로가 없으면 기존 '내보내기(Save As)'로 유도)
        """
        path = self.portfolio_json_path
        if not path:
            # 아직 불러온 파일이 없으면 Save As로 처리
            self.save_to_json()
            return
        try:
            if not messagebox.askyesno("덮어쓰기 저장", f"아래 파일에 덮어써서 저장할까요?\n\n{path}"):
                return
        except Exception:
            # askyesno가 실패하는 특이 케이스에서는 조용히 중단
            return

        self.update_rebalance_config_from_gui()
        rebalance_ratios = dict(self.target_ratios)
        data = {
            "account_cash": self.account_cash,
            "portfolio": self.portfolio,
            # 실현손익 기록은 별도 누적 JSON로 관리하지만, 내보내기에는 포함(백업 용도)
            "sell_records": self.sell_records,
            "rebalance_enabled": bool(self.rebalance_enabled.get()),
            "target_ratios": rebalance_ratios,
            # input JSON 호환성을 위해 별칭 키도 함께 저장한다.
            "rebalance_ratios": rebalance_ratios,
        }
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)
            messagebox.showinfo("저장 완료", "포트폴리오가 저장되었습니다. (덮어쓰기)")
        except Exception:
            pass

    # [수정] JSON 불러올 때 'account' 키 인식하여 Listbox에 표시
    def load_from_json(self):
        filepath = filedialog.askopenfilename(filetypes=[("JSON 파일", "*.json")])
        if not filepath:
            return
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
            self.clear_all()
            self.portfolio = data.get("portfolio", [])
            self.portfolio_json_path = filepath
            # sell_records는 누적 데이터이므로 기본적으로 디스크본을 유지한다.
            # 단, 가져온 JSON에 sell_records가 있으면 병합(중복 제거)하여 누적 데이터에 반영한다.
            incoming = data.get("sell_records", [])
            if isinstance(incoming, list) and incoming:
                self._merge_and_persist_sell_records(incoming)
            raw_cash = data.get("account_cash")
            self.account_cash = []
            if isinstance(raw_cash, list):
                for item in raw_cash:
                    ent = _normalize_account_cash_entry(item)
                    if ent:
                        self.account_cash.append(ent)
            legacy_krw = float(data.get("cash_krw", 0.0) or 0.0)
            legacy_usd = float(data.get("cash_usd", 0.0) or 0.0)
            if not self.account_cash and (legacy_krw != 0 or legacy_usd != 0):
                self.account_cash.append({
                    "account": "예수금 (레거시 통합)",
                    "cash_krw": legacy_krw,
                    "cash_usd": legacy_usd
                })
            self.rebalance_enabled.set(bool(data.get("rebalance_enabled", False)))
            loaded_ratios = self._load_target_ratios_from_json(data)
            for k, v in loaded_ratios.items():
                self.target_ratios[k] = v
            self.sync_rebalance_entries_from_config()
            for ent in self.account_cash:
                acc = ent.get("account", "일반 계좌")
                ck = float(ent.get("cash_krw", 0) or 0)
                cu = float(ent.get("cash_usd", 0) or 0)
                self.listbox.insert(tk.END, f"[예수금] {acc} | KRW {ck:,.0f} / USD {cu:,.2f}")
            for item in self.portfolio:
                account = item.get('account', '일반 계좌')
                name = item.get('name', '')
                ticker = str(item.get('ticker', '')).strip()
                if ticker.upper() == "FIXED":
                    qty = item.get("qty", None)
                    avg_price = item.get("avg_price", None)
                    if qty is not None and avg_price is not None:
                        try:
                            self.listbox.insert(
                                tk.END,
                                f"[{account}] [실물/고정자산] {name} | 수량: {float(qty):g} | 단가: {float(avg_price):,.0f}원"
                            )
                        except Exception:
                            self.listbox.insert(tk.END, f"[{account}] [실물/고정자산] {name}")
                    else:
                        self.listbox.insert(tk.END, f"[{account}] [실물/고정자산] {name}")
                else:
                    unit = "원" if is_korean_ticker(ticker) else "$"
                    self.listbox.insert(
                        tk.END,
                        f"[{account}] {name} ({ticker}) | {item.get('qty',0)}주 | 평단: {item.get('avg_price',0)}{unit}"
                    )
            self.refresh_account_options()
        except Exception:
            pass

    def _sell_record_dedupe_key(self, d):
        try:
            # 충분히 안정적인 키(문자열화). 실사용에서는 체결ID가 없으니 이 정도로 중복 제거.
            return (
                str(d.get("sell_date", "")).strip(),
                str(d.get("account", "")).strip(),
                str(d.get("ticker", "")).strip().upper(),
                str(d.get("name", "")).strip(),
                float(d.get("qty", 0) or 0),
                float(d.get("sell_price", 0) or 0),
                bool(d.get("is_us", False)),
                float(d.get("sell_exchange_rate", 0) or 0) if d.get("sell_exchange_rate") not in (None, "") else 0.0,
                float(d.get("fee_krw", 0) or 0),
                str(d.get("memo", "") or "").strip(),
            )
        except Exception:
            return ("__bad__", id(d))

    def _load_sell_records_from_disk(self):
        path = get_realized_pnl_records_file_path()
        if not os.path.exists(path):
            return []
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, list):
                return []
            # 정규화 가능한 항목만 유지
            out = []
            for raw in data:
                if not isinstance(raw, dict):
                    continue
                try:
                    rec = SellRecord.from_json(raw)
                    out.append(rec.to_json())
                except Exception:
                    continue
            # 중복 제거
            uniq = {}
            for r in out:
                uniq[self._sell_record_dedupe_key(r)] = r
            return list(uniq.values())
        except Exception:
            return []

    def _save_sell_records_to_disk(self):
        path = get_realized_pnl_records_file_path()
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.sell_records, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _merge_and_persist_sell_records(self, incoming_list):
        existing = list(self.sell_records or [])
        merged = []
        for raw in existing:
            if isinstance(raw, dict):
                merged.append(raw)
        for raw in incoming_list:
            if not isinstance(raw, dict):
                continue
            try:
                merged.append(SellRecord.from_json(raw).to_json())
            except Exception:
                continue
        uniq = {}
        for r in merged:
            uniq[self._sell_record_dedupe_key(r)] = r
        self.sell_records = list(uniq.values())
        self._save_sell_records_to_disk()

    def _portfolio_choices_for_account(self, account: str):
        account = str(account or "").strip() or "일반 계좌"
        rows = []
        for item in self.portfolio:
            acc = str(item.get("account", "")).strip() or "일반 계좌"
            if acc != account:
                continue
            ticker = str(item.get("ticker", "")).strip()
            if not ticker or ticker.upper() == "FIXED":
                continue
            name = str(item.get("name", "")).strip()
            qty = float(item.get("qty", 0) or 0)
            rows.append((ticker, name, qty))
        rows.sort(key=lambda x: (x[1], x[0]))
        return rows

    def open_realized_pnl_report(self):
        """
        기간별(일/주/월/년) 실현손익 요약을 보여준다.
        매도 입력은 메인 화면의 '매도 입력창'에서 처리한다.
        """
        win = tk.Toplevel(self.root)
        win.title("🧾 실현손익 리포트")
        win.geometry("720x680")
        win.configure(bg=self.BG)
        self.bind_escape_to_close(win)
        try:
            win.attributes('-alpha', self.current_alpha)
            win.after(100, lambda: win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass

        top = self._build_card_frame(win)
        top.pack(fill="x", padx=12, pady=(12, 8))
        top.columnconfigure(1, weight=1)
        top.columnconfigure(3, weight=1)

        tk.Label(top, text="계좌", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=0, column=0, sticky="w")
        ent_acc = ttk.Combobox(
            top,
            font=self.FONT_MAIN,
            state="readonly",
            values=list(self.ent_account["values"]),
            style="Modern.TCombobox",
        )
        ent_acc.grid(row=0, column=1, padx=(8, 10), pady=4, sticky="ew")
        ent_acc.set(str(self.ent_account.get()).strip() or "일반 계좌")

        tk.Label(top, text="매도일", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=0, column=2, sticky="w")
        ent_date = self._make_entry(top, width=12)
        ent_date.grid(row=0, column=3, padx=(8, 0), pady=4, sticky="w")
        ent_date.insert(0, datetime.date.today().strftime("%Y-%m-%d"))

        tk.Label(top, text="종목", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=1, column=0, sticky="w")
        ent_ticker = ttk.Combobox(top, font=self.FONT_MAIN, state="readonly", values=[], style="Modern.TCombobox")
        ent_ticker.grid(row=1, column=1, padx=(8, 10), pady=4, sticky="ew")

        tk.Label(top, text="매도수량", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=1, column=2, sticky="w")
        ent_qty = self._make_entry(top, width=12)
        ent_qty.grid(row=1, column=3, padx=(8, 0), pady=4, sticky="w")

        tk.Label(top, text="매도가", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=2, column=0, sticky="w")
        ent_price = self._make_entry(top, width=18)
        ent_price.grid(row=2, column=1, padx=(8, 10), pady=4, sticky="w")

        tk.Label(top, text="매도환율(해외)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=2, column=2, sticky="w")
        ent_sell_ex = self._make_entry(top, width=12)
        ent_sell_ex.grid(row=2, column=3, padx=(8, 0), pady=4, sticky="w")
        try:
            ent_sell_ex.insert(0, f"{self.get_exchange_rate():.2f}")
        except Exception:
            ent_sell_ex.insert(0, "1400")

        tk.Label(top, text="수수료(원)", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=3, column=0, sticky="w")
        ent_fee = self._make_entry(top, width=18)
        ent_fee.grid(row=3, column=1, padx=(8, 10), pady=4, sticky="w")
        ent_fee.insert(0, "0")

        tk.Label(top, text="메모", bg=self.CARD_BG, fg=self.FG, font=self.FONT_MAIN).grid(row=3, column=2, sticky="w")
        ent_memo = self._make_entry(top)
        ent_memo.grid(row=3, column=3, padx=(8, 0), pady=4, sticky="ew")

        mid = tk.Frame(win, bg=self.BG)
        mid.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        mid.columnconfigure(0, weight=1)

        txt = tk.Text(mid, bg=self.ENTRY_BG, fg=self.FG, font=(self.FONT_MAIN[0], 10), wrap=tk.WORD, padx=12, pady=10)
        txt.grid(row=0, column=0, sticky="nsew")
        sb = tk.Scrollbar(mid, command=txt.yview)
        sb.grid(row=0, column=1, sticky="ns")
        txt.configure(yscrollcommand=sb.set)

        self._setup_text_tags(txt, title_size=14, title_color=self.ACCENT, body_size=11)

        def refresh_ticker_choices(*_args):
            acc = str(ent_acc.get()).strip() or "일반 계좌"
            choices = self._portfolio_choices_for_account(acc)
            ent_ticker["values"] = [f"{t} | {n} | 보유 {q:g}" for (t, n, q) in choices]
            if choices:
                ent_ticker.set(ent_ticker["values"][0])
            else:
                ent_ticker.set("")

        def build_report_text():
            records: List[SellRecord] = []
            for raw in (self.sell_records or []):
                try:
                    records.append(SellRecord.from_json(raw))
                except Exception:
                    continue
            lines = []
            lines.append("🧾 실현손익 리포트\n")
            lines.append("=" * 62 + "\n")
            lines.append(f"기록 건수: {len(records)}\n\n")

            if not records:
                lines.append("아직 매도 기록이 없습니다.\n상단에서 종목을 선택하고 매도 기록을 추가하세요.\n")
                return "".join(lines)

            def _fmt_sum_table(title, period_key):
                lines.append(f"[ {title} ]\n")
                sums = summarize_realized_pnl(records, self.portfolio, period_key)
                if not sums:
                    lines.append("  (기록 없음)\n\n")
                    return
                for k, s in sums:
                    pnl = s.get("pnl_krw", 0.0)
                    sign = "+" if pnl > 0 else ""
                    lines.append(
                        f"  - {k}: 손익 {sign}{int(round(pnl)):,}원"
                        f" | 매도 {int(round(s.get('proceeds_krw', 0.0))):,}원"
                        f" | 원가 {int(round(s.get('cost_krw', 0.0))):,}원"
                        f" | 수수료 {int(round(s.get('fee_krw', 0.0))):,}원\n"
                    )
                lines.append("\n")

            _fmt_sum_table("일간", "일간")
            _fmt_sum_table("주간", "주간")
            _fmt_sum_table("월간", "월간")
            _fmt_sum_table("연간", "연간")

            lines.append("=" * 62 + "\n")
            lines.append("[ 매도 기록 ]\n")
            for r in sorted(records, key=lambda x: x.sell_date):
                kind = "해외" if r.is_us else "국내"
                ex = f", 매도환율 {r.sell_exchange_rate:,.2f}" if r.is_us and r.sell_exchange_rate else ""
                fee = f", 수수료 {int(round(r.fee_krw)):,}원" if r.fee_krw else ""
                memo = f" ({r.memo})" if r.memo else ""
                lines.append(
                    f"  - {r.sell_date} | [{r.account}] {r.name} ({r.ticker})"
                    f" | {kind} | 수량 {r.qty:g} | 매도가 {r.sell_price:g}{('$' if r.is_us else '원')}{ex}{fee}{memo}\n"
                )
            return "".join(lines)

        def refresh_report_view():
            txt.config(state="normal")
            txt.delete("1.0", tk.END)
            txt.insert(tk.END, build_report_text())
            txt.config(state="disabled")

        def parse_selected_ticker():
            raw = str(ent_ticker.get() or "").strip()
            if not raw:
                return None
            # Format: "TICKER | NAME | 보유 Q"
            t = raw.split("|", 1)[0].strip()
            return t

        def find_holding(account, ticker):
            for item in self.portfolio:
                acc = str(item.get("account", "")).strip() or "일반 계좌"
                t = str(item.get("ticker", "")).strip().upper()
                if acc == account and t == ticker:
                    return item
            return None

        def on_add_sell():
            try:
                account = str(ent_acc.get()).strip() or "일반 계좌"
                ticker = parse_selected_ticker()
                if not ticker:
                    messagebox.showwarning("입력 오류", "매도할 종목을 선택하세요.")
                    return
                ticker = str(ticker).strip().upper()
                holding = find_holding(account, ticker)
                if not holding:
                    messagebox.showwarning("대상 없음", "해당 계좌/종목 보유 내역을 찾지 못했습니다.")
                    return
                name = str(holding.get("name", "")).strip() or ticker
                is_us = not is_korean_ticker(ticker)

                rec = SellRecord(
                    sell_date=str(ent_date.get()).strip(),
                    account=account,
                    ticker=ticker,
                    name=name,
                    qty=float(str(ent_qty.get()).strip().replace(",", "")),
                    sell_price=float(str(ent_price.get()).strip().replace(",", "")),
                    is_us=is_us,
                    sell_exchange_rate=(float(str(ent_sell_ex.get()).strip().replace(",", "")) if is_us else None),
                    fee_krw=float(str(ent_fee.get()).strip().replace(",", "") or "0"),
                    memo=str(ent_memo.get()).strip(),
                ).normalized()

                old_qty = float(holding.get("qty", 0) or 0)
                if rec.qty > old_qty + 1e-12:
                    messagebox.showwarning("수량 오류", f"매도 수량이 보유 수량을 초과합니다.\n보유: {old_qty:g} / 매도: {rec.qty:g}")
                    return

                self.sell_records.append(rec.to_json())
                self._merge_and_persist_sell_records([])  # dedupe + persist
                self.portfolio = apply_sell_to_portfolio(self.portfolio, rec)
                self.listbox.insert(tk.END, f"[매도기록] [{account}] {name} ({ticker}) | {rec.qty:g}주")
                self.refresh_account_options(preferred_account=account)
                refresh_ticker_choices()
                refresh_report_view()
            except Exception as e:
                messagebox.showerror("실현손익 기록 실패", f"매도 기록 추가 중 오류가 발생했습니다.\n\n{e}")

        ent_acc.bind("<<ComboboxSelected>>", refresh_ticker_choices)
        refresh_ticker_choices()

        btn_row = tk.Frame(win, bg=self.BG)
        btn_row.pack(fill="x", padx=12, pady=(0, 12))
        self._make_button(btn_row, "🔄 리포트 새로고침", refresh_report_view, bg="#2E8B57", fg="white", bold=True, pad=(12, 7)).pack(side="left")
        tk.Label(
            btn_row,
            text="매도 반영은 메인 화면의 '매도 입력창'을 이용하세요.",
            bg=self.BG,
            fg=self.MUTED,
            font=self.FONT_CAPTION,
        ).pack(side="left", padx=(10, 0))

        refresh_report_view()

    def get_exchange_rate(self):
        try:
            return float(yf.Ticker("KRW=X").history(period="1d")['Close'].iloc[-1])
        except Exception:
            return 1400.0

    def get_kr_price(self, code):
        try:
            res = requests.get(
                f"https://finance.naver.com/item/main.naver?code={code}",
                headers={'User-Agent': 'Mozilla/5.0'},
                timeout=5,
            )
            price_tag = BeautifulSoup(res.text, 'html.parser').select_one('.no_today .blind')
            if price_tag:
                return float(price_tag.text.replace(',', ''))
        except Exception:
            pass
        return 0.0

    def get_krx_gold_price_krw_per_g(self, reuters_code="M04020000", category="metals"):
        """
        네이버증권 모바일 내부 API(front-api)로 KRX 금(국내 금) 가격(원/g)을 가져온다.
        - reutersCode: 기본 M04020000 (국내 금)
        - category: 기본 metals
        """
        try:
            url = "https://m.stock.naver.com/front-api/marketIndex/productDetail"
            params = {"category": category, "reutersCode": reuters_code}
            res = requests.get(url, params=params, headers={"User-Agent": "Mozilla/5.0", "Accept": "application/json"}, timeout=5)
            data = res.json()
            if not isinstance(data, dict) or not data.get("isSuccess"):
                return 0.0
            result = data.get("result") or {}
            close_price = str(result.get("closePrice", "")).replace(",", "").strip()
            if not close_price:
                return 0.0
            return float(close_price)
        except Exception:
            return 0.0

    def _us_latest_price_from_yahoo_info(self, info):
        """
        Yahoo Finance API 기준 '가장 최근 시각' 호가: 정규·프리·애프터 구분 없이
        regularMarketTime / preMarketTime / postMarketTime 중 가장 늦은 타임스탬프의 가격을 쓴다.
        (fast_info.last_price 는 연장 구간을 반영하지 않는 경우가 많음)
        """
        if not isinstance(info, dict) or not info:
            return None

        def fp(x):
            if x is None:
                return None
            try:
                v = float(x)
                return v if v > 0 else None
            except (TypeError, ValueError):
                return None

        def ti(x):
            if x is None:
                return None
            try:
                return int(x)
            except (TypeError, ValueError):
                return None

        reg = fp(info.get("regularMarketPrice") or info.get("currentPrice"))
        pre = fp(info.get("preMarketPrice"))
        post = fp(info.get("postMarketPrice"))

        pairs = []
        rt = ti(info.get("regularMarketTime"))
        if reg is not None and rt is not None:
            pairs.append((rt, reg))
        pt = ti(info.get("preMarketTime"))
        if pre is not None and pt is not None:
            pairs.append((pt, pre))
        pot = ti(info.get("postMarketTime"))
        if post is not None and pot is not None:
            pairs.append((pot, post))
        if pairs:
            return max(pairs, key=lambda z: z[0])[1]
        for p in (post, pre, reg):
            if p is not None:
                return p
        return None

    def get_us_price(self, ticker):
        try:
            t = yf.Ticker(ticker)
            picked = self._us_latest_price_from_yahoo_info(t.info)
            if picked is not None and picked > 0:
                return float(picked)
            # info 실패 시에도 프리/애프터 포함한 최신 봉을 쓴다.
            hist = t.history(period="2d", interval="5m", prepost=True, auto_adjust=True)
            if hist is not None and not hist.empty:
                last = float(hist["Close"].iloc[-1])
                if last > 0:
                    return last
            hist_d = t.history(period="5d", interval="1d", prepost=False, auto_adjust=True)
            if hist_d is not None and not hist_d.empty:
                last_d = float(hist_d["Close"].iloc[-1])
                if last_d > 0:
                    return last_d
            return float(t.fast_info["last_price"])
        except Exception:
            return 0.0

    def update_rebalance_config_from_gui(self):
        try:
            self.target_ratios["주식"] = float(self.ent_ratio_stock.get().strip() or "0")
            self.target_ratios["채권"] = float(self.ent_ratio_bond.get().strip() or "0")
            self.target_ratios["금"] = float(self.ent_ratio_gold.get().strip() or "0")
            self.target_ratios["원자재"] = float(self.ent_ratio_comm.get().strip() or "0")
            self.target_ratios["현금성 자산"] = float(self.ent_ratio_cash.get().strip() or "0")
        except ValueError:
            messagebox.showwarning("입력 오류", "리밸런싱 비중은 숫자로 입력해주세요.")
            raise

    def _load_target_ratios_from_json(self, data):
        def _to_float(value):
            try:
                return float(value)
            except (TypeError, ValueError):
                return None

        alias_map = {
            "주식": ["주식", "stock", "stocks", "equity", "equities", "ratio_stock", "stock_ratio"],
            "채권": ["채권", "bond", "bonds", "fixed_income", "ratio_bond", "bond_ratio"],
            "금": ["금", "gold", "ratio_gold", "gold_ratio"],
            "원자재": ["원자재", "commodity", "commodities", "ratio_commodity", "commodity_ratio"],
            "현금성 자산": ["현금성 자산", "현금", "cash", "cash_equivalent", "cash_equivalents", "ratio_cash", "cash_ratio"],
        }

        sources = []
        if isinstance(data, dict):
            sources.append(data)
            for key in ["target_ratios", "rebalance_ratios", "rebalance_ratio"]:
                v = data.get(key)
                if isinstance(v, dict):
                    sources.append(v)

        loaded = {}
        for category, aliases in alias_map.items():
            for source in sources:
                found = False
                for alias in aliases:
                    if alias in source:
                        ratio_val = _to_float(source.get(alias))
                        if ratio_val is not None:
                            loaded[category] = ratio_val
                            found = True
                            break
                if found:
                    break
        return loaded

    def sync_rebalance_entries_from_config(self):
        self.ent_ratio_stock.delete(0, tk.END)
        self.ent_ratio_stock.insert(0, str(self.target_ratios.get("주식", 0)))
        self.ent_ratio_bond.delete(0, tk.END)
        self.ent_ratio_bond.insert(0, str(self.target_ratios.get("채권", 0)))
        self.ent_ratio_gold.delete(0, tk.END)
        self.ent_ratio_gold.insert(0, str(self.target_ratios.get("금", 0)))
        self.ent_ratio_comm.delete(0, tk.END)
        self.ent_ratio_comm.insert(0, str(self.target_ratios.get("원자재", 0)))
        self.ent_ratio_cash.delete(0, tk.END)
        self.ent_ratio_cash.insert(0, str(self.target_ratios.get("현금성 자산", 0)))

    def validate_rebalance_ratio_sum(self):
        ratio_sum = sum(float(v) for v in self.target_ratios.values())
        if abs(ratio_sum - 100.0) > 1e-6:
            messagebox.showwarning(
                "리밸런싱 비중 오류",
                f"리밸런싱 비중 합계는 반드시 100이어야 합니다.\n현재 합계: {ratio_sum:.4f}",
            )
            return False
        return True

    def get_rebalance_guide(self, total_val, macro_alloc):
        ratio_sum = sum(v for v in self.target_ratios.values() if v > 0)
        if ratio_sum <= 0:
            return None, "리밸런싱 비중 합계가 0입니다. 비중을 다시 입력해주세요."
        if abs(ratio_sum - 100.0) > 1e-6:
            return None, f"리밸런싱 비중 합계는 100이어야 합니다. 현재 합계: {ratio_sum:.4f}"

        guides = []
        categories = ["주식", "채권", "금", "원자재", "현금성 자산"]
        for cat in categories:
            target_amount = total_val * (max(self.target_ratios.get(cat, 0), 0) / ratio_sum)
            current_amount = macro_alloc.get(cat, 0.0)
            diff = target_amount - current_amount
            action = "매수" if diff > 0 else ("매도" if diff < 0 else "유지")
            guides.append({"category": cat, "current": current_amount, "target": target_amount, "diff": diff, "action": action})

        return guides, None

    def _refresh_portfolio_history_path_label(self) -> None:
        if not hasattr(self, "lbl_portfolio_history_path"):
            return
        p = self.portfolio_history_path
        self.lbl_portfolio_history_path.config(text=p)

    def choose_portfolio_history_path(self) -> None:
        # 저장 대화상자(asksaveasfilename)는 기존 파일을 고를 때 덮어쓰기 확인이 뜬다.
        # 일별 히스토리는 기존 JSON을 지정하는 경우가 많으므로 열기 대화상자를 쓴다.
        initial_dir = os.path.dirname(os.path.abspath(self.portfolio_history_path))
        if not os.path.isdir(initial_dir):
            initial_dir = os.path.expanduser("~")
        path = filedialog.askopenfilename(
            parent=self.root,
            title="포트폴리오 히스토리 JSON 파일 선택",
            filetypes=[("JSON 파일", "*.json"), ("모든 파일", "*.*")],
            initialdir=initial_dir,
        )
        if not path:
            return
        self.portfolio_history_path = os.path.normpath(os.path.expanduser(path))
        try:
            save_portfolio_history_file_path(self.portfolio_history_path)
        except Exception as e:
            messagebox.showerror("설정 저장 실패", f"히스토리 경로 설정을 저장하지 못했습니다.\n{e}")
            return
        self._refresh_portfolio_history_path_label()

    def save_and_get_history(self, total_roi, total_prin, total_val, macro_alloc):
        filename = self.portfolio_history_path
        history = {}
        legacy_filename = "portfolio_history.json"
        default_store = get_history_file_path()

        if os.path.exists(filename):
            try:
                with open(filename, 'r', encoding='utf-8') as f:
                    history = json.load(f)
            except Exception:
                pass
        elif os.path.abspath(filename) == os.path.abspath(default_store) and os.path.exists(legacy_filename):
            # 기본 저장 경로이고 아직 없을 때만, 작업 디렉터리의 구버전 파일을 1회 마이그레이션
            try:
                with open(legacy_filename, 'r', encoding='utf-8') as f:
                    history = json.load(f)
            except Exception:
                history = {}

        alloc_record = {}
        for cat, val in macro_alloc.items():
            pct = round((val / total_val * 100), 2) if total_val > 0 else 0.0
            alloc_record[cat] = {"amount": round(val, 2), "percent": pct}

        today = datetime.date.today().strftime('%Y-%m-%d')
        history[today] = {"roi": total_roi, "principal": total_prin, "value": total_val, "allocation": alloc_record}

        try:
            parent = os.path.dirname(os.path.abspath(filename))
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(filename, 'w', encoding='utf-8') as f:
                json.dump(history, f, indent=4, ensure_ascii=False)
        except Exception:
            pass

        return dict(sorted(history.items()))

    def calculate_and_draw(self, in_place_refresh=False):
        try:
            if not self.portfolio and not self.account_cash:
                return
            self.update_rebalance_config_from_gui()
            if self.rebalance_enabled.get() and not self.validate_rebalance_ratio_sum():
                self.lbl_status.config(text="리밸런싱 비중 합계 오류 - 계산 중단", fg="#FF6B6B")
                return

            self.lbl_status.config(text="실시간 시세 및 수익률 계산 중...", fg="#FFFF00")
            self.root.update()

            exchange_rate = self.get_exchange_rate()
            asset_values = defaultdict(float)
            report_data = []

            macro_alloc = {"현금성 자산": 0.0, "주식": 0.0, "채권": 0.0, "금": 0.0, "원자재": 0.0}

            pure_cash_val = 0.0
            pure_cash_prin = 0.0
            for ent in self.account_cash:
                acc_name = str(ent.get("account", "")).strip() or "일반 계좌"
                ck = float(ent.get("cash_krw", 0) or 0)
                cu = float(ent.get("cash_usd", 0) or 0)
                usd_val_krw = cu * exchange_rate
                usd_cost_krw = float(ent.get("usd_cost_krw", 0) or 0)
                if cu > 0 and usd_cost_krw <= 0:
                    usd_cost_krw = usd_val_krw
                line_prin = ck + usd_cost_krw
                line_val = ck + usd_val_krw
                if line_val <= 0:
                    continue
                pure_cash_val += line_val
                pure_cash_prin += line_prin
                asset_values["현금 및 현금성 자산"] += line_val
                macro_alloc["현금성 자산"] += line_val
                parts = []
                if ck > 0:
                    parts.append(f"KRW {ck:,.0f}")
                if cu > 0:
                    parts.append(f"USD {cu:,.2f}")
                cash_label = "예수금 (" + " · ".join(parts) + ")" if parts else "예수금"
                report_data.append(
                    {
                        'name': cash_label,
                        'account': acc_name,
                        'is_pure_cash': True,
                        'is_usd_cash': cu > 0,
                        'cash_krw': ck,
                        'cash_usd': cu,
                        'cash_usd_val_krw': usd_val_krw,
                        'roi': ((line_val - line_prin) / line_prin * 100) if line_prin > 0 else 0.0,
                        'prof': line_val - line_prin,
                        'fx_prof': usd_val_krw - usd_cost_krw,
                        'val': line_val,
                        'prin': line_prin,
                    }
                )

            total_prin = pure_cash_prin
            total_val = pure_cash_val

            for item in self.portfolio:
                name = item.get('name', '알수없음')
                ticker = str(item.get('ticker', '')).strip()
                acc_name = item.get('account', '일반 계좌')  # 명시된 계좌명 사용

                # FIXED(실물/고정자산): prin/val 수동입력 대신 qty/avg_price 기반 자동 계산 지원
                if ticker.upper() == "FIXED":
                    qty = float(item.get("qty", 0) or 0)
                    avg_price = float(item.get("avg_price", 0) or 0)  # 1개당 매입단가(원)
                    p_krw = avg_price * qty
                    v_krw = float(item.get("val", 0) or 0)  # fallback (legacy)

                    # 연동 가격소스가 있으면 실시간 평가액을 재계산한다.
                    if str(item.get("price_source", "")).strip().lower() == "naver_marketindex":
                        cfg = item.get("naver_marketindex") or {}
                        reuters_code = str(cfg.get("reutersCode", "")).strip() or "M04020000"
                        category = str(cfg.get("category", "")).strip() or "metals"
                        unit_price = str(cfg.get("unit_price", "")).strip().upper() or "KRW_PER_G"
                        unit_weight_g = float(item.get("unit_weight_g", 1) or 1)
                        if qty > 0 and unit_weight_g > 0 and unit_price == "KRW_PER_G":
                            krw_per_g = self.get_krx_gold_price_krw_per_g(reuters_code=reuters_code, category=category)
                            if krw_per_g > 0:
                                v_krw = krw_per_g * unit_weight_g * qty
                    else:
                        if v_krw <= 0 and p_krw > 0:
                            v_krw = p_krw

                    roi = ((v_krw - p_krw) / p_krw * 100) if p_krw > 0 else 0
                    cur_unit = (v_krw / qty) if qty > 0 else 0.0
                    report_data.append(
                        {
                            'name': name,
                            'account': acc_name,
                            'is_fixed': True,
                            'qty': qty,
                            'cur_p': cur_unit,
                            'avg_p': avg_price,
                            'roi': roi,
                            'prof': v_krw - p_krw,
                            'val': v_krw,
                            'prin': p_krw,
                        }
                    )

                    cat = get_asset_category(name, "")
                    asset_values[name] += v_krw
                    macro_alloc[cat] += v_krw

                    total_prin += p_krw
                    total_val += v_krw
                    continue

                qty = float(item.get('qty', 0))
                avg_price = float(item.get('avg_price', 0))

                cat = get_asset_category(name, ticker)

                if is_korean_ticker(ticker):
                    cur_price = self.get_kr_price(ticker)
                    v_krw = cur_price * qty
                    p_krw = avg_price * qty
                    roi = ((cur_price - avg_price) / avg_price * 100) if avg_price > 0 else 0
                    report_data.append({'name': name, 'ticker': ticker, 'account': acc_name, 'is_us': False, 'qty': qty, 'roi': roi, 'prof': v_krw - p_krw, 'cur_p': cur_price, 'avg_p': avg_price, 'val': v_krw, 'prin': p_krw})
                else:
                    cur_price = self.get_us_price(ticker)
                    v_usd = cur_price * qty
                    p_usd = avg_price * qty
                    buy_ex = float(item.get('buy_exchange_rate', exchange_rate) or exchange_rate)
                    v_krw = v_usd * exchange_rate
                    p_krw = p_usd * buy_ex
                    roi = ((cur_price - avg_price) / avg_price * 100) if avg_price > 0 else 0
                    price_prof = (cur_price - avg_price) * qty * buy_ex
                    fx_prof = (exchange_rate - buy_ex) * v_usd
                    report_data.append(
                        {
                            'name': name,
                            'ticker': ticker,
                            'account': acc_name,
                            'is_us': True,
                            'qty': qty,
                            'roi': roi,
                            'prof': v_krw - p_krw,
                            'price_prof': price_prof,
                            'fx_prof': fx_prof,
                            'cur_p': cur_price,
                            'avg_p': avg_price,
                            'buy_exchange_rate': buy_ex,
                            'val': v_krw,
                            'prin': p_krw,
                        }
                    )

                macro_alloc[cat] += v_krw

                if cat == "현금성 자산":
                    asset_values["현금 및 현금성 자산"] += v_krw
                else:
                    asset_values[name] += v_krw

                total_prin += p_krw
                total_val += v_krw

            total_profit = total_val - total_prin
            total_roi = (total_profit / total_prin * 100) if total_prin > 0 else 0

            self.history_data = self.save_and_get_history(total_roi, total_prin, total_val, macro_alloc)

            self.current_asset_values = asset_values
            self.current_macro_alloc = macro_alloc
            self.current_total_val = total_val
            self.current_rebalance_guide = None
            self.current_rebalance_error = None
            if self.rebalance_enabled.get():
                self.current_rebalance_guide, self.current_rebalance_error = self.get_rebalance_guide(total_val, macro_alloc)

            self.current_report_data = report_data
            self.current_exchange_rate = exchange_rate

            self.lbl_status.config(text="계산 완료! 통합 수익률 확인", fg="#00FF00")
            if in_place_refresh and self.chart_win and self.chart_win.winfo_exists():
                self.refresh_chart_and_report(report_data, total_prin, total_val, total_profit, total_roi, exchange_rate)
            else:
                self.show_chart_and_report(report_data, total_prin, total_val, total_profit, total_roi, exchange_rate)

        except Exception:
            err_msg = traceback.format_exc()
            messagebox.showerror("데이터 수집 에러", f"시세를 불러오는 중 오류가 발생했습니다.\n\n{err_msg}")
            self.lbl_status.config(text="오류 발생 - 계산 중단", fg="#FF6B6B")

    def show_chart_and_report(self, report_data, total_prin, total_val, total_prof, total_roi, ex_rate):
        try:
            if self.chart_win and self.chart_win.winfo_exists():
                self._close_chart_window()

            self.chart_win = tk.Toplevel(self.root)
            self.chart_win.title("포트폴리오 수익률 보고서 및 추이")
            self.chart_win.configure(bg=self.BG)
            self.chart_win.protocol("WM_DELETE_WINDOW", self._close_chart_window)
            self.chart_win.bind("<Escape>", lambda event: self._close_chart_window())
            try:
                self.chart_win.attributes('-alpha', self.current_alpha)
                self.chart_win.after(100, lambda: self.chart_win.attributes('-alpha', self.current_alpha))
            except Exception:
                pass

            left_frame = tk.Frame(self.chart_win, bg=self.BG, width=550)
            left_frame.pack(side='left', fill='both', expand=True, padx=5, pady=5)
            right_frame = tk.Frame(self.chart_win, bg=self.CARD_BG)
            right_frame.pack(side='right', fill='both', expand=True, padx=10, pady=10)

            top_action_frame = tk.Frame(left_frame, bg=self.CARD_BG)
            top_action_frame.pack(side='top', fill='x', pady=(10, 5))

            self._make_button(top_action_frame, "🍩 종목별 비중", self.show_pie_popup, bg="#D4AF37", fg="black", bold=True).pack(
                side='left', expand=True, fill='x', padx=2
            )
            self._make_button(top_action_frame, "🍰 자산군 비중", self.show_macro_pie_popup, bg="#8C52FF", fg="white", bold=True).pack(
                side='left', expand=True, fill='x', padx=2
            )
            self._make_button(top_action_frame, "📈 투자자산 비중", self.show_investment_pie_popup, bg="#E84393", fg="white", bold=True).pack(
                side='left', expand=True, fill='x', padx=2
            )
            self._make_button(top_action_frame, "🏦 계좌별 수익률", self.show_account_yield_popup, bg="#FF914D", fg="black", bold=True).pack(
                side='left', expand=True, fill='x', padx=2
            )
            self._make_button(top_action_frame, "⚖ 리밸런싱 가이드", self.show_rebalance_popup, bg="#2E8B57", fg="white", bold=True).pack(
                side='left', expand=True, fill='x', padx=2
            )

            alloc_trend_frame = tk.Frame(left_frame, bg=self.CARD_BG)
            alloc_trend_frame.pack(side='top', fill='x', pady=(0, 5), padx=10)
            self._make_button(
                alloc_trend_frame,
                "📊 자산분배 추이",
                self.show_allocation_trend_menu,
                bg="#3D5A80",
                fg="white",
                bold=True,
            ).pack(side='left', fill='x', expand=True)

            btn_frame = tk.Frame(left_frame, bg=self.CARD_BG)
            btn_frame.pack(side='top', fill='x', pady=5, padx=10)
            self.btn_daily = self._make_button(btn_frame, "일간 수익률", lambda: self.update_line_chart("일간"), bg="#FFD700", fg="black", bold=True)
            self.btn_daily.pack(side='left', expand=True, fill='x', padx=2)
            self.btn_weekly = self._make_button(btn_frame, "주간 수익률", lambda: self.update_line_chart("주간"), bg="#3A5A7A", fg="white", bold=True)
            self.btn_weekly.pack(side='left', expand=True, fill='x', padx=2)
            self.btn_monthly = self._make_button(btn_frame, "월간 수익률", lambda: self.update_line_chart("월간"), bg="#3A5A7A", fg="white", bold=True)
            self.btn_monthly.pack(side='left', expand=True, fill='x', padx=2)
            self.btn_manual_refresh = self._make_button(
                btn_frame,
                "🔄 보고서 갱신",
                self.refresh_report_on_click,
                bg="#2E8B57",
                fg="white",
                bold=True
            )
            self.btn_manual_refresh.pack(side='left', expand=True, fill='x', padx=2)

            daily_scroll_frame = tk.Frame(left_frame, bg=self.CARD_BG)
            daily_scroll_frame.pack(side='top', fill='x', padx=10, pady=(0, 6))
            self.daily_window_label = tk.Label(
                daily_scroll_frame,
                text=f"일간 구간: 최근 {self.daily_window_size}일",
                bg=self.CARD_BG,
                fg=self.MUTED,
                font=self.FONT_CAPTION,
                anchor='w'
            )
            self.daily_window_label.pack(side='top', fill='x')
            self.daily_window_scale = tk.Scale(
                daily_scroll_frame,
                from_=0,
                to=0,
                orient='horizontal',
                resolution=1,
                showvalue=False,
                command=self._on_daily_window_scroll,
                bg=self.CARD_BG,
                fg=self.FG,
                troughcolor=self.ENTRY_BG,
                highlightthickness=0
            )
            self.daily_window_scale.pack(side='top', fill='x')
            self.daily_window_follow_latest = True

            line_frame = tk.Frame(left_frame, bg=self.BG)
            line_frame.pack(side='bottom', fill='both', expand=True)

            from matplotlib.figure import Figure
            self.fig_line = Figure(figsize=(5, 6.8))
            self.fig_line.patch.set_facecolor(self.BG)
            self.canvas_line = FigureCanvasTkAgg(self.fig_line, master=line_frame)
            self.canvas_line.get_tk_widget().pack(fill='both', expand=True)

            self.generate_report_text(right_frame, report_data, total_prin, total_val, total_prof, total_roi, ex_rate)
            self.chart_win.update_idletasks()
            self._resize_and_place_chart_win(self.chart_win, desired_w=1100, desired_h=650, reserve_bottom=130)
            self.update_line_chart("일간")
            self.chart_win.update_idletasks()
            self._resize_and_place_chart_win(self.chart_win, desired_w=1100, desired_h=650, reserve_bottom=130)

        except Exception:
            err_msg = traceback.format_exc()
            messagebox.showerror("차트 UI 에러", f"보고서 화면을 띄우는 중 오류가 발생했습니다:\n\n{err_msg}")

    def refresh_chart_and_report(self, report_data, total_prin, total_val, total_prof, total_roi, ex_rate):
        if not (self.chart_win and self.chart_win.winfo_exists()):
            return
        if self.report_text_widget and self.report_text_widget.winfo_exists():
            self._fill_report_text(self.report_text_widget, report_data, total_prin, total_val, total_prof, total_roi, ex_rate)
        self.update_line_chart(getattr(self, "current_chart_view_mode", "일간"))

    def show_account_yield_popup(self):
        if not hasattr(self, 'current_report_data'):
            return

        acc_win = tk.Toplevel(self.root)
        acc_win.title("계좌별 수익률 요약")
        acc_win.geometry("500x600")
        acc_win.configure(bg=self.BG)
        self.bind_escape_to_close(acc_win)
        try:
            acc_win.attributes('-alpha', self.current_alpha)
            acc_win.after(100, lambda: acc_win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass

        scrollbar = tk.Scrollbar(acc_win)
        scrollbar.pack(side='right', fill='y')
        txt = tk.Text(acc_win, bg=self.ENTRY_BG, fg=self.FG, font=(self.FONT_MAIN[0], 11), yscrollcommand=scrollbar.set)
        txt.pack(side='left', fill='both', expand=True, padx=10, pady=10)
        scrollbar.config(command=txt.yview)

        self._setup_text_tags(txt, title_size=14, title_color=self.ACCENT, body_size=11)

        txt.insert(tk.END, "🏦 계좌별 수익률 요약\n", "title")
        txt.insert(tk.END, "=" * 40 + "\n\n")

        account_groups = defaultdict(list)
        for d in self.current_report_data:
            acc = d.get('account', '일반 계좌')
            account_groups[acc].append(d)

        for acc_name, items in account_groups.items():
            acc_prin = sum(i.get('prin', 0) for i in items)
            acc_val = sum(i.get('val', 0) for i in items)
            acc_prof = acc_val - acc_prin
            acc_roi = (acc_prof / acc_prin * 100) if acc_prin > 0 else 0

            sec_items = [i for i in items if not i.get('is_pure_cash')]
            cash_items = [i for i in items if i.get('is_pure_cash')]
            sec_prin = sum(i.get('prin', 0) for i in sec_items)
            cash_prin = sum(i.get('prin', 0) for i in cash_items)

            acc_tag = "up" if acc_roi > 0 else ("down" if acc_roi < 0 else "flat")
            acc_sign = "+" if acc_roi > 0 else ""

            txt.insert(tk.END, f"▶ [{acc_name}]\n", "acc_title")
            txt.insert(tk.END, f"  총 평가금: {int(acc_val):,}원\n")
            if cash_items:
                txt.insert(tk.END, f"  종목 매수(원가): {int(sec_prin):,}원  ·  예수금 원가: {int(cash_prin):,}원\n")
                txt.insert(tk.END, f"  계좌 수익률 (종목+예수금 총원가 대비): ")
            else:
                txt.insert(tk.END, f"  매수(원가): {int(acc_prin):,}원\n")
                txt.insert(tk.END, f"  계좌 수익률: ")
            txt.insert(tk.END, f"{acc_sign}{acc_roi:.2f}% ({acc_sign}{int(acc_prof):,}원)\n", acc_tag)
            txt.insert(tk.END, "-" * 40 + "\n")

            for d in items:
                item_tag = "up" if d['roi'] > 0 else ("down" if d['roi'] < 0 else "flat")
                item_sign = "+" if d['roi'] > 0 else ""
                if d.get('is_pure_cash'):
                    txt.insert(tk.END, f"  • {d['name']} : 평가 {int(d['val']):,}원 / 원가 {int(d['prin']):,}원 ")
                else:
                    txt.insert(tk.END, f"  • {d['name']} : 평가 {int(d['val']):,}원 / 매수 {int(d['prin']):,}원 ")
                txt.insert(tk.END, f"({item_sign}{d['roi']:.2f}%)\n", item_tag)

            txt.insert(tk.END, "\n")

        txt.config(state='disabled')

    def _ordered_allocation_categories(self) -> list:
        """히스토리에 등장한 자산군 키를 UI 일관된 순서로 정렬."""
        preferred = ("주식", "채권", "금", "원자재", "현금성 자산")
        hist = getattr(self, "history_data", None) or {}
        found: set = set()
        for rec in hist.values():
            a = (rec or {}).get("allocation")
            if isinstance(a, dict):
                found.update(a.keys())
        return [c for c in preferred if c in found] + sorted(c for c in found if c not in preferred)

    def _allocation_history_dataframe(self):
        """
        history_data로부터 날짜 인덱스·자산군별 금액/비중 컬럼 DataFrame.
        allocation이 없는 날짜/자산은 NaN.
        """
        categories = self._ordered_allocation_categories()
        hist = getattr(self, "history_data", None) or {}
        if not hist:
            return None, []
        if not categories:
            return None, []
        rows = []
        idx = []
        for d in sorted(hist.keys()):
            rec = hist[d] or {}
            alloc = rec.get("allocation")
            if not isinstance(alloc, dict):
                alloc = {}
            idx.append(pd.Timestamp(d))
            r = {}
            for cat in categories:
                c = alloc.get(cat)
                if isinstance(c, dict):
                    r[f"__amt__{cat}"] = c.get("amount", float("nan"))
                    r[f"__pct__{cat}"] = c.get("percent", float("nan"))
                else:
                    r[f"__amt__{cat}"] = float("nan")
                    r[f"__pct__{cat}"] = float("nan")
            rows.append(r)
        df = pd.DataFrame(rows, index=pd.DatetimeIndex(idx))
        df = df.sort_index()
        return df, categories

    def _aggregate_allocation_dataframe(self, df: pd.DataFrame, view_mode: str) -> pd.DataFrame:
        """update_line_chart와 유사: 영업일만 사용 후 주/월/분기 말(마지막 기록) 집계."""
        if df is None or df.empty:
            return df
        out = df.copy()
        if not out.empty:
            _hset = _kr_holiday_date_set(out.index.min(), out.index.max())
            out = out.loc[out.index.map(lambda t: _is_kr_business_day(t, _hset))]
        if out.empty:
            return out
        if view_mode == "주간":
            out = out.groupby(out.index.to_period("W-FRI")).last()
            out.index = out.index.to_timestamp()
        elif view_mode == "월간":
            out = out.groupby(out.index.to_period("M")).last()
            out.index = out.index.to_timestamp()
        elif view_mode == "분기":
            out = out.groupby(out.index.to_period("Q")).last()
            out.index = out.index.to_timestamp()
        return out

    def show_allocation_trend_menu(self) -> None:
        if not (self.chart_win and self.chart_win.winfo_exists()):
            return
        hist = getattr(self, "history_data", None) or {}
        if not hist:
            messagebox.showinfo("자산분배 추이", "히스토리가 없습니다. 먼저 '계산 및 차트/수익률 보기'를 실행하세요.", parent=self.chart_win)
            return
        has_alloc = False
        for rec in hist.values():
            a = (rec or {}).get("allocation")
            if isinstance(a, dict) and a:
                has_alloc = True
                break
        if not has_alloc:
            messagebox.showinfo(
                "자산분배 추이",
                "저장된 히스토리에 자산군(allocation) 항목이 없습니다. 최신 앱으로 기록이 쌓인 뒤 다시 시도하세요.",
                parent=self.chart_win,
            )
            return
        menu = tk.Toplevel(self.chart_win)
        menu.title("자산분배 추이")
        menu.configure(bg=self.CARD_BG)
        self.bind_escape_to_close(menu)
        try:
            menu.attributes("-alpha", self.current_alpha)
            menu.after(100, lambda: menu.attributes("-alpha", self.current_alpha))
        except Exception:
            pass
        tk.Label(
            menu,
            text="보기 모드를 선택하세요. 각 버튼은 새 창에 표로 열립니다.",
            bg=self.CARD_BG,
            fg=self.FG,
            font=self.FONT_MAIN,
            wraplength=400,
        ).pack(pady=(12, 8), padx=14)
        btn_fr = tk.Frame(menu, bg=self.CARD_BG)
        btn_fr.pack(fill="x", padx=14, pady=(0, 14))
        modes = [
            ("일별 자산군", "일간"),
            ("주별 자산군", "주간"),
            ("월별 자산군", "월간"),
            ("분기별 자산군", "분기"),
        ]
        for label, key in modes:
            self._make_button(
                btn_fr,
                label,
                lambda k=key: self.show_allocation_table_popup(k),
                bg=self.BTN_BG,
                fg=self.FG,
                bold=True,
            ).pack(fill="x", pady=3)
        menu.update_idletasks()
        w = max(menu.winfo_reqwidth(), 360)
        h = menu.winfo_reqheight()
        self._resize_and_place_chart_win(menu, desired_w=int(w) + 40, desired_h=int(h) + 40, reserve_bottom=0)

    def _format_alloc_pct_with_amount(self, pct, amt) -> str:
        """한 셀에 '비중% (금액원)' 형식. 누락은 —."""
        ptxt = "—"
        atxt = "—"
        try:
            if pct is not None and not pd.isna(pct):
                ptxt = f"{float(pct):.2f}%"
        except (TypeError, ValueError):
            pass
        try:
            if amt is not None and not pd.isna(amt):
                atxt = f"{int(round(float(amt))):,}원"
        except (TypeError, ValueError):
            pass
        if ptxt == "—" and atxt == "—":
            return "—"
        return f"{ptxt} ({atxt})"

    def show_allocation_table_popup(self, view_mode: str) -> None:
        """view_mode: 일간 | 주간 | 월간 | 분기 — 자산군 amount·percent 표."""
        if not (self.chart_win and self.chart_win.winfo_exists()):
            return
        df, categories = self._allocation_history_dataframe()
        if df is None or not categories:
            messagebox.showinfo("자산분배 표", "표시할 allocation 데이터가 없습니다.", parent=self.chart_win)
            return
        df = self._aggregate_allocation_dataframe(df, view_mode)
        if df is None or df.empty:
            messagebox.showinfo("자산분배 표", "집계 결과가 없습니다(영업일·기록 범위를 확인하세요).", parent=self.chart_win)
            return
        titles = {
            "일간": "일별 자산군 · 비중% (금액)",
            "주간": "주별 자산군 · 비중% (금액)",
            "월간": "월별 자산군 · 비중% (금액)",
            "분기": "분기별 자산군 · 비중% (금액)",
        }
        win = tk.Toplevel(self.chart_win)
        win.title(titles.get(view_mode, "자산군"))
        win.configure(bg=self.BG)
        self.bind_escape_to_close(win)
        try:
            win.attributes("-alpha", self.current_alpha)
            win.after(100, lambda: win.attributes("-alpha", self.current_alpha))
        except Exception:
            pass
        # 컬럼: 날짜 + 자산별 한 열(비중% (금액))
        col_ids = ["c_date"]
        for c in categories:
            col_ids.append(f"alloc__{c}")
        st = ttk.Style()
        try:
            st.theme_use("clam")
        except Exception:
            pass
        st.configure(
            "AllocTable.Treeview",
            background=self.ENTRY_BG,
            fieldbackground=self.ENTRY_BG,
            foreground=self.FG,
            bordercolor=self.BORDER,
        )
        st.configure("AllocTable.Treeview.Heading", background=self.BTN_BG, foreground=self.FG, relief="flat")
        st.map("AllocTable.Treeview.Heading", background=[("active", self.BTN_BG)])
        outer = tk.Frame(win, bg=self.BG, padx=8, pady=8)
        outer.pack(fill="both", expand=True)
        yscroll = ttk.Scrollbar(outer, orient="vertical")
        yscroll.pack(side="right", fill="y")
        xscroll = ttk.Scrollbar(outer, orient="horizontal")
        xscroll.pack(side="bottom", fill="x")
        tree = ttk.Treeview(
            outer,
            columns=col_ids,
            show="headings",
            yscrollcommand=yscroll.set,
            xscrollcommand=xscroll.set,
            style="AllocTable.Treeview",
            height=24,
        )
        tree.pack(side="left", fill="both", expand=True)
        yscroll.config(command=tree.yview)
        xscroll.config(command=tree.xview)
        w_date = 200
        w_combined = 200
        tree.column("c_date", width=w_date, minwidth=120, stretch=False, anchor="center")
        tree.heading("c_date", text="날짜(기간 말)")
        for c in categories:
            cid = f"alloc__{c}"
            tree.column(cid, width=w_combined, minwidth=140, stretch=False, anchor="e")
            tree.heading(cid, text=c)
        for i, ts in enumerate(df.index):
            dstr = _date_with_weekday_kr(ts)
            vals = [dstr]
            row = df.iloc[i]
            for cat in categories:
                av = row.get(f"__amt__{cat}", float("nan"))
                pv = row.get(f"__pct__{cat}", float("nan"))
                vals.append(self._format_alloc_pct_with_amount(pv, av))
            tree.insert("", "end", values=vals)
        win.minsize(600, 400)
        win.geometry("1000x520")
        win.update_idletasks()
        # chart 근처에 배치
        self._resize_and_place_chart_win(win, desired_w=1000, desired_h=520, reserve_bottom=0)

    def show_pie_popup(self):
        pie_win = tk.Toplevel(self.root)
        pie_win.title("개별 종목 원형 차트")
        pie_win.geometry("550x550")
        pie_win.configure(bg=self.BG)
        self.bind_escape_to_close(pie_win)
        try:
            pie_win.attributes('-alpha', self.current_alpha)
            pie_win.after(100, lambda: pie_win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass

        from matplotlib.figure import Figure
        fig_pie = Figure(figsize=(5, 5))
        fig_pie.patch.set_facecolor(self.BG)
        ax_pie = fig_pie.add_subplot(111)
        ax_pie.set_facecolor(self.BG)

        labels, sizes = [], []
        for name, value in sorted(self.current_asset_values.items(), key=lambda x: x[1], reverse=True):
            if value > 0:
                labels.append(name)
                sizes.append(value)

        total = sum(sizes)
        display_labels = []
        for i, s in enumerate(sizes):
            pct = s / total * 100
            display_labels.append(labels[i] if pct >= 5 else "")

        wedges, texts, autotexts = ax_pie.pie(
            sizes,
            labels=display_labels,
            autopct=lambda p: f'{p:.1f}%' if p >= 5 else '',
            startangle=90,
            wedgeprops={'edgecolor': 'black', 'linewidth': 1},
        )
        for t in texts + autotexts:
            t.set_color('white')
            t.set_fontsize(9)

        ax_pie.set_title("개별 종목별 비중 (호버: 요약 · 클릭: 구성)", color="white", fontsize=13, fontweight='bold', pad=15)

        canvas_pie = FigureCanvasTkAgg(fig_pie, master=pie_win)
        canvas_pie.draw()
        canvas_pie.get_tk_widget().pack(fill='both', expand=True, padx=10, pady=10)

        def on_stock_wedge_click(i):
            body = self._format_stock_pie_slice_breakdown(labels[i], sizes[i])
            self._show_pie_detail_popup(pie_win, f"{labels[i]} — 구성", body)

        self._setup_pie_hover(canvas_pie, fig_pie, ax_pie, wedges, labels, sizes, parent_win=pie_win, on_wedge_click=on_stock_wedge_click)

    def show_macro_pie_popup(self):
        pie_win = tk.Toplevel(self.root)
        pie_win.title("자산군별 포트폴리오 비중")
        pie_win.geometry("500x500")
        pie_win.configure(bg=self.BG)
        self.bind_escape_to_close(pie_win)
        try:
            pie_win.attributes('-alpha', self.current_alpha)
            pie_win.after(100, lambda: pie_win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass

        from matplotlib.figure import Figure
        fig_pie = Figure(figsize=(5, 5))
        fig_pie.patch.set_facecolor(self.BG)
        ax_pie = fig_pie.add_subplot(111)
        ax_pie.set_facecolor(self.BG)

        labels, sizes, colors = [], [], []
        color_map = {
            "주식": "#FF6B6B",
            "채권": "#4D96FF",
            "현금성 자산": "#4CAF50",
            "금": "#FFD700",
            "원자재": "#B08D57",
        }

        for name, value in sorted(self.current_macro_alloc.items(), key=lambda x: x[1], reverse=True):
            if value > 0:
                labels.append(name)
                sizes.append(value)
                colors.append(color_map.get(name, "#FFFFFF"))

        wedges, texts, autotexts = ax_pie.pie(
            sizes,
            labels=labels,
            colors=colors,
            autopct='%1.1f%%',
            startangle=90,
            wedgeprops={'edgecolor': 'black', 'linewidth': 1.5},
        )
        for t in texts + autotexts:
            t.set_color('white')
            t.set_fontsize(11)
            t.set_fontweight('bold')

        ax_pie.set_title("안전/위험 자산 배분 현황 (호버: 요약 · 클릭: 종목 구성)", color="white", fontsize=14, fontweight='bold', pad=15)

        canvas_pie = FigureCanvasTkAgg(fig_pie, master=pie_win)
        canvas_pie.draw()
        canvas_pie.get_tk_widget().pack(fill='both', expand=True, padx=10, pady=10)

        def on_macro_wedge_click(i):
            body = self._format_macro_category_breakdown(labels[i])
            self._show_pie_detail_popup(pie_win, f"{labels[i]} — 포함 종목", body)

        self._setup_pie_hover(canvas_pie, fig_pie, ax_pie, wedges, labels, sizes, parent_win=pie_win, on_wedge_click=on_macro_wedge_click)

    def show_investment_pie_popup(self):
        pie_win = tk.Toplevel(self.root)
        pie_win.title("투자자산 비중 (현금 제외)")
        pie_win.geometry("500x500")
        pie_win.configure(bg=self.BG)
        self.bind_escape_to_close(pie_win)
        try:
            pie_win.attributes('-alpha', self.current_alpha)
            pie_win.after(100, lambda: pie_win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass

        from matplotlib.figure import Figure
        fig_pie = Figure(figsize=(5, 5))
        fig_pie.patch.set_facecolor(self.BG)
        ax_pie = fig_pie.add_subplot(111)
        ax_pie.set_facecolor(self.BG)

        labels, sizes, colors = [], [], []
        color_map = {"주식": "#FF6B6B", "채권": "#4D96FF", "금": "#FFD700", "원자재": "#B08D57"}

        invest_alloc = {k: v for k, v in self.current_macro_alloc.items() if k != "현금성 자산" and v > 0}

        if not invest_alloc:
            ax_pie.text(
                0.5,
                0.5,
                "현금성 자산 외 투자자산이 없습니다.",
                color="white",
                ha="center",
                va="center",
                transform=ax_pie.transAxes,
                fontsize=13,
            )
        else:
            for name, value in sorted(invest_alloc.items(), key=lambda x: x[1], reverse=True):
                labels.append(name)
                sizes.append(value)
                colors.append(color_map.get(name, "#FFFFFF"))

            invest_total = sum(sizes)

            def make_label(pct):
                val = int(round(pct / 100.0 * invest_total))
                return f"{pct:.1f}%\n({val:,}원)"

            wedges, texts, autotexts = ax_pie.pie(
                sizes,
                labels=labels,
                colors=colors,
                autopct='%1.1f%%',
                startangle=90,
                wedgeprops={'edgecolor': 'black', 'linewidth': 1.5},
            )
            for t in texts + autotexts:
                t.set_color('white')
                t.set_fontsize(10)
                t.set_fontweight('bold')

        ax_pie.set_title("투자자산 비중 - 현금 제외 (호버: 요약 · 클릭: 종목 구성)", color="white", fontsize=14, fontweight='bold', pad=15)

        canvas_pie = FigureCanvasTkAgg(fig_pie, master=pie_win)
        canvas_pie.draw()
        canvas_pie.get_tk_widget().pack(fill='both', expand=True, padx=10, pady=10)
        if invest_alloc:

            def on_invest_wedge_click(i):
                body = self._format_macro_category_breakdown(labels[i])
                self._show_pie_detail_popup(pie_win, f"{labels[i]} — 포함 종목", body)

            self._setup_pie_hover(canvas_pie, fig_pie, ax_pie, wedges, labels, sizes, parent_win=pie_win, on_wedge_click=on_invest_wedge_click)

    def show_rebalance_popup(self):
        if not self.rebalance_enabled.get():
            messagebox.showinfo("리밸런싱 OFF", "리밸런싱 가이드가 OFF 상태입니다.\n메인 화면에서 ON 후 다시 계산해주세요.")
            return

        rb_win = tk.Toplevel(self.root)
        rb_win.title("자산군 리밸런싱 가이드")
        rb_win.geometry("620x560")
        rb_win.configure(bg=self.BG)
        self.bind_escape_to_close(rb_win)
        try:
            rb_win.attributes('-alpha', self.current_alpha)
            rb_win.after(100, lambda: rb_win.attributes('-alpha', self.current_alpha))
        except Exception:
            pass

        scrollbar = tk.Scrollbar(rb_win)
        scrollbar.pack(side='right', fill='y')
        txt = tk.Text(rb_win, bg=self.ENTRY_BG, fg=self.FG, font=(self.FONT_MAIN[0], 11), yscrollcommand=scrollbar.set)
        txt.pack(side='left', fill='both', expand=True, padx=10, pady=10)
        scrollbar.config(command=txt.yview)

        self._setup_text_tags(txt, title_size=14, title_color=self.ACCENT, body_size=11)

        txt.insert(tk.END, "⚖ 자산군 리밸런싱 가이드\n", "title")
        txt.insert(tk.END, "=" * 46 + "\n")
        txt.insert(
            tk.END,
            f"목표 비중(주식:채권:금:원자재:현금) = "
            f"{self.target_ratios['주식']}:{self.target_ratios['채권']}:{self.target_ratios['금']}:{self.target_ratios['원자재']}:{self.target_ratios['현금성 자산']}\n",
        )
        txt.insert(tk.END, f"기준 총자산: {int(getattr(self, 'current_total_val', 0)):,}원\n\n")

        if getattr(self, "current_rebalance_error", None):
            txt.insert(tk.END, f"⚠ {self.current_rebalance_error}\n", "down")
        else:
            guide_list = getattr(self, "current_rebalance_guide", None) or []
            if not guide_list:
                txt.insert(
                    tk.END,
                    "계산된 리밸런싱 데이터가 없습니다.\n'계산 및 차트/수익률 보기'를 먼저 실행해주세요.\n",
                    "flat",
                )
            else:
                total_val = float(getattr(self, "current_total_val", 0.0))
                for g in guide_list:
                    cur_pct = (g["current"] / total_val * 100) if total_val > 0 else 0.0
                    target_pct = (g["target"] / total_val * 100) if total_val > 0 else 0.0
                    txt.insert(
                        tk.END,
                        f"▶ {g['category']} | 현재 {cur_pct:.2f}% ({int(g['current']):,}원) → 목표 {target_pct:.2f}% ({int(g['target']):,}원)\n",
                    )
                    if g["action"] == "매수":
                        txt.insert(tk.END, f"  - 권장: {int(abs(g['diff'])):,}원 매수\n", "up")
                    elif g["action"] == "매도":
                        txt.insert(tk.END, f"  - 권장: {int(abs(g['diff'])):,}원 매도\n", "down")
                    else:
                        txt.insert(tk.END, "  - 권장: 유지 (목표 비중과 동일)\n", "flat")

        txt.config(state='disabled')

    def update_line_chart(self, view_mode):
        if not hasattr(self, 'history_data') or not self.history_data:
            return
        self.current_chart_view_mode = view_mode

        if hasattr(self, "canvas_line"):
            self._disconnect_line_chart_hovers()

        if hasattr(self, 'btn_daily') and hasattr(self, 'btn_weekly') and hasattr(self, 'btn_monthly'):
            active_bg, active_fg = ("#FFD700", "black")
            idle_bg, idle_fg = ("#3A5A7A", "white")
            self.btn_daily.config(bg=active_bg if view_mode == "일간" else idle_bg, fg=active_fg if view_mode == "일간" else idle_fg)
            self.btn_weekly.config(bg=active_bg if view_mode == "주간" else idle_bg, fg=active_fg if view_mode == "주간" else idle_fg)
            self.btn_monthly.config(bg=active_bg if view_mode == "월간" else idle_bg, fg=active_fg if view_mode == "월간" else idle_fg)

        df = pd.DataFrame.from_dict(self.history_data, orient='index')
        if 'roi' not in df.columns:
            if 0 in df.columns:
                df['roi'] = df[0]
            else:
                df['roi'] = 0.0
        if 'principal' not in df.columns:
            df['principal'] = np.nan
        if 'value' not in df.columns:
            df['value'] = np.nan

        df.index = pd.to_datetime(df.index)
        df = df.sort_index()

        if not df.empty:
            _hset = _kr_holiday_date_set(df.index.min(), df.index.max())
            df = df.loc[df.index.map(lambda t: _is_kr_business_day(t, _hset))]

        if view_mode == "주간":
            df = df.groupby(df.index.to_period('W-FRI')).last()
            df.index = df.index.to_timestamp()
        if view_mode == "월간":
            df = df.groupby(df.index.to_period('M')).last()
            df.index = df.index.to_timestamp()

        if view_mode == "일간" and not df.empty:
            total_points = len(df)
            max_start = max(0, total_points - int(self.daily_window_size))
            self.daily_window_max_start = max_start

            if self.daily_window_follow_latest:
                start = max_start
            else:
                start = max(0, min(int(self.daily_window_start), max_start))
            end = min(total_points, start + int(self.daily_window_size))
            self.daily_window_start = start
            df = df.iloc[start:end]

            if self.daily_window_scale and self.daily_window_scale.winfo_exists():
                self._updating_daily_window_scale = True
                try:
                    self.daily_window_scale.config(to=max_start, state=('normal' if max_start > 0 else 'disabled'))
                    self.daily_window_scale.set(start)
                finally:
                    self._updating_daily_window_scale = False

            if self.daily_window_label and self.daily_window_label.winfo_exists():
                self.daily_window_label.config(
                    text=f"일간 구간: {start + 1}~{end} / {total_points}일 (가로 스크롤로 이동)"
                )
        elif self.daily_window_scale and self.daily_window_scale.winfo_exists():
            self._updating_daily_window_scale = True
            try:
                self.daily_window_scale.config(to=0, state='disabled')
                self.daily_window_scale.set(0)
            finally:
                self._updating_daily_window_scale = False
            if self.daily_window_label and self.daily_window_label.winfo_exists():
                self.daily_window_label.config(text=f"일간 구간: 최근 {self.daily_window_size}일")

        self.fig_line.clf()
        mode_label = view_mode if view_mode in ("일간", "주간", "월간") else "일간"

        if not df.empty:
            dates = df.index
            rois = df['roi']
            prins = df['principal'].ffill().bfill().fillna(0)
            vals = df['value'].ffill().bfill().fillna(0)

            prev_vals = vals.shift(1)
            net_flow = prins.diff().fillna(0.0)
            pure_raw_pct = ((vals - prev_vals - net_flow) / prev_vals.replace(0, np.nan)) * 100.0
            pure_raw_pct = pure_raw_pct.replace([np.inf, -np.inf], np.nan)

            n_pts = len(dates)
            bd_after_prev = np.ones(n_pts, dtype=np.float64)
            for i in range(1, n_pts):
                bd_after_prev[i] = float(
                    _count_kr_bdays_after_prev(dates[i - 1], dates[i], _hset)
                )

            pure_day_returns = pure_raw_pct.copy()
            if view_mode == "일간" and n_pts > 1:
                rawv = pure_raw_pct.to_numpy(dtype=np.float64, copy=True)
                inv_n = 1.0 / bd_after_prev
                rf = rawv / 100.0
                base = 1.0 + rf
                safe = np.isfinite(rf) & (base > 0) & (bd_after_prev > 1)
                rawv[safe] = (np.power(base[safe], inv_n[safe]) - 1.0) * 100.0
                pure_day_returns = pd.Series(rawv, index=pure_raw_pct.index)

            if not pure_day_returns.empty:
                pure_day_returns.iloc[0] = 0.0
            pure_day_returns = pure_day_returns.fillna(0.0)

            ax_roi = self.fig_line.add_subplot(311)
            ax_roi.set_facecolor(self.BG)
            roi_colors = ["#FF6B6B" if r >= 0 else "#4D96FF" for r in rois]
            ax_roi.plot(dates, rois, color="#00FFFF", linewidth=2, marker='o', markersize=6)
            ax_roi.scatter(dates, rois, color=roi_colors, s=50, zorder=5)
            for d, r in zip(dates, rois):
                sign = "+" if r >= 0 else ""
                ax_roi.annotate(f"{sign}{r:.2f}%", (d, r), textcoords="offset points", xytext=(0, 10), ha='center', color='white', fontsize=8, fontweight='bold')
            ax_roi.axhline(0, color='white', linestyle=':', linewidth=1, alpha=0.5)
            ax_roi.set_ylabel("수익률 (%)", color="white")
            ax_roi.set_title(f"투자원금 대비 수익률 ({mode_label})", color="white", fontsize=12, fontweight='bold', pad=10)
            ax_roi.tick_params(axis='y', colors='white', labelsize=9)
            ax_roi.tick_params(axis='x', colors='white', labelsize=8)
            ax_roi.grid(True, linestyle=':', alpha=0.2)

            ax_pure_day = self.fig_line.add_subplot(312)
            ax_pure_day.set_facecolor(self.BG)
            pure_day_colors = ["#FF6B6B" if r >= 0 else "#4D96FF" for r in pure_day_returns]
            ax_pure_day.plot(dates, pure_day_returns, color="#FFA657", linewidth=2, marker='o', markersize=5)
            ax_pure_day.scatter(dates, pure_day_returns, color=pure_day_colors, s=42, zorder=5)
            for d, r in zip(dates, pure_day_returns):
                sign = "+" if r >= 0 else ""
                ax_pure_day.annotate(f"{sign}{r:.2f}%", (d, r), textcoords="offset points", xytext=(0, 10), ha='center', color='white', fontsize=8, fontweight='bold')
            ax_pure_day.axhline(0, color='white', linestyle=':', linewidth=1, alpha=0.5)
            pure_day_mode_label = (
                "직전 기록 대비(영업일 환산)" if view_mode == "일간" else ("전주" if view_mode == "주간" else "전월")
            )
            ax_pure_day.set_ylabel("입출금 제외 (%)", color="white")
            ax_pure_day.set_title(f"{pure_day_mode_label} 순수 성과 ({mode_label})", color="white", fontsize=12, fontweight='bold', pad=10)
            ax_pure_day.tick_params(axis='y', colors='white', labelsize=9)
            ax_pure_day.tick_params(axis='x', colors='white', labelsize=8)
            ax_pure_day.grid(True, linestyle=':', alpha=0.2)

            def _roi_tip(i):
                r = float(rois.iloc[i])
                sign = "+" if r >= 0 else ""
                return f"{_date_with_weekday_kr(dates[i])}\n원금 대비 수익률: {sign}{r:.2f}%"

            def _pure_tip(i):
                r = float(pure_day_returns.iloc[i])
                sign = "+" if r >= 0 else ""
                lbl = "전일 순수 성과" if view_mode == "일간" else ("전주 순수 성과" if view_mode == "주간" else "전월 순수 성과")
                dval = float((vals - prev_vals - net_flow).iloc[i]) if i < len(vals) else 0.0
                if math.isfinite(dval):
                    dval_sign = "+" if dval >= 0 else ""
                    dval_text = f"{dval_sign}{int(round(dval)):,}원"
                else:
                    dval_text = "N/A"
                bd = int(bd_after_prev[i]) if i < len(bd_after_prev) else 1
                raw_r = float(pure_raw_pct.iloc[i]) if i < len(pure_raw_pct) else float("nan")
                head = f"{_date_with_weekday_kr(dates[i])}\n"
                if view_mode == "일간" and i > 0 and bd > 1 and math.isfinite(raw_r):
                    rawsign = "+" if raw_r >= 0 else ""
                    return (
                        head
                        + f"영업일 환산(복리)·일평균: {sign}{r:.2f}%\n"
                        + f"직전 저장 대비 누적 ({bd}영업일): {rawsign}{raw_r:.2f}%\n"
                        + f"순수 손익(원): {dval_text}"
                    )
                return (
                    head + f"{lbl}: {sign}{r:.2f}%\n" + f"{lbl} 원화손익: {dval_text}"
                )

            self._setup_line_series_hover(ax_roi, dates, rois.values, _roi_tip)
            self._setup_line_series_hover(ax_pure_day, dates, pure_day_returns.values, _pure_tip)

            ax_val = self.fig_line.add_subplot(313)
            ax_val.set_facecolor(self.BG)
            ax_val.plot(dates, prins, color="#AAAAAA", linestyle='--', linewidth=2, marker='s', markersize=4, label="투자 원금")
            ax_val.plot(dates, vals, color="#FFD700", linewidth=2.5, marker='o', markersize=5, label="현재 평가금")
            ax_val.fill_between(dates, prins, vals, where=(vals >= prins), color="#FF6B6B", alpha=0.15, interpolate=True)
            ax_val.fill_between(dates, prins, vals, where=(vals < prins), color="#4D96FF", alpha=0.15, interpolate=True)
            ax_val.set_ylabel("자산 규모 (원)", color="white")
            ax_val.set_title(f"투자 원금 vs 평가금 ({mode_label})", color="white", fontsize=12, fontweight='bold', pad=10)
            ax_val.tick_params(axis='y', colors='white', labelsize=9)
            ax_val.tick_params(axis='x', colors='white', labelsize=8)
            ax_val.yaxis.set_major_formatter(FuncFormatter(currency_formatter))
            ax_val.legend(loc='upper left', facecolor=self.BG, edgecolor='white', labelcolor='white', fontsize=9)
            ax_val.grid(True, linestyle=':', alpha=0.2)

            self._setup_line_chart_val_hover(ax_val, dates, prins, vals)

            self.fig_line.autofmt_xdate()
            self.fig_line.subplots_adjust(hspace=0.55)
        else:
            ax = self.fig_line.add_subplot(111)
            ax.set_facecolor(self.BG)
            ax.text(0.5, 0.5, "해당 기간의 기록이 없습니다.", color="white", ha="center", va="center", transform=ax.transAxes)

        self.canvas_line.draw()

    def generate_report_text(self, right_frame, report_data, total_prin, total_val, total_prof, total_roi, ex_rate):
        scrollbar = tk.Scrollbar(right_frame)
        scrollbar.pack(side='right', fill='y')
        txt = tk.Text(right_frame, bg=self.ENTRY_BG, fg=self.FG, font=(self.FONT_MAIN[0], 11), yscrollcommand=scrollbar.set)
        txt.pack(side='left', fill='both', expand=True, padx=5, pady=5)
        scrollbar.config(command=txt.yview)
        self.report_text_widget = txt

        self._setup_text_tags(txt, title_size=14, title_color=self.ACCENT, body_size=11)
        self._fill_report_text(txt, report_data, total_prin, total_val, total_prof, total_roi, ex_rate)

    def _macro_category_pnl_rows(self, report_data):
        """개별 보고서 행을 자산군으로 묶어 투자·평가·손익·수익률을 합산한다."""
        sums: defaultdict[str, dict[str, float]] = defaultdict(lambda: {"prin": 0.0, "val": 0.0})
        for d in report_data:
            if d.get("is_pure_cash"):
                cat = "현금성 자산"
            elif d.get("is_fixed"):
                cat = get_asset_category(d.get("name", ""), "")
            else:
                cat = get_asset_category(d.get("name", ""), d.get("ticker", ""))
            sums[cat]["prin"] += float(d.get("prin", 0) or 0)
            sums[cat]["val"] += float(d.get("val", 0) or 0)
        order = ("주식", "채권", "금", "원자재", "현금성 자산")
        rows: list[dict] = []
        for cat in order:
            if cat not in sums:
                continue
            prin = sums[cat]["prin"]
            val = sums[cat]["val"]
            if prin <= 0 and val <= 0:
                continue
            prof = val - prin
            roi = (prof / prin * 100.0) if prin > 0 else 0.0
            rows.append({"category": cat, "prin": prin, "val": val, "prof": prof, "roi": roi})
        return rows

    def _fill_report_text(self, txt, report_data, total_prin, total_val, total_prof, total_roi, ex_rate):
        txt.config(state='normal')
        txt.delete("1.0", tk.END)
        txt.insert(tk.END, "📊 포트폴리오 수익률 상세 보고서\n", "title")
        txt.insert(tk.END, "=" * 45 + "\n")
        txt.insert(tk.END, f"적용 환율: 1 USD = {ex_rate:,.2f} KRW\n\n")

        txt.insert(tk.END, "[ 개별 종목 수익률 ]\n")
        for d in report_data:
            tag = "up" if d['roi'] > 0 else ("down" if d['roi'] < 0 else "flat")
            sign = "+" if d['roi'] > 0 else ""

            if d.get('is_pure_cash'):
                txt.insert(tk.END, f"▶ {d['name']} [{d['account']}]\n")
                cash_tag = "up" if d['roi'] > 0 else ("down" if d['roi'] < 0 else "flat")
                cash_sign = "+" if d['roi'] > 0 else ""
                txt.insert(tk.END, f"  - 예수금(원화 환산 평가): {int(d['val']):,}원  ·  원가: {int(d['prin']):,}원  ·  ")
                txt.insert(tk.END, f"수익률 {cash_sign}{d['roi']:.2f}%\n", cash_tag)
                txt.insert(tk.END, "  - 손익금: ")
                txt.insert(tk.END, f"{cash_sign}{int(d['prof']):,}원\n", cash_tag)
                if d.get('is_usd_cash'):
                    fx_prof = float(d.get('fx_prof', 0.0))
                    fx_tag = "up" if fx_prof > 0 else ("down" if fx_prof < 0 else "flat")
                    fx_sign = "+" if fx_prof > 0 else ""
                    txt.insert(tk.END, "  - 환손익: ")
                    txt.insert(tk.END, f"{fx_sign}{int(fx_prof):,}원\n", fx_tag)
                txt.insert(tk.END, "\n")
            elif d.get('is_fixed'):
                txt.insert(tk.END, f"▶ {d['name']} [{d['account']}]\n")
                qf = d.get('qty')
                if qf is not None and float(qf) > 0:
                    txt.insert(tk.END, f"  - 보유 수량: {float(qf):,.4f}\n")
                cup = float(d.get('cur_p', 0) or 0)
                if cup > 0:
                    txt.insert(tk.END, f"  - 현재 가격: {cup:,.2f}원 (1단위당)\n")
                avgp = float(d.get('avg_p', 0) or 0)
                if avgp > 0:
                    txt.insert(tk.END, f"  - 평단: {avgp:,.2f}원\n")
                txt.insert(tk.END, f"  - 총 평가액: {int(d['val']):,}원  ·  매수액: {int(d['prin']):,}원  ·  ")
                txt.insert(tk.END, f"수익률 {sign}{d['roi']:.2f}%\n", tag)
                txt.insert(tk.END, "  - 손익금: ")
                txt.insert(tk.END, f"{sign}{int(d['prof']):,}원\n\n", tag)
            else:
                unit = "$" if d.get('is_us') else "원"
                qty = d.get('qty')
                txt.insert(tk.END, f"▶ {d['name']} [{d['account']}]\n")
                if qty is not None:
                    txt.insert(tk.END, f"  - 보유 수량: {qty:,.4f}\n")
                txt.insert(tk.END, f"  - 현재 가격: {d['cur_p']:,.2f}{unit}\n")
                txt.insert(tk.END, f"  - 평단: {d['avg_p']:,.2f}{unit}  ·  ")
                txt.insert(tk.END, f"수익률 {sign}{d['roi']:.2f}%\n", tag)
                txt.insert(tk.END, f"  - 평가액: {int(d['val']):,}원  ·  매수액: {int(d['prin']):,}원\n")
                txt.insert(tk.END, "  - 손익금: ")
                txt.insert(tk.END, f"{sign}{int(d['prof']):,}원\n\n", tag)
                if d.get('is_us'):
                    buy_ex = float(d.get('buy_exchange_rate', ex_rate))
                    txt.insert(tk.END, f"  - 매수 기준 환율: 1 USD = {buy_ex:,.2f} KRW\n")
                    price_prof = float(d.get('price_prof', 0.0))
                    fx_prof = float(d.get('fx_prof', 0.0))
                    price_tag = "up" if price_prof > 0 else ("down" if price_prof < 0 else "flat")
                    fx_tag = "up" if fx_prof > 0 else ("down" if fx_prof < 0 else "flat")
                    price_sign = "+" if price_prof > 0 else ""
                    fx_sign = "+" if fx_prof > 0 else ""
                    txt.insert(tk.END, "  - 가격손익: ")
                    txt.insert(tk.END, f"{price_sign}{int(price_prof):,}원\n", price_tag)
                    txt.insert(tk.END, "  - 환손익: ")
                    txt.insert(tk.END, f"{fx_sign}{int(fx_prof):,}원\n\n", fx_tag)

        txt.insert(tk.END, "=" * 45 + "\n")
        txt.insert(tk.END, "[ 전체 포트폴리오 요약 ]\n", "title")
        txt.insert(tk.END, f"▶ 총 매수 금액 : {int(total_prin):,}원\n")
        txt.insert(tk.END, f"▶ 총 평가 금액 : {int(total_val):,}원\n")

        macro_rows = self._macro_category_pnl_rows(report_data)
        if macro_rows:
            cash_krw_total = 0.0
            cash_usd_total = 0.0
            cash_usd_val_krw_total = 0.0
            for d in report_data:
                if d.get("is_pure_cash"):
                    cash_krw_total += float(d.get("cash_krw", 0.0) or 0.0)
                    usd_amt = float(d.get("cash_usd", 0.0) or 0.0)
                    usd_krw_val = float(d.get("cash_usd_val_krw", 0.0) or 0.0)
                    cash_usd_total += usd_amt
                    cash_usd_val_krw_total += usd_krw_val
                    continue

                name = d.get("name", "")
                if d.get("is_fixed"):
                    cat = get_asset_category(name, "")
                else:
                    cat = get_asset_category(name, d.get("ticker", ""))
                if cat != "현금성 자산":
                    continue

                val = float(d.get("val", 0.0) or 0.0)
                if d.get("is_us"):
                    qty = float(d.get("qty", 0.0) or 0.0)
                    cur_p = float(d.get("cur_p", 0.0) or 0.0)
                    usd_amt = qty * cur_p
                    if usd_amt > 0:
                        cash_usd_total += usd_amt
                        cash_usd_val_krw_total += val
                else:
                    cash_krw_total += val

            txt.insert(tk.END, "\n")
            txt.insert(tk.END, "  ― 자산군별 ―\n", "title")
            for row in macro_rows:
                tag = "up" if row["roi"] > 0 else ("down" if row["roi"] < 0 else "flat")
                sign = "+" if row["roi"] > 0 else ""
                prof_sign = "+" if row["prof"] > 0 else ""
                txt.insert(tk.END, f"  ▶ {row['category']}\n")
                txt.insert(
                    tk.END,
                    f"     투자(매수) {int(row['prin']):,}원  ·  평가 {int(row['val']):,}원  ·  수익률 ",
                )
                txt.insert(tk.END, f"{sign}{row['roi']:.2f}%\n", tag)
                txt.insert(tk.END, "     손익 ")
                txt.insert(tk.END, f"{prof_sign}{int(row['prof']):,}원\n", tag)
                if row["category"] == "현금성 자산":
                    txt.insert(tk.END, f"     원화 자산: {int(cash_krw_total):,}원\n")
                    txt.insert(tk.END, f"     외화 자산: {cash_usd_total:,.2f} USD (원화환산 {int(cash_usd_val_krw_total):,}원)\n")
            txt.insert(tk.END, "\n")

        total_tag = "up" if total_roi > 0 else ("down" if total_roi < 0 else "flat")
        total_sign = "+" if total_roi > 0 else ""

        txt.insert(tk.END, "▶ 통합 손익금 : ")
        txt.insert(tk.END, f"{total_sign}{int(total_prof):,}원\n", total_tag)
        txt.insert(tk.END, "▶ 통합 수익률 : ")
        txt.insert(tk.END, f"{total_sign}{total_roi:.2f}%\n", total_tag)

        if self.rebalance_enabled.get():
            txt.insert(tk.END, "\n" + "=" * 45 + "\n")
            txt.insert(tk.END, "[ 자산군 리밸런싱 가이드 ]\n", "title")
            txt.insert(tk.END, "목표 비중(주식:채권:금:원자재:현금) = ")
            txt.insert(
                tk.END,
                f"{self.target_ratios['주식']}:{self.target_ratios['채권']}:{self.target_ratios['금']}:{self.target_ratios['원자재']}:{self.target_ratios['현금성 자산']}\n",
            )
            txt.insert(tk.END, f"기준 총자산: {int(total_val):,}원\n\n")

            if getattr(self, "current_rebalance_error", None):
                txt.insert(tk.END, f"⚠ {self.current_rebalance_error}\n", "down")
            else:
                for g in (self.current_rebalance_guide or []):
                    diff_sign = "+" if g["diff"] > 0 else ""
                    cur_pct = (g["current"] / total_val * 100) if total_val > 0 else 0.0
                    target_pct = (g["target"] / total_val * 100) if total_val > 0 else 0.0
                    txt.insert(
                        tk.END,
                        f"▶ {g['category']} | 현재 {cur_pct:.2f}% ({int(g['current']):,}원) → 목표 {target_pct:.2f}% ({int(g['target']):,}원)\n",
                    )
                    if g["action"] == "매수":
                        txt.insert(tk.END, f"  - 권장: {int(abs(g['diff'])):,}원 매수 ({diff_sign}{int(g['diff']):,}원)\n", "up")
                    elif g["action"] == "매도":
                        txt.insert(tk.END, f"  - 권장: {int(abs(g['diff'])):,}원 매도 ({int(g['diff']):,}원)\n", "down")
                    else:
                        txt.insert(tk.END, "  - 권장: 유지 (목표 비중과 동일)\n", "flat")

            txt.see(tk.END)

        txt.config(state='disabled')


def run() -> None:
    # Tk 루트를 만든 뒤에 Matplotlib(TkAgg)를 초기화한다. import 시점에 백엔드를
    # 묶어두면 Wayland/일부 Linux에서 Tk C API와 순서가 꼬여 세그폴트가 난다.
    root = tk.Tk()
    _configure_matplotlib_for_tk()
    _app = PortfolioApp(root)

    def signal_handler(sig, frame):
        root.quit()
        root.destroy()
        sys.exit(0)

    signal.signal(signal.SIGINT, signal_handler)

    def check_signals():
        root.after(500, check_signals)

    check_signals()
    root.mainloop()



