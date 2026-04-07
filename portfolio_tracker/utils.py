from __future__ import annotations

import datetime
import os
import platform
from typing import Any, Dict, Optional, Set

import pandas as pd

current_os = platform.system()

_WEEKDAYS_KR = ("월", "화", "수", "목", "금", "토", "일")


def weekday_kr(ts) -> str:
    return _WEEKDAYS_KR[pd.Timestamp(ts).weekday()]


def date_with_weekday_kr(ts) -> str:
    t = pd.Timestamp(ts)
    return f"{t.strftime('%Y-%m-%d')} ({weekday_kr(t)})"


def kr_holiday_date_set(dmin, dmax) -> Set[datetime.date]:
    """한국 법정공휴일 date 집합(연도 범위). `holidays` 패키지가 있으면 음력·대체공휴일 포함."""
    dmin = pd.Timestamp(dmin).date()
    dmax = pd.Timestamp(dmax).date()
    years = range(dmin.year, dmax.year + 1)
    out: Set[datetime.date] = set()
    for y in years:
        for m, d in (
            (1, 1),
            (3, 1),
            (5, 5),
            (6, 6),
            (8, 15),
            (10, 3),
            (10, 9),
            (12, 25),
        ):
            try:
                out.add(datetime.date(y, m, d))
            except ValueError:
                pass
    try:
        import holidays

        cal = holidays.SouthKorea(years=years)
        out.update(cal.keys())
    except Exception:
        pass
    return out


def is_kr_business_day(ts, holiday_dates: Set[datetime.date]) -> bool:
    d = pd.Timestamp(ts).normalize().date()
    if d.weekday() >= 5:
        return False
    if d in holiday_dates:
        return False
    return True


def count_kr_business_days_after_prev(
    prev_ts,
    curr_ts,
    holiday_dates: Set[datetime.date],
) -> int:
    """
    직전 스냅샷일 다음날부터 현재 스냅샷일까지(양 끝 포함)의 한국 영업일 수.
    일간 순수 수익률을 '며칠치 누적'으로 나누어 영업일 환산할 때 사용한다.
    """
    p = pd.Timestamp(prev_ts).normalize()
    c = pd.Timestamp(curr_ts).normalize()
    if c <= p:
        return 1
    n = 0
    d = p.date()
    end = c.date()
    step = datetime.timedelta(days=1)
    cur = d + step
    while cur <= end:
        if is_kr_business_day(pd.Timestamp(cur), holiday_dates):
            n += 1
        cur += step
    return max(n, 1)


def normalize_account_cash_entry(raw: Any) -> Optional[Dict[str, Any]]:
    """JSON의 account_cash 항목을 정규화한다."""
    if not isinstance(raw, dict):
        return None
    acc = str(raw.get("account", "")).strip() or "일반 계좌"
    try:
        ck = float(raw.get("cash_krw", 0) or 0)
    except (TypeError, ValueError):
        ck = 0.0
    try:
        cu = float(raw.get("cash_usd", 0) or 0)
    except (TypeError, ValueError):
        cu = 0.0
    try:
        usd_cost_krw = float(raw.get("usd_cost_krw", 0) or 0)
    except (TypeError, ValueError):
        usd_cost_krw = 0.0
    if ck == 0 and cu == 0:
        return None
    return {"account": acc, "cash_krw": ck, "cash_usd": cu, "usd_cost_krw": usd_cost_krw}


def get_user_data_dir() -> str:
    """
    패키징 배포 환경에서도 쓰기 가능한 사용자 데이터 디렉터리를 반환한다.
    Linux   : ~/.local/share/portfolio-tracker
    macOS   : ~/Library/Application Support/portfolio-tracker
    Windows : %APPDATA%\\portfolio-tracker
    """
    app_name = "portfolio-tracker"
    home_dir = os.path.expanduser("~")

    if current_os == "Windows":
        base_dir = os.getenv("APPDATA", home_dir)
    elif current_os == "Darwin":
        base_dir = os.path.join(home_dir, "Library", "Application Support")
    else:
        base_dir = os.getenv("XDG_DATA_HOME", os.path.join(home_dir, ".local", "share"))

    data_dir = os.path.join(base_dir, app_name)
    os.makedirs(data_dir, exist_ok=True)
    return data_dir


def get_history_file_path() -> str:
    return os.path.join(get_user_data_dir(), "portfolio_history.json")


def get_realized_pnl_records_file_path() -> str:
    return os.path.join(get_user_data_dir(), "realized_pnl_records.json")


def is_korean_ticker(ticker: Any) -> bool:
    ticker_str = str(ticker).strip()
    return len(ticker_str) == 6 and ticker_str[0].isdigit()


def normalize_ticker_base(ticker: Any) -> str:
    """거래소 접미사(TLT.K, TLT.US 등)를 제거해 심볼 루트만 남긴다."""
    s = str(ticker).upper().strip()
    if not s:
        return ""
    if "." in s:
        s = s.split(".", 1)[0]
    return s


_BOND_ETF_TICKERS = frozenset(
    {
        "TLT",
        "TMF",
        "IEF",
        "SHY",
        "BND",
        "AGG",
        "EDV",
        "TLTW",
        "GOVT",
        "SPTL",
        "SPTS",
        "VGIT",
        "VGSH",
        "SCHZ",
        "LQD",
        "HYG",
        "JNK",
        "TIP",
        "VTIP",
        "SCHP",
        "SPIP",
        "STIP",
        "TMV",
        "TBT",
        "TYD",
        "TYO",
        "PST",
        "TBF",
    }
)


def currency_formatter(x, _pos=None) -> str:
    if x >= 100000000:
        return f"{x/100000000:.1f}억"
    if x >= 10000:
        return f"{int(x/10000):,}만"
    return f"{int(x):,}"


def get_asset_category(name: Any, ticker: Any = "") -> str:
    n_up = str(name).upper().strip()
    t_up = str(ticker).upper().strip()
    t_sym = normalize_ticker_base(ticker)
    n_sym = normalize_ticker_base(name)

    if t_sym == "SGOV" or t_up == "SGOV" or any(k in n_up for k in ["CD금리", "머니마켓", "KOFR", "파킹", "예수금"]):
        return "현금성 자산"

    if (
        n_up == "금"
        or " 금 " in n_up
        or n_up.startswith("금 ")
        or n_up.endswith(" 금")
        or any(
            k in n_up
            for k in [
                "금현물",
                "KRX금",
                "골드",
                "GOLD",
                "실물금",
                "골드바",
                "순금",
                "한국금거래소",
                "센골드",
                "금은방",
                "금액티브",
                "금선물",
                "금은선물",
            ]
        )
        or t_sym in ["GLD", "IAU", "SGOL", "GLDM", "OUNZ", "IAUM", "GOLD"]
        or t_up in ["GLD", "IAU", "SGOL", "GLDM", "OUNZ", "IAUM", "GOLD"]
    ):
        return "금"

    if any(k in n_up for k in ["채권", "국채", "국고채", "회사채", "종합채권", "TREASURY"]) or (
        t_sym in _BOND_ETF_TICKERS or n_sym in _BOND_ETF_TICKERS
    ):
        return "채권"

    if any(k in n_up for k in ["원자재", "원유", "석유", "은선물", "은현물", "구리", "팔라듐", "농산물", "WTI"]) or (
        t_sym in ["USO", "SLV", "PDBC", "GSG", "SIL", "CPER"]
        or t_up in ["USO", "SLV", "PDBC", "GSG", "SIL", "CPER"]
    ):
        return "원자재"

    return "주식"

