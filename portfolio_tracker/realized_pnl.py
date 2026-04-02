from __future__ import annotations

from dataclasses import dataclass, asdict
from typing import Any, Dict, Iterable, List, Optional, Tuple
import datetime as _dt


def _to_date(value: Any) -> _dt.date:
    if isinstance(value, _dt.date) and not isinstance(value, _dt.datetime):
        return value
    if isinstance(value, _dt.datetime):
        return value.date()
    s = str(value).strip()
    # Accept YYYY-MM-DD (primary) or YYYY/MM/DD (fallback)
    for fmt in ("%Y-%m-%d", "%Y/%m/%d"):
        try:
            return _dt.datetime.strptime(s, fmt).date()
        except Exception:
            pass
    raise ValueError(f"Invalid date: {value!r}")


def _to_float(value: Any, default: float = 0.0) -> float:
    try:
        if value is None:
            return default
        if isinstance(value, (int, float)):
            return float(value)
        s = str(value).strip().replace(",", "")
        if not s:
            return default
        return float(s)
    except Exception:
        return default


@dataclass(frozen=True)
class SellRecord:
    """
    Realized PnL record based on a sell transaction.

    - KR: KRW unit price, no FX needed
    - US: USD unit price, require sell_exchange_rate for KRW proceeds conversion
    Cost basis is computed from current holding's avg_price and buy_exchange_rate (if any).
    """

    sell_date: str  # YYYY-MM-DD
    account: str
    ticker: str
    name: str
    qty: float
    sell_price: float  # KRW for KR, USD for US
    is_us: bool
    sell_exchange_rate: Optional[float] = None  # required if is_us
    fee_krw: float = 0.0
    memo: str = ""

    def normalized(self) -> "SellRecord":
        d = _to_date(self.sell_date).strftime("%Y-%m-%d")
        acc = str(self.account or "").strip() or "일반 계좌"
        ticker = str(self.ticker or "").strip().upper()
        name = str(self.name or "").strip()
        qty = _to_float(self.qty)
        sell_price = _to_float(self.sell_price)
        fee_krw = _to_float(self.fee_krw)
        memo = str(self.memo or "").strip()
        is_us = bool(self.is_us)
        ser = self.sell_exchange_rate
        if is_us:
            ser = _to_float(ser, default=0.0)
            if ser <= 0:
                raise ValueError("sell_exchange_rate is required for US ticker")
        else:
            ser = None
        if qty <= 0:
            raise ValueError("qty must be > 0")
        if sell_price <= 0:
            raise ValueError("sell_price must be > 0")
        if fee_krw < 0:
            raise ValueError("fee_krw must be >= 0")
        return SellRecord(
            sell_date=d,
            account=acc,
            ticker=ticker,
            name=name,
            qty=qty,
            sell_price=sell_price,
            is_us=is_us,
            sell_exchange_rate=ser,
            fee_krw=fee_krw,
            memo=memo,
        )

    def to_json(self) -> Dict[str, Any]:
        return asdict(self)

    @staticmethod
    def from_json(d: Dict[str, Any]) -> "SellRecord":
        return SellRecord(
            sell_date=str(d.get("sell_date", "")).strip(),
            account=str(d.get("account", "")).strip(),
            ticker=str(d.get("ticker", "")).strip(),
            name=str(d.get("name", "")).strip(),
            qty=_to_float(d.get("qty", 0.0)),
            sell_price=_to_float(d.get("sell_price", 0.0)),
            is_us=bool(d.get("is_us", False)),
            sell_exchange_rate=(
                None if d.get("sell_exchange_rate") in (None, "") else _to_float(d.get("sell_exchange_rate"))
            ),
            fee_krw=_to_float(d.get("fee_krw", 0.0)),
            memo=str(d.get("memo", "") or "").strip(),
        ).normalized()


@dataclass(frozen=True)
class RealizedPnlRow:
    sell_date: str
    account: str
    ticker: str
    name: str
    qty: float
    proceeds_krw: float
    cost_krw: float
    fee_krw: float
    pnl_krw: float


def calc_realized_row(
    rec: SellRecord,
    holding: Optional[Dict[str, Any]],
) -> RealizedPnlRow:
    """
    holding: current holding dict from portfolio list, matched by (account, ticker).
      - KR: avg_price in KRW
      - US: avg_price in USD and buy_exchange_rate in KRW/USD
    """
    r = rec.normalized()
    avg_price = _to_float((holding or {}).get("avg_price", 0.0))
    buy_ex = _to_float((holding or {}).get("buy_exchange_rate", 0.0))

    if not r.is_us:
        proceeds_krw = r.sell_price * r.qty
        cost_krw = avg_price * r.qty
    else:
        sell_ex = _to_float(r.sell_exchange_rate, default=0.0)
        if sell_ex <= 0:
            raise ValueError("sell_exchange_rate missing")
        if buy_ex <= 0:
            # fallback: if missing, assume sell exchange rate for cost conversion
            buy_ex = sell_ex
        proceeds_krw = r.sell_price * r.qty * sell_ex
        cost_krw = avg_price * r.qty * buy_ex

    fee_krw = float(r.fee_krw or 0.0)
    pnl_krw = proceeds_krw - cost_krw - fee_krw
    return RealizedPnlRow(
        sell_date=r.sell_date,
        account=r.account,
        ticker=r.ticker,
        name=r.name,
        qty=r.qty,
        proceeds_krw=proceeds_krw,
        cost_krw=cost_krw,
        fee_krw=fee_krw,
        pnl_krw=pnl_krw,
    )


def group_period_key(d: _dt.date, period: str) -> str:
    period = str(period).strip().lower()
    if period in ("day", "daily", "일", "일간"):
        return d.strftime("%Y-%m-%d")
    if period in ("week", "weekly", "주", "주간"):
        iso = d.isocalendar()
        return f"{iso.year}-W{iso.week:02d}"
    if period in ("month", "monthly", "월", "월간"):
        return d.strftime("%Y-%m")
    if period in ("year", "yearly", "연", "연간"):
        return d.strftime("%Y")
    raise ValueError(f"Unknown period: {period!r}")


def summarize_realized_pnl(
    records: Iterable[SellRecord],
    holdings: Iterable[Dict[str, Any]],
    period: str,
) -> List[Tuple[str, Dict[str, float]]]:
    """
    Returns list of (period_key, sums) sorted by period_key asc.
    sums keys: proceeds_krw, cost_krw, fee_krw, pnl_krw
    """
    holding_map: Dict[Tuple[str, str], Dict[str, Any]] = {}
    for h in holdings:
        acc = str(h.get("account", "")).strip() or "일반 계좌"
        ticker = str(h.get("ticker", "")).strip().upper()
        if not ticker:
            continue
        holding_map[(acc, ticker)] = h

    agg: Dict[str, Dict[str, float]] = {}
    for rec in records:
        r = rec.normalized()
        row = calc_realized_row(r, holding_map.get((r.account, r.ticker)))
        key = group_period_key(_to_date(row.sell_date), period)
        slot = agg.setdefault(
            key, {"proceeds_krw": 0.0, "cost_krw": 0.0, "fee_krw": 0.0, "pnl_krw": 0.0}
        )
        slot["proceeds_krw"] += float(row.proceeds_krw)
        slot["cost_krw"] += float(row.cost_krw)
        slot["fee_krw"] += float(row.fee_krw)
        slot["pnl_krw"] += float(row.pnl_krw)

    return [(k, agg[k]) for k in sorted(agg.keys())]


def apply_sell_to_portfolio(
    portfolio: List[Dict[str, Any]],
    rec: SellRecord,
) -> List[Dict[str, Any]]:
    """
    Returns updated portfolio list (in-place update of matching holding qty).
    - Match by (account, ticker).
    - If qty becomes <= 0 (tolerance), remove the holding.
    """
    r = rec.normalized()
    out: List[Dict[str, Any]] = []
    tol = 1e-12
    applied = False
    for item in portfolio:
        acc = str(item.get("account", "")).strip() or "일반 계좌"
        ticker = str(item.get("ticker", "")).strip().upper()
        if (not applied) and acc == r.account and ticker == r.ticker:
            old_qty = _to_float(item.get("qty", 0.0))
            new_qty = old_qty - float(r.qty)
            applied = True
            if new_qty > tol:
                item = dict(item)
                item["qty"] = new_qty
                out.append(item)
            else:
                # drop the holding
                pass
        else:
            out.append(item)
    if not applied:
        # If holding not found, keep portfolio unchanged; caller may decide to warn user.
        return list(portfolio)
    return out

