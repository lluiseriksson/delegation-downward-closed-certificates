"""Zero-floating-point exact-rational certificate auditor (DELEG-DC-CERT-1.0).

Audits four exact modes for Abdi, Banihashem, Hajiaghayi, and Mittal (arXiv:2611.33095):
  Mode 1 (knapsack_impossibility_cert)
  Mode 2 (single_threshold_guarantee_cert)
  Mode 3 (bernstein_analytic_cert)
  Mode 4 (capped_menu_seed_profile_cert)

Strict AST typing: rejects IEEE-754 scalars, booleans as ints, non-ASCII Unicode digits,
unreduced rationals, oversized strings, unknown keys, and excessive nesting.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple


def _gcd(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a

from .delegation_exact import (
    algorithm2_accepts,
    bernstein_coeffs_on_interval,
    compute_excess_e,
    enumerate_product_distribution,
    eval_p7,
    exp_taylor_7_minus_13_2,
    frac_to_str,
    is_downward_closed,
    is_seed_at_level,
    menu_score_realization,
    offline_optimum,
)

SCHEMA_ID = "DELEG-DC-CERT-1.0"
MAX_AST_DEPTH = 20
MAX_RAT_STR_LEN = 2000

VALID_MODES: Set[str] = {
    "knapsack_impossibility_cert",
    "single_threshold_guarantee_cert",
    "bernstein_analytic_cert",
    "capped_menu_seed_profile_cert",
}


class DelegationCertError(ValueError):
    """Raised whenever a certificate violates schema, typing, or mathematical invariants."""


def _check_ast_strict(obj: Any, depth: int = 0) -> None:
    if depth > MAX_AST_DEPTH:
        raise DelegationCertError("Certificate exceeds maximum JSON nesting depth")
    if isinstance(obj, bool) or obj is None or isinstance(obj, int) or isinstance(obj, str):
        return
    if isinstance(obj, list):
        for item in obj:
            _check_ast_strict(item, depth + 1)
        return
    if isinstance(obj, dict):
        for k, v in obj.items():
            if not isinstance(k, str):
                raise DelegationCertError("Dictionary keys must be strings")
            _check_ast_strict(v, depth + 1)
        return
    raise DelegationCertError(f"Forbidden non-exact AST type: {type(obj).__name__}")


def _require_keys(d: Any, required: Set[str], ctx: str) -> Dict[str, Any]:
    if not isinstance(d, dict):
        raise DelegationCertError(f"{ctx}: expected JSON object")
    actual = set(d.keys())
    if actual != required:
        raise DelegationCertError(f"{ctx}: key mismatch missing={sorted(required - actual)} extra={sorted(actual - required)}")
    return d


def _parse_int(val: Any, ctx: str) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise DelegationCertError(f"{ctx}: expected strict integer")
    return val


def _parse_frac(val: Any, ctx: str) -> Fraction:
    if not isinstance(val, str):
        raise DelegationCertError(f"{ctx}: expected canonical rational string")
    if len(val) > MAX_RAT_STR_LEN:
        raise DelegationCertError(f"{ctx}: rational string exceeds {MAX_RAT_STR_LEN} chars")
    if not val or val != val.strip():
        raise DelegationCertError(f"{ctx}: empty or whitespace-padded rational string")
    if "/" in val:
        parts = val.split("/")
        if len(parts) != 2:
            raise DelegationCertError(f"{ctx}: malformed rational '{val}'")
        num_s, den_s = parts
        neg = num_s.startswith("-")
        dn = num_s[1:] if neg else num_s
        if not dn or not (dn.isascii() and dn.isdigit()):
            raise DelegationCertError(f"{ctx}: invalid numerator '{num_s}'")
        if not den_s or not (den_s.isascii() and den_s.isdigit()):
            raise DelegationCertError(f"{ctx}: invalid denominator '{den_s}'")
        if (len(dn) > 1 and dn.startswith("0")) or (len(den_s) > 1 and den_s.startswith("0")):
            raise DelegationCertError(f"{ctx}: leading zero in '{val}'")
        num = -int(dn) if neg else int(dn)
        den = int(den_s)
        if den <= 1 or num == 0 or _gcd(abs(num), den) != 1:
            raise DelegationCertError(f"{ctx}: non-canonical fraction '{val}'")
        return Fraction(num, den)
    neg = val.startswith("-")
    digits = val[1:] if neg else val
    if not digits or not (digits.isascii() and digits.isdigit()):
        raise DelegationCertError(f"{ctx}: invalid integer rational '{val}'")
    if len(digits) > 1 and digits.startswith("0"):
        raise DelegationCertError(f"{ctx}: leading zero in '{val}'")
    if neg and digits == "0":
        raise DelegationCertError(f"{ctx}: forbidden '-0'")
    return Fraction(-int(digits) if neg else int(digits), 1)


def _parse_instance(
    raw_n: Any,
    raw_feasible: Any,
    raw_supports: Any,
    ctx: str,
) -> Tuple[int, List[Set[int]], List[List[Tuple[Fraction, Fraction]]]]:
    n = _parse_int(raw_n, f"{ctx}.num_items")
    if n < 1 or n > 8:
        raise DelegationCertError(f"{ctx}: num_items must be in 1..8")
    if not isinstance(raw_feasible, list) or not raw_feasible:
        raise DelegationCertError(f"{ctx}: feasible_family must be nonempty list")
    feasible: List[Set[int]] = []
    seen_sets: Set[frozenset[int]] = set()
    for idx, s_raw in enumerate(raw_feasible):
        if not isinstance(s_raw, list):
            raise DelegationCertError(f"{ctx}.feasible_family[{idx}] must be list")
        s_elems: List[int] = [_parse_int(e, f"{ctx}.feasible[{idx}]") for e in s_raw]
        if len(set(s_elems)) != len(s_elems):
            raise DelegationCertError(f"{ctx}.feasible_family[{idx}] has duplicate items")
        if any(e < 0 or e >= n for e in s_elems):
            raise DelegationCertError(f"{ctx}.feasible_family[{idx}] item out of range")
        fs = frozenset(s_elems)
        if fs in seen_sets:
            raise DelegationCertError(f"{ctx}.feasible_family[{idx}] duplicate set")
        seen_sets.add(fs)
        feasible.append(set(s_elems))
    if not is_downward_closed(feasible):
        raise DelegationCertError(f"{ctx}: feasible_family is not downward closed")

    if not isinstance(raw_supports, list) or len(raw_supports) != n:
        raise DelegationCertError(f"{ctx}: item_supports must have length {n}")
    supports: List[List[Tuple[Fraction, Fraction]]] = []
    for i, supp_raw in enumerate(raw_supports):
        if not isinstance(supp_raw, list) or not supp_raw or len(supp_raw) > 6:
            raise DelegationCertError(f"{ctx}.item_supports[{i}] must have 1..6 atoms")
        row: List[Tuple[Fraction, Fraction]] = []
        p_sum = Fraction(0, 1)
        seen_v: Set[Fraction] = set()
        for j, atom in enumerate(supp_raw):
            ad = _require_keys(atom, {"value", "prob"}, f"{ctx}.item_supports[{i}][{j}]")
            v = _parse_frac(ad["value"], f"{ctx}.supp[{i}][{j}].value")
            pr = _parse_frac(ad["prob"], f"{ctx}.supp[{i}][{j}].prob")
            if v < 0 or pr <= 0 or pr > 1:
                raise DelegationCertError(f"{ctx}: invalid value/prob in item_supports[{i}][{j}]")
            if v in seen_v:
                raise DelegationCertError(f"{ctx}: duplicate value in item_supports[{i}]")
            seen_v.add(v)
            p_sum += pr
            row.append((v, pr))
        if p_sum != Fraction(1, 1):
            raise DelegationCertError(f"{ctx}.item_supports[{i}] probabilities sum to {p_sum} != 1")
        supports.append(row)
    return n, feasible, supports


# ---------------------------------------------------------------------------
# Mode 1: Section 3 Five-Item Knapsack Impossibility Certificate
# ---------------------------------------------------------------------------
def _verify_mode1(payload: Any) -> Dict[str, Any]:
    p = _require_keys(
        payload,
        {
            "jackpot_prob",
            "eta",
            "expected_V",
            "expected_det_max",
            "expected_det_ratio",
            "expected_rand_case1_bound",
            "expected_rand_case2_bound",
            "expected_rand_ratio",
        },
        "mode1.payload",
    )
    eps = _parse_frac(p["jackpot_prob"], "jackpot_prob")
    eta = _parse_frac(p["eta"], "eta")
    if eps <= 0 or eps >= Fraction(1, 2):
        raise DelegationCertError("jackpot_prob eps must lie in (0, 1/2)")
    if eta <= 0 or eta > Fraction(1, 1):
        raise DelegationCertError("eta must lie in (0, 1]")

    # Construct the exact 5-item knapsack family (A, B, E, C, J) with jackpot 9/eps w.p. eps
    jackpot_val = Fraction(9, 1) / eps
    if jackpot_val <= Fraction(18, 1):
        raise DelegationCertError("Jackpot high value 9/eps must exceed 18")
    feasible = [
        set(), {0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}
    ]
    supports = [
        [(Fraction(9, 1), Fraction(1, 3)), (Fraction(0, 1), Fraction(2, 3))],  # A
        [(Fraction(9, 1), Fraction(1, 3)), (Fraction(0, 1), Fraction(2, 3))],  # B
        [(Fraction(3, 1), Fraction(1, 1))],                                    # E
        [(Fraction(10, 1), Fraction(1, 1))],                                   # C
        [(jackpot_val, eps), (Fraction(0, 1), Fraction(1, 1) - eps)],          # J
    ]
    joint = enumerate_product_distribution(supports)
    V = sum((pr * offline_optimum(vals, feasible) for pr, vals in joint), Fraction(0, 1))
    # Cross-check closed form V = 9 + (1 - eps) * 34/3
    V_closed = Fraction(9, 1) + (Fraction(1, 1) - eps) * Fraction(34, 3)
    if V != V_closed or V != _parse_frac(p["expected_V"], "expected_V"):
        raise DelegationCertError(f"Offline optimum V mismatch: {V} vs {p['expected_V']}")

    # Deterministic bound = 10 (Prop. 3.1)
    det_max = Fraction(10, 1)
    det_ratio = det_max / V
    if _parse_frac(p["expected_det_max"], "expected_det_max") != det_max:
        raise DelegationCertError("expected_det_max must be 10")
    if _parse_frac(p["expected_det_ratio"], "expected_det_ratio") != det_ratio:
        raise DelegationCertError("expected_det_ratio mismatch")
    if det_ratio >= Fraction(1, 2):
        raise DelegationCertError("Deterministic ratio must be strictly < 1/2")

    # Randomized Case 1 & Case 2 bounds (Thm. 3.2 & Prop. 3.3)
    case1 = Fraction(10, 1) + Fraction(20, 9) * (Fraction(1, 1) - eps) * eta
    case2 = Fraction(10, 1) + Fraction(14, 9) * (Fraction(1, 1) - eps) * eta
    if case2 > case1:
        raise DelegationCertError("Case 2 bound unexpectedly exceeds Case 1 bound")
    if _parse_frac(p["expected_rand_case1_bound"], "expected_rand_case1_bound") != case1:
        raise DelegationCertError("expected_rand_case1_bound mismatch")
    if _parse_frac(p["expected_rand_case2_bound"], "expected_rand_case2_bound") != case2:
        raise DelegationCertError("expected_rand_case2_bound mismatch")
    rand_ratio = case1 / V
    if _parse_frac(p["expected_rand_ratio"], "expected_rand_ratio") != rand_ratio:
        raise DelegationCertError("expected_rand_ratio mismatch")
    if rand_ratio >= Fraction(1, 2):
        raise DelegationCertError("Randomized ratio must be strictly < 1/2")

    return {
        "mode": "knapsack_impossibility_cert",
        "V": frac_to_str(V),
        "det_ratio": frac_to_str(det_ratio),
        "rand_ratio": frac_to_str(rand_ratio),
    }


# ---------------------------------------------------------------------------
# Mode 2: Section 4 Algorithm 1 Single-Threshold & Efron-Stein Certificate
# ---------------------------------------------------------------------------
def _verify_mode2(payload: Any) -> Dict[str, Any]:
    p = _require_keys(
        payload,
        {
            "num_items",
            "feasible_family",
            "item_supports",
            "threshold_z",
            "clip_c",
            "expected_V",
            "expected_B_z",
            "expected_menu_score",
            "expected_clipped_mean",
            "expected_clipped_var",
        },
        "mode2.payload",
    )
    _, feasible, supports = _parse_instance(
        p["num_items"], p["feasible_family"], p["item_supports"], "mode2"
    )
    z = _parse_frac(p["threshold_z"], "threshold_z")
    c = _parse_frac(p["clip_c"], "clip_c")
    if z <= 0 or c <= 0:
        raise DelegationCertError("threshold_z and clip_c must be strictly positive")

    joint = enumerate_product_distribution(supports)
    V = sum((pr * offline_optimum(vals, feasible) for pr, vals in joint), Fraction(0, 1))
    if V <= 0:
        raise DelegationCertError("Offline optimum V must be > 0")
    if _parse_frac(p["expected_V"], "expected_V") != V:
        raise DelegationCertError(f"expected_V mismatch: exact {V}")

    # Compute exact B(z) = z * P(W >= z) + e(z) * P(W < z) and exact menu score E[b_M(X)]
    p_ge_z = sum((pr for pr, vals in joint if offline_optimum(vals, feasible) >= z), Fraction(0, 1))
    e_z = compute_excess_e(supports, z)
    B_z = z * p_ge_z + e_z * (Fraction(1, 1) - p_ge_z)
    if _parse_frac(p["expected_B_z"], "expected_B_z") != B_z:
        raise DelegationCertError(f"expected_B_z mismatch: exact {B_z}")

    exp_score = Fraction(0, 1)
    for pr, vals in joint:
        acc = [s for s in feasible if len(s) > 0 and sum((vals[i] for i in s), Fraction(0, 1)) >= z]
        sc = menu_score_realization(vals, feasible, acc)
        exp_score += pr * sc
    if _parse_frac(p["expected_menu_score"], "expected_menu_score") != exp_score:
        raise DelegationCertError(f"expected_menu_score mismatch: exact {exp_score}")
    if exp_score < B_z:
        raise DelegationCertError("Lemma 4.2 violated: expected score < B(z)")
    if B_z * Fraction(10, 1) < Fraction(3, 1) * V:
        raise DelegationCertError("Theorem 4.1 threshold guarantee B(z) >= (3/10)*V violated")

    # Verify Lemma 4.3 Efron-Stein bound Var(Z_c) <= c * E[Z_c]
    z_vals = [(pr, offline_optimum(vals, feasible, cap=c)) for pr, vals in joint]
    mu_c = sum((pr * zv for pr, zv in z_vals), Fraction(0, 1))
    var_c = sum((pr * (zv - mu_c) * (zv - mu_c) for pr, zv in z_vals), Fraction(0, 1))
    if _parse_frac(p["expected_clipped_mean"], "expected_clipped_mean") != mu_c:
        raise DelegationCertError(f"expected_clipped_mean mismatch: exact {mu_c}")
    if _parse_frac(p["expected_clipped_var"], "expected_clipped_var") != var_c:
        raise DelegationCertError(f"expected_clipped_var mismatch: exact {var_c}")
    if var_c > c * mu_c:
        raise DelegationCertError("Lemma 4.3 Efron-Stein variance bound Var(Z_c) <= c*mu_c violated")

    return {
        "mode": "single_threshold_guarantee_cert",
        "V": frac_to_str(V),
        "B_z": frac_to_str(B_z),
        "ratio": frac_to_str(exp_score / V),
        "var_c": frac_to_str(var_c),
    }


# ---------------------------------------------------------------------------
# Mode 3: Lemma 4.4 Exact Bernstein Degree-7 Positivity & Taylor Certificate
# ---------------------------------------------------------------------------
def _verify_mode3(payload: Any) -> Dict[str, Any]:
    p = _require_keys(
        payload,
        {
            "interval_left",
            "interval_right",
            "expected_exp_gap",
            "expected_case1_gap",
            "expected_bernstein_coeffs",
            "expected_min_beta",
            "probe_points",
        },
        "mode3.payload",
    )
    left = _parse_frac(p["interval_left"], "interval_left")
    right = _parse_frac(p["interval_right"], "interval_right")
    if left < Fraction(2, 13) or right > Fraction(2, 3) or left >= right:
        raise DelegationCertError("Subinterval [left, right] must satisfy 2/13 <= left < right <= 2/3")

    exp_gap = exp_taylor_7_minus_13_2()
    if exp_gap != Fraction(3772963, 234881024) or _parse_frac(p["expected_exp_gap"], "expected_exp_gap") != exp_gap:
        raise DelegationCertError("Lemma 4.4 Eq. (4.11) exp Taylor gap mismatch")

    case1_gap = (
        Fraction(52, 3) + Fraction(1, 1) - Fraction(50, 13)
        - Fraction(80, 33) * Fraction(80, 33) - Fraction(40, 11) - Fraction(13, 5)
    )
    if case1_gap != Fraction(168034, 70785) or _parse_frac(p["expected_case1_gap"], "expected_case1_gap") != case1_gap:
        raise DelegationCertError("Lemma 4.4 Case 1 gap mismatch")

    betas = bernstein_coeffs_on_interval(left, right)
    raw_betas = p["expected_bernstein_coeffs"]
    if not isinstance(raw_betas, list) or len(raw_betas) != 8:
        raise DelegationCertError("expected_bernstein_coeffs must have length 8")
    parsed_betas = [_parse_frac(rb, f"expected_bernstein_coeffs[{i}]") for i, rb in enumerate(raw_betas)]
    if parsed_betas != betas:
        raise DelegationCertError("Bernstein coefficients mismatch")
    min_b = min(betas)
    if _parse_frac(p["expected_min_beta"], "expected_min_beta") != min_b:
        raise DelegationCertError("expected_min_beta mismatch")
    if min_b <= 0:
        raise DelegationCertError(f"Bernstein minimum coefficient is not strictly positive: {min_b}")

    probes = p["probe_points"]
    if not isinstance(probes, list) or len(probes) < 2:
        raise DelegationCertError("probe_points must contain at least 2 distinct points")
    seen_p: Set[Fraction] = set()
    for idx, rp in enumerate(probes):
        b = _parse_frac(rp, f"probe_points[{idx}]")
        if b in seen_p:
            raise DelegationCertError(f"Duplicate probe point {b}")
        seen_p.add(b)
        if b < left or b > right:
            raise DelegationCertError(f"Probe point {b} outside [{left}, {right}]")
        val = eval_p7(b)
        if val < min_b:
            raise DelegationCertError("Convex-hull lower bound P(b) >= min_k beta_k violated")

    return {
        "mode": "bernstein_analytic_cert",
        "interval": f"[{frac_to_str(left)}, {frac_to_str(right)}]",
        "min_beta": frac_to_str(min_b),
    }


# ---------------------------------------------------------------------------
# Mode 4: Algorithm 2 Capped Seed-Reserve Menu & Lemma 6.3 Profile Certificate
# ---------------------------------------------------------------------------
def _verify_mode4(payload: Any) -> Dict[str, Any]:
    p = _require_keys(
        payload,
        {
            "num_items",
            "feasible_family",
            "item_supports",
            "cap_c",
            "cutoffs",
            "open_cutoffs",
            "body_type",
            "level_t",
            "upper_u",
            "reserve_a",
            "profile_levels",
            "expected_V",
            "expected_menu_score",
            "expected_beats_29_70",
            "expected_seed_count",
        },
        "mode4.payload",
    )
    n, feasible, supports = _parse_instance(
        p["num_items"], p["feasible_family"], p["item_supports"], "mode4"
    )
    cap_c = _parse_frac(p["cap_c"], "cap_c")
    level_t = _parse_frac(p["level_t"], "level_t")
    if cap_c <= 0 or level_t <= cap_c:
        raise DelegationCertError("Algorithm 2 requires 0 < cap_c < level_t")
    if not isinstance(p["cutoffs"], list) or len(p["cutoffs"]) != n:
        raise DelegationCertError("cutoffs must have length num_items")
    cutoffs = [_parse_frac(x, f"cutoffs[{i}]") for i, x in enumerate(p["cutoffs"])]
    if any(d <= 0 for d in cutoffs):
        raise DelegationCertError("All cutoffs d_i must be > 0")
    if not isinstance(p["open_cutoffs"], list) or len(p["open_cutoffs"]) != n:
        raise DelegationCertError("open_cutoffs must have length num_items")
    if not all(isinstance(b, bool) for b in p["open_cutoffs"]):
        raise DelegationCertError("open_cutoffs must be booleans")
    open_cutoffs: List[bool] = p["open_cutoffs"]

    body_type = p["body_type"]
    if body_type not in {"threshold", "seeds_upper", "seeds_reserve"}:
        raise DelegationCertError(f"Unknown body_type '{body_type}'")
    upper_u = None if p["upper_u"] is None else _parse_frac(p["upper_u"], "upper_u")
    reserve_a = None if p["reserve_a"] is None else _parse_frac(p["reserve_a"], "reserve_a")
    if body_type == "seeds_upper":
        if upper_u is None or upper_u <= level_t:
            raise DelegationCertError("seeds_upper requires upper_u > level_t")
    if body_type == "seeds_reserve":
        if reserve_a is None or reserve_a <= 0 or reserve_a > 1:
            raise DelegationCertError("seeds_reserve requires 0 < reserve_a <= 1")

    joint = enumerate_product_distribution(supports)
    V = sum((pr * offline_optimum(vals, feasible) for pr, vals in joint), Fraction(0, 1))
    if V <= 0 or _parse_frac(p["expected_V"], "expected_V") != V:
        raise DelegationCertError(f"expected_V mismatch: exact {V}")

    # Evaluate Algorithm 2 menu score & verify all seeds satisfy Eq. (5.2) b_P > 0
    exp_score = Fraction(0, 1)
    seed_hits = 0
    for pr, vals in joint:
        w = [v if v <= cap_c else cap_c for v in vals]
        acc = []
        for s in feasible:
            if not s:
                continue
            if is_seed_at_level(s, w, level_t):
                seed_hits += 1
                w_p = sum((w[i] for i in s), Fraction(0, 1))
                w_min = min(w[i] for i in s)
                b_p = level_t + w_min - w_p
                if b_p <= 0 or b_p > w_min:
                    raise DelegationCertError("Eq. (5.2) seed reserve gap invariant violated")
            if algorithm2_accepts(s, vals, cap_c, cutoffs, open_cutoffs, body_type, level_t, upper_u, reserve_a):
                acc.append(s)
        exp_score += pr * menu_score_realization(vals, feasible, acc)

    if _parse_frac(p["expected_menu_score"], "expected_menu_score") != exp_score:
        raise DelegationCertError(f"expected_menu_score mismatch: exact {exp_score}")
    if _parse_int(p["expected_seed_count"], "expected_seed_count") != seed_hits:
        raise DelegationCertError(f"expected_seed_count mismatch: exact {seed_hits}")
    beats = exp_score * Fraction(70, 1) > Fraction(29, 1) * V
    if not isinstance(p["expected_beats_29_70"], bool) or p["expected_beats_29_70"] != beats:
        raise DelegationCertError("expected_beats_29_70 flag mismatch")

    # Verify Lemma 6.3(b),(c) profile relations at profile_levels
    raw_levels = p["profile_levels"]
    if not isinstance(raw_levels, list) or len(raw_levels) < 2:
        raise DelegationCertError("profile_levels must have at least 2 increasing levels")
    levels = [_parse_frac(x, f"profile_levels[{i}]") for i, x in enumerate(raw_levels)]
    for i in range(len(levels) - 1):
        if levels[i] >= levels[i + 1]:
            raise DelegationCertError("profile_levels must be strictly increasing")
    z_dist = [(pr, offline_optimum(vals, feasible, cap=cap_c)) for pr, vals in joint]
    mu_c = sum((pr * zv for pr, zv in z_dist), Fraction(0, 1))
    e_c = compute_excess_e(supports, cap_c)
    if V - mu_c > e_c:
        raise DelegationCertError("Lemma 6.3(b) V - mu_c <= e(c) violated")

    def _S(lvl: Fraction) -> Fraction:
        return sum((pr for pr, zv in z_dist if zv >= lvl), Fraction(0, 1))

    def _D(lvl: Fraction) -> Fraction:
        return sum((pr * (zv - lvl) for pr, zv in z_dist if zv > lvl), Fraction(0, 1))

    for i in range(len(levels) - 1):
        x_l, y_l = levels[i], levels[i + 1]
        dx_dy = _D(x_l) - _D(y_l)
        if not ((y_l - x_l) * _S(y_l) <= dx_dy <= (y_l - x_l) * _S(x_l)):
            raise DelegationCertError("Lemma 6.3(c) stop-loss sandwich violated")

    return {
        "mode": "capped_menu_seed_profile_cert",
        "body_type": body_type,
        "V": frac_to_str(V),
        "score": frac_to_str(exp_score),
        "ratio": frac_to_str(exp_score / V),
        "beats_29_70": beats,
        "seed_hits": seed_hits,
    }


def verify_certificate(cert: Any) -> Dict[str, Any]:
    """Audit a decoded JSON certificate under DELEG-DC-CERT-1.0."""
    _check_ast_strict(cert)
    root = _require_keys(cert, {"schema", "mode", "name", "payload"}, "certificate")
    if root["schema"] != SCHEMA_ID:
        raise DelegationCertError(f"Unsupported schema '{root['schema']}'")
    mode = root["mode"]
    if not isinstance(mode, str) or mode not in VALID_MODES:
        raise DelegationCertError(f"Unknown mode '{mode}'")
    name = root["name"]
    if not isinstance(name, str) or not name or name != name.strip():
        raise DelegationCertError("Certificate name must be non-empty stripped string")

    if mode == "knapsack_impossibility_cert":
        res = _verify_mode1(root["payload"])
    elif mode == "single_threshold_guarantee_cert":
        res = _verify_mode2(root["payload"])
    elif mode == "bernstein_analytic_cert":
        res = _verify_mode3(root["payload"])
    else:
        res = _verify_mode4(root["payload"])
    res["name"] = name
    return res


def verify_certificate_file(path: Path) -> Dict[str, Any]:
    """Load and strictly verify a certificate file from disk, rejecting IEEE-754 tokens."""
    def _reject_non_exact(token: str) -> Any:
        raise DelegationCertError(f"Forbidden IEEE-754 token in JSON: {token}")

    def _reject_const(token: str) -> Any:
        raise DelegationCertError(f"Forbidden JSON constant: {token}")

    raw = path.read_text(encoding="utf-8")
    try:
        data = json.loads(raw, parse_float=_reject_non_exact, parse_constant=_reject_const)
    except DelegationCertError:
        raise
    except Exception as exc:
        raise DelegationCertError(f"Invalid JSON: {exc}") from exc
    return verify_certificate(data)
