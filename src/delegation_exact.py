"""Pure-integer and exact-rational arithmetic engine for downward-closed delegation bounds.

Implements exact rational evaluations for Abdi, Banihashem, Hajiaghayi, and Mittal
(arXiv:2611.33095, Nov 24, 2026), "Improved Downward-Closed Delegation Bounds":
  1. Five-item knapsack impossibility (Sec. 3: Prop. 3.1, Thm. 3.2, Prop. 3.3);
  2. Algorithm 1 single-threshold guarantee & Efron-Stein clipped variance (Sec. 4);
  3. Lemma 4.4 exact Bernstein degree-7 polynomial positivity & Taylor log(13/2) < 15/8;
  4. Algorithm 2 capped seed-reserve menus & Lemma 6.3 profile relations (Sec. 5-6).

Zero IEEE-754 arithmetic; pure stdlib int and fractions.Fraction only.
Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Dict, List, Sequence, Set, Tuple

# Degree-7 polynomial P(b) from Lemma 4.4 Eq. (4.12), coefficients in ascending powers b^0..b^7
P7_COEFFS: Tuple[int, ...] = (-72, 1345, -5459, 7546, -2948, 1795, -3593, 1242)


def frac_to_str(val: Fraction) -> str:
    if not isinstance(val, Fraction):
        raise TypeError("Expected Fraction")
    if val.denominator == 1:
        return str(val.numerator)
    return f"{val.numerator}/{val.denominator}"


def binom(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    if k == 0 or k == n:
        return 1
    k = min(k, n - k)
    num = 1
    den = 1
    for i in range(1, k + 1):
        num *= n - i + 1
        den *= i
    return num // den


def eval_p7(b: Fraction) -> Fraction:
    """Evaluate Lemma 4.4 degree-7 polynomial P(b) exactly over Q."""
    acc = Fraction(0, 1)
    p = Fraction(1, 1)
    for c in P7_COEFFS:
        acc += Fraction(c, 1) * p
        p *= b
    return acc


def bernstein_coeffs_on_interval(left: Fraction, right: Fraction) -> List[Fraction]:
    """Compute exact rational Bernstein coefficients beta_0..beta_7 of P(left + (right-left)*v)."""
    d = right - left
    # Expand P(left + d*v) = sum_{j=0}^7 p_j v^j
    pj: List[Fraction] = [Fraction(0, 1)] * 8
    for m, coeff in enumerate(P7_COEFFS):
        c_frac = Fraction(coeff, 1)
        for j in range(m + 1):
            term = c_frac * Fraction(binom(m, j), 1) * (left ** (m - j)) * (d ** j)
            pj[j] += term
    # Convert power basis p_j to Bernstein basis beta_k = sum_{j=0}^k (C(k,j)/C(7,j)) * p_j
    betas: List[Fraction] = []
    for k in range(8):
        bk = Fraction(0, 1)
        for j in range(k + 1):
            bk += Fraction(binom(k, j), binom(7, j)) * pj[j]
        betas.append(bk)
    return betas


def exp_taylor_7_minus_13_2() -> Fraction:
    """Exact sum_{k=0}^7 (15/8)^k / k! - 13/2 from Lemma 4.4 Eq. (4.11)."""
    x = Fraction(15, 8)
    total = Fraction(0, 1)
    term = Fraction(1, 1)
    for k in range(8):
        if k > 0:
            term = term * x / Fraction(k, 1)
        total += term
    return total - Fraction(13, 2)


def is_downward_closed(feasible: Sequence[Set[int]]) -> bool:
    """Verify nonempty downward-closed family F (every subset of S in F is also in F)."""
    if not feasible:
        return False
    fset = {frozenset(s) for s in feasible}
    if frozenset() not in fset:
        return False
    for s in fset:
        for i in s:
            if (s - {i}) not in fset:
                return False
    return True


def enumerate_product_distribution(
    item_supports: Sequence[Sequence[Tuple[Fraction, Fraction]]],
) -> List[Tuple[Fraction, Tuple[Fraction, ...]]]:
    """Enumerate all joint realizations (prob, (x_0, ..., x_{n-1})) for independent items."""
    out: List[Tuple[Fraction, Tuple[Fraction, ...]]] = []
    for combo in product(*item_supports):
        prob = Fraction(1, 1)
        vals: List[Fraction] = []
        for v, p in combo:
            prob *= p
            vals.append(v)
        out.append((prob, tuple(vals)))
    return out


def offline_optimum(vals: Sequence[Fraction], feasible: Sequence[Set[int]], cap: Fraction | None = None) -> Fraction:
    """Compute W(x) or Z_c(x) = max_{S in F} sum_{i in S} min(x_i, c)."""
    best = Fraction(0, 1)
    for s in feasible:
        tot = Fraction(0, 1)
        for i in s:
            v = vals[i] if cap is None or vals[i] <= cap else cap
            tot += v
        if tot > best:
            best = tot
    return best


def compute_excess_e(item_supports: Sequence[Sequence[Tuple[Fraction, Fraction]]], z: Fraction) -> Fraction:
    """Compute e(z) = sum_i E[(X_i - z)_+] exactly over Q."""
    tot = Fraction(0, 1)
    for supp in item_supports:
        for v, p in supp:
            if v > z:
                tot += p * (v - z)
    return tot


def menu_score_realization(
    vals: Sequence[Fraction],
    feasible: Sequence[Set[int]],
    accepted_sets: Sequence[Set[int]],
) -> Fraction:
    """Compute exact score b_M(x) = min{x(S) : S inclusion-maximal in A_M(x)} (0 if empty)."""
    nonempty = [frozenset(s) for s in accepted_sets if len(s) > 0]
    if not nonempty:
        return Fraction(0, 1)
    maximal = [s for s in nonempty if not any(s < other for other in nonempty)]
    return min(sum((vals[i] for i in s), Fraction(0, 1)) for s in maximal)


def is_seed_at_level(
    s: Set[int],
    clipped_vals: Sequence[Fraction],
    level_t: Fraction,
) -> bool:
    """Check Algorithm 2 Eq. (5.1): nonempty S with w(S) >= t and w(S) - w_i < t for all i in S."""
    if not s:
        return False
    tot = sum((clipped_vals[i] for i in s), Fraction(0, 1))
    if tot < level_t:
        return False
    return all(tot - clipped_vals[i] < level_t for i in s)


def algorithm2_accepts(
    s: Set[int],
    vals: Sequence[Fraction],
    cap_c: Fraction,
    cutoffs: Sequence[Fraction],
    open_cutoffs: Sequence[bool],
    body_type: str,
    level_t: Fraction,
    upper_u: Fraction | None = None,
    reserve_a: Fraction | None = None,
) -> bool:
    """Exact Algorithm 2 acceptance test on a nonempty feasible report (S, x_S)."""
    if not s:
        return False
    if len(s) == 1:
        i = next(iter(s))
        if open_cutoffs[i]:
            if vals[i] > cutoffs[i]:
                return True
        else:
            if vals[i] >= cutoffs[i]:
                return True
    w = [v if v <= cap_c else cap_c for v in vals]
    w_s = sum((w[i] for i in s), Fraction(0, 1))
    if body_type == "threshold":
        return w_s >= level_t
    if body_type == "seeds_upper":
        assert upper_u is not None
        return is_seed_at_level(s, w, level_t) or w_s >= upper_u
    if body_type == "seeds_reserve":
        assert reserve_a is not None
        # Check all nonempty subsets P subseteq S (feasible by downward closure)
        elems = sorted(s)
        n = len(elems)
        for mask in range(1, 1 << n):
            p_set = {elems[j] for j in range(n) if (mask >> j) & 1}
            if is_seed_at_level(p_set, w, level_t):
                if len(p_set) == n:
                    return True
                w_p = sum((w[i] for i in p_set), Fraction(0, 1))
                w_min = min(w[i] for i in p_set)
                b_p = level_t + w_min - w_p
                w_rem = w_s - w_p
                if w_rem >= reserve_a * b_p:
                    return True
        return False
    raise ValueError(f"Unknown body_type: {body_type}")
