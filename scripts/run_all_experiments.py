"""Generate all 16 canonical DELEG-DC-CERT-1.0 certificates and 4 experiment JSONs for Paper 54.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence, Set, Tuple

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.delegation_certifier import SCHEMA_ID, verify_certificate_file
from src.delegation_exact import (
    algorithm2_accepts,
    bernstein_coeffs_on_interval,
    compute_excess_e,
    enumerate_product_distribution,
    eval_p7,
    exp_taylor_7_minus_13_2,
    frac_to_str,
    is_seed_at_level,
    menu_score_realization,
    offline_optimum,
)

CERT_DIR = ROOT / "certificates"
RES_DIR = ROOT / "results"
CERT_DIR.mkdir(parents=True, exist_ok=True)
RES_DIR.mkdir(parents=True, exist_ok=True)


def _make_mode1_cert(name: str, eps: Fraction, eta: Fraction) -> Dict[str, Any]:
    V = Fraction(9, 1) + (Fraction(1, 1) - eps) * Fraction(34, 3)
    det_max = Fraction(10, 1)
    c1 = Fraction(10, 1) + Fraction(20, 9) * (Fraction(1, 1) - eps) * eta
    c2 = Fraction(10, 1) + Fraction(14, 9) * (Fraction(1, 1) - eps) * eta
    return {
        "schema": SCHEMA_ID,
        "mode": "knapsack_impossibility_cert",
        "name": name,
        "payload": {
            "jackpot_prob": frac_to_str(eps),
            "eta": frac_to_str(eta),
            "expected_V": frac_to_str(V),
            "expected_det_max": frac_to_str(det_max),
            "expected_det_ratio": frac_to_str(det_max / V),
            "expected_rand_case1_bound": frac_to_str(c1),
            "expected_rand_case2_bound": frac_to_str(c2),
            "expected_rand_ratio": frac_to_str(c1 / V),
        },
    }


def _make_mode2_cert(
    name: str,
    n: int,
    feasible: Sequence[Set[int]],
    supports: Sequence[Sequence[Tuple[Fraction, Fraction]]],
    z: Fraction,
    c: Fraction,
) -> Dict[str, Any]:
    joint = enumerate_product_distribution(supports)
    V = sum((pr * offline_optimum(vals, feasible) for pr, vals in joint), Fraction(0, 1))
    p_ge_z = sum((pr for pr, vals in joint if offline_optimum(vals, feasible) >= z), Fraction(0, 1))
    e_z = compute_excess_e(supports, z)
    B_z = z * p_ge_z + e_z * (Fraction(1, 1) - p_ge_z)
    exp_score = Fraction(0, 1)
    for pr, vals in joint:
        acc = [s for s in feasible if len(s) > 0 and sum((vals[i] for i in s), Fraction(0, 1)) >= z]
        exp_score += pr * menu_score_realization(vals, feasible, acc)
    z_vals = [(pr, offline_optimum(vals, feasible, cap=c)) for pr, vals in joint]
    mu_c = sum((pr * zv for pr, zv in z_vals), Fraction(0, 1))
    var_c = sum((pr * (zv - mu_c) * (zv - mu_c) for pr, zv in z_vals), Fraction(0, 1))
    return {
        "schema": SCHEMA_ID,
        "mode": "single_threshold_guarantee_cert",
        "name": name,
        "payload": {
            "num_items": n,
            "feasible_family": [sorted(s) for s in feasible],
            "item_supports": [
                [{"value": frac_to_str(v), "prob": frac_to_str(pr)} for v, pr in supp]
                for supp in supports
            ],
            "threshold_z": frac_to_str(z),
            "clip_c": frac_to_str(c),
            "expected_V": frac_to_str(V),
            "expected_B_z": frac_to_str(B_z),
            "expected_menu_score": frac_to_str(exp_score),
            "expected_clipped_mean": frac_to_str(mu_c),
            "expected_clipped_var": frac_to_str(var_c),
        },
    }


def _make_mode3_cert(name: str, left: Fraction, right: Fraction) -> Dict[str, Any]:
    betas = bernstein_coeffs_on_interval(left, right)
    mid = (left + right) / Fraction(2, 1)
    q1 = (left + mid) / Fraction(2, 1)
    q3 = (mid + right) / Fraction(2, 1)
    return {
        "schema": SCHEMA_ID,
        "mode": "bernstein_analytic_cert",
        "name": name,
        "payload": {
            "interval_left": frac_to_str(left),
            "interval_right": frac_to_str(right),
            "expected_exp_gap": frac_to_str(exp_taylor_7_minus_13_2()),
            "expected_case1_gap": "168034/70785",
            "expected_bernstein_coeffs": [frac_to_str(b) for b in betas],
            "expected_min_beta": frac_to_str(min(betas)),
            "probe_points": [frac_to_str(left), frac_to_str(q1), frac_to_str(mid), frac_to_str(q3), frac_to_str(right)],
        },
    }


def _make_mode4_cert(
    name: str,
    n: int,
    feasible: Sequence[Set[int]],
    supports: Sequence[Sequence[Tuple[Fraction, Fraction]]],
    cap_c: Fraction,
    cutoffs: Sequence[Fraction],
    open_cutoffs: Sequence[bool],
    body_type: str,
    level_t: Fraction,
    upper_u: Fraction | None,
    reserve_a: Fraction | None,
    profile_levels: Sequence[Fraction],
) -> Dict[str, Any]:
    joint = enumerate_product_distribution(supports)
    V = sum((pr * offline_optimum(vals, feasible) for pr, vals in joint), Fraction(0, 1))
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
            if algorithm2_accepts(s, vals, cap_c, cutoffs, open_cutoffs, body_type, level_t, upper_u, reserve_a):
                acc.append(s)
        exp_score += pr * menu_score_realization(vals, feasible, acc)
    beats = exp_score * Fraction(70, 1) > Fraction(29, 1) * V
    return {
        "schema": SCHEMA_ID,
        "mode": "capped_menu_seed_profile_cert",
        "name": name,
        "payload": {
            "num_items": n,
            "feasible_family": [sorted(s) for s in feasible],
            "item_supports": [
                [{"value": frac_to_str(v), "prob": frac_to_str(pr)} for v, pr in supp]
                for supp in supports
            ],
            "cap_c": frac_to_str(cap_c),
            "cutoffs": [frac_to_str(d) for d in cutoffs],
            "open_cutoffs": list(open_cutoffs),
            "body_type": body_type,
            "level_t": frac_to_str(level_t),
            "upper_u": None if upper_u is None else frac_to_str(upper_u),
            "reserve_a": None if reserve_a is None else frac_to_str(reserve_a),
            "profile_levels": [frac_to_str(lv) for lv in profile_levels],
            "expected_V": frac_to_str(V),
            "expected_menu_score": frac_to_str(exp_score),
            "expected_beats_29_70": beats,
            "expected_seed_count": seed_hits,
        },
    }


def main() -> None:
    # Reusable small downward-closed families (non-matroid knapsack & independent-set families!)
    # Family A: 4-item knapsack (weights 1,1,2,2; cap 3) -> maximal sets {0,1}, {0,2}, {0,3}, {1,2}, {1,3}
    fam_knap4 = [set(), {0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}]
    supp_knap4 = [
        [(Fraction(2, 1), Fraction(1, 2)), (Fraction(0, 1), Fraction(1, 2))],
        [(Fraction(2, 1), Fraction(1, 2)), (Fraction(0, 1), Fraction(1, 2))],
        [(Fraction(3, 1), Fraction(1, 3)), (Fraction(1, 1), Fraction(2, 3))],
        [(Fraction(5, 1), Fraction(1, 4)), (Fraction(0, 1), Fraction(3, 4))],
    ]
    # Family B: 5-item knapsack of Section 3 (A,B,E,C,J)
    fam_sec3 = [set(), {0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}]
    supp_sec3 = [
        [(Fraction(9, 1), Fraction(1, 3)), (Fraction(0, 1), Fraction(2, 3))],
        [(Fraction(9, 1), Fraction(1, 3)), (Fraction(0, 1), Fraction(2, 3))],
        [(Fraction(3, 1), Fraction(1, 1))],
        [(Fraction(10, 1), Fraction(1, 1))],
        [(Fraction(900, 1), Fraction(1, 100)), (Fraction(0, 1), Fraction(99, 100))],
    ]
    # Family C: 4-vertex path P_4 independent sets ({0,2}, {0,3}, {1,3})
    fam_p4 = [set(), {0}, {1}, {2}, {3}, {0, 2}, {0, 3}, {1, 3}]
    supp_p4 = [
        [(Fraction(3, 1), Fraction(1, 2)), (Fraction(1, 1), Fraction(1, 2))],
        [(Fraction(4, 1), Fraction(1, 3)), (Fraction(0, 1), Fraction(2, 3))],
        [(Fraction(3, 1), Fraction(1, 2)), (Fraction(0, 1), Fraction(1, 2))],
        [(Fraction(6, 1), Fraction(1, 4)), (Fraction(1, 1), Fraction(3, 4))],
    ]
    # Family D: 3-item cardinality-2 with safe singleton s0=1 (normalized style)
    fam_norm = [set(), {0}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}]
    supp_norm = [
        [(Fraction(1, 1), Fraction(1, 1))],  # safe singleton s0 = 1
        [(Fraction(3, 2), Fraction(1, 2)), (Fraction(1, 2), Fraction(1, 2))],
        [(Fraction(2, 1), Fraction(1, 3)), (Fraction(1, 2), Fraction(2, 3))],
        [(Fraction(4, 1), Fraction(1, 4)), (Fraction(0, 1), Fraction(3, 4))],
    ]

    certs: List[Dict[str, Any]] = [
        # Mode 1: Section 3 Five-Item Knapsack Impossibility (4 certificates)
        _make_mode1_cert("knap5_sec3_canonical_eps100", Fraction(1, 100), Fraction(1, 100)),
        _make_mode1_cert("knap5_sec3_eps50_eta100", Fraction(1, 50), Fraction(1, 100)),
        _make_mode1_cert("knap5_sec3_eps200_eta200", Fraction(1, 200), Fraction(1, 200)),
        _make_mode1_cert("knap5_sec3_limit_eps1000", Fraction(1, 1000), Fraction(1, 1000)),
        # Mode 2: Section 4 Single-Threshold & Efron-Stein Certificates (4 certificates)
        _make_mode2_cert("thresh_knap4_z3", 4, fam_knap4, supp_knap4, Fraction(3, 1), Fraction(3, 2)),
        _make_mode2_cert("thresh_sec3_z10", 5, fam_sec3, supp_sec3, Fraction(10, 1), Fraction(15, 1)),
        _make_mode2_cert("thresh_p4_indset_z4", 4, fam_p4, supp_p4, Fraction(4, 1), Fraction(3, 1)),
        _make_mode2_cert("thresh_norm_safe_z2", 4, fam_norm, supp_norm, Fraction(2, 1), Fraction(3, 2)),
        # Mode 3: Lemma 4.4 Exact Bernstein Degree-7 Positivity Certificates (4 certificates)
        _make_mode3_cert("bernstein_left_2_13_to_2_5", Fraction(2, 13), Fraction(2, 5)),
        _make_mode3_cert("bernstein_right_2_5_to_2_3", Fraction(2, 5), Fraction(2, 3)),
        _make_mode3_cert("bernstein_mid_1_4_to_1_2", Fraction(1, 4), Fraction(1, 2)),
        _make_mode3_cert("bernstein_upper_1_2_to_2_3", Fraction(1, 2), Fraction(2, 3)),
        # Mode 4: Algorithm 2 Capped Seed-Reserve Menus & Lemma 6.3 Profiles (4 certificates)
        _make_mode4_cert(
            "alg2_thresh_knap4", 4, fam_knap4, supp_knap4,
            Fraction(2, 1), [Fraction(3, 1)] * 4, [True] * 4,
            "threshold", Fraction(3, 1), None, None,
            [Fraction(1, 1), Fraction(2, 1), Fraction(3, 1), Fraction(4, 1)],
        ),
        _make_mode4_cert(
            "alg2_seeds_upper_p4", 4, fam_p4, supp_p4,
            Fraction(3, 1), [Fraction(5, 1)] * 4, [False] * 4,
            "seeds_upper", Fraction(4, 1), Fraction(5, 1), None,
            [Fraction(1, 1), Fraction(2, 1), Fraction(4, 1), Fraction(6, 1)],
        ),
        _make_mode4_cert(
            "alg2_seeds_reserve_norm", 4, fam_norm, supp_norm,
            Fraction(3, 2), [Fraction(3, 1)] * 4, [True] * 4,
            "seeds_reserve", Fraction(2, 1), None, Fraction(1, 2),
            [Fraction(1, 1), Fraction(3, 2), Fraction(2, 1), Fraction(3, 1)],
        ),
        _make_mode4_cert(
            "alg2_seeds_reserve_sec3", 5, fam_sec3, supp_sec3,
            Fraction(9, 1), [Fraction(10, 1)] * 5, [False] * 5,
            "seeds_reserve", Fraction(12, 1), None, Fraction(1, 3),
            [Fraction(3, 1), Fraction(9, 1), Fraction(12, 1), Fraction(18, 1)],
        ),
    ]

    atlas_rows = []
    for cert in certs:
        fname = f"{cert['name']}.cert.json"
        fpath = CERT_DIR / fname
        fpath.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        # Time 20-run average for stable low-noise latency
        t0 = time.perf_counter()
        summary = verify_certificate_file(fpath)
        for _ in range(19):
            verify_certificate_file(fpath)
        elapsed_ms = (time.perf_counter() - t0) * 1000.0 / 20.0
        atlas_rows.append({
            "file": fname,
            "name": cert["name"],
            "mode": cert["mode"],
            "verify_ms": round(elapsed_ms, 4),
            "summary": summary,
        })

    # Exp 1: Certified Atlas
    (RES_DIR / "exp1_certified_atlas.json").write_text(
        json.dumps({"schema": SCHEMA_ID, "count": len(atlas_rows), "rows": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 2: Universal Bound Sandwich & Section 3 Impossibility Limit Sweep
    eps_sweep = [Fraction(1, 10), Fraction(1, 20), Fraction(1, 50), Fraction(1, 100), Fraction(1, 200), Fraction(1, 500), Fraction(1, 1000)]
    sweep_rows = []
    for eps in eps_sweep:
        V = Fraction(9, 1) + (Fraction(1, 1) - eps) * Fraction(34, 3)
        det_r = Fraction(10, 1) / V
        rand_r = (Fraction(10, 1) + Fraction(20, 9) * (Fraction(1, 1) - eps) * eps) / V
        sweep_rows.append({
            "eps": frac_to_str(eps),
            "eps_val": float(eps),
            "det_ratio": frac_to_str(det_r),
            "det_val": round(float(det_r), 6),
            "rand_ratio": frac_to_str(rand_r),
            "rand_val": round(float(rand_r), 6),
        })
    (RES_DIR / "exp2_impossibility_sweep.json").write_text(
        json.dumps(
            {
                "limit_30_61": round(30.0 / 61.0, 6),
                "prior_lower": 0.1098,
                "single_thresh_lower": 0.3,
                "main_lower_29_70": round(29.0 / 70.0, 6),
                "comp_upper": 0.48105,
                "matroid_opt": 0.5,
                "sweep": sweep_rows,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    # Exp 3: Lemma 4.4 Exact Degree-7 Polynomial P(b) & Bernstein Lower Hull Profile
    b_left = bernstein_coeffs_on_interval(Fraction(2, 13), Fraction(2, 5))
    b_right = bernstein_coeffs_on_interval(Fraction(2, 5), Fraction(2, 3))
    p7_samples = []
    for k_step in range(0, 41):
        b = Fraction(2, 13) + (Fraction(2, 3) - Fraction(2, 13)) * Fraction(k_step, 40)
        p7_samples.append({"b": frac_to_str(b), "b_val": round(float(b), 5), "P_val": round(float(eval_p7(b)), 5)})
    (RES_DIR / "exp3_bernstein_profile.json").write_text(
        json.dumps(
            {
                "left_interval": "[2/13, 2/5]",
                "left_betas": [frac_to_str(x) for x in b_left],
                "left_min": frac_to_str(min(b_left)),
                "left_min_val": round(float(min(b_left)), 6),
                "right_interval": "[2/5, 2/3]",
                "right_betas": [frac_to_str(x) for x in b_right],
                "right_min": frac_to_str(min(b_right)),
                "right_min_val": round(float(min(b_right)), 6),
                "samples": p7_samples,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    # Exp 4: Exact Finite Instance Guarantees Summary (Modes 2 & 4)
    inst_summary = [
        {"name": r["name"], "mode": r["mode"], "ratio_val": round(float(Fraction(r["summary"]["ratio"])), 5), "ratio_exact": r["summary"]["ratio"]}
        for r in atlas_rows
        if r["mode"] in ("single_threshold_guarantee_cert", "capped_menu_seed_profile_cert")
    ]
    (RES_DIR / "exp4_instance_guarantees.json").write_text(
        json.dumps({"rows": inst_summary}, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"[PASS] Generated and verified {len(atlas_rows)}/16 certificates and 4 experiment logs.")


if __name__ == "__main__":
    main()
