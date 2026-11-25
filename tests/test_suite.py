"""Comprehensive unit, canonical-replay, and 60-attack red-team forgery suite for Paper 54.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, List, Tuple

import pytest

from src.delegation_certifier import (
    SCHEMA_ID,
    DelegationCertError,
    verify_certificate,
    verify_certificate_file,
)
from src.delegation_exact import (
    bernstein_coeffs_on_interval,
    exp_taylor_7_minus_13_2,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(stem: str) -> dict:
    return json.loads((CERT_DIR / f"{stem}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_pass() -> None:
    files = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(files) == 16
    modes = {verify_certificate_file(f)["mode"] for f in files}
    assert len(modes) == 4


def test_exact_bernstein_and_taylor_primitives() -> None:
    assert exp_taylor_7_minus_13_2() == Fraction(3772963, 234881024)
    assert min(bernstein_coeffs_on_interval(Fraction(2, 13), Fraction(2, 5))) == Fraction(447966, 78125)
    assert min(bernstein_coeffs_on_interval(Fraction(2, 5), Fraction(2, 3))) == Fraction(6518, 118125)


def _build_red_team_cases() -> List[Tuple[str, Callable[[], Any]]]:
    base1 = _load("knap5_sec3_canonical_eps100")
    base2 = _load("thresh_knap4_z3")
    base3 = _load("bernstein_left_2_13_to_2_5")
    base4 = _load("alg2_seeds_reserve_norm")
    base4u = _load("alg2_seeds_upper_p4")

    def m(base: dict, fn: Callable[[dict], None]) -> Callable[[], dict]:
        def _run() -> dict:
            c = copy.deepcopy(base)
            fn(c)
            return c
        return _run

    cases: List[Tuple[str, Callable[[], Any]]] = [
        # --- Group A: Global AST, Schema, Canonical-Rational, Unicode Hardening (16 attacks) ---
        ("A01_wrong_schema", m(base1, lambda c: c.__setitem__("schema", "DELEG-DC-CERT-2.0"))),
        ("A02_unknown_mode", m(base1, lambda c: c.__setitem__("mode", "bogus"))),
        ("A03_empty_name", m(base1, lambda c: c.__setitem__("name", ""))),
        ("A04_whitespace_name", m(base1, lambda c: c.__setitem__("name", " x "))),
        ("A05_extra_root_key", m(base1, lambda c: c.__setitem__("extra", 1))),
        ("A06_missing_payload", m(base1, lambda c: c.pop("payload"))),
        ("A07_float_in_payload", m(base1, lambda c: c["payload"].__setitem__("eta", 0.01))),
        ("A08_bool_as_int", m(base2, lambda c: c["payload"].__setitem__("num_items", True))),
        ("A09_unreduced_frac", m(base1, lambda c: c["payload"].__setitem__("eta", "2/200"))),
        ("A10_denom_one", m(base1, lambda c: c["payload"].__setitem__("expected_det_max", "10/1"))),
        ("A11_zero_as_0_over_2", m(base2, lambda c: c["payload"]["item_supports"][0][1].__setitem__("value", "0/2"))),
        ("A12_neg_zero", m(base2, lambda c: c["payload"]["item_supports"][0][1].__setitem__("value", "-0"))),
        ("A13_leading_zero", m(base1, lambda c: c["payload"].__setitem__("eta", "01/100"))),
        ("A14_unicode_superscript", m(base1, lambda c: c["payload"].__setitem__("eta", "1/10²"))),
        ("A15_unicode_arabic_digit", m(base3, lambda c: c["payload"].__setitem__("interval_left", "2/1٣"))),
        ("A16_deep_nesting_dos", lambda: {"schema": SCHEMA_ID, "mode": "knapsack_impossibility_cert", "name": "x", "payload": [[[[[[[[[[[[[[[[[[[[[1]]]]]]]]]]]]]]]]]]]]]}),

        # --- Group B: Mode 1 Knapsack Impossibility Forgeries (11 attacks) ---
        ("B01_eps_zero", m(base1, lambda c: c["payload"].__setitem__("jackpot_prob", "0"))),
        ("B02_eps_half", m(base1, lambda c: c["payload"].__setitem__("jackpot_prob", "1/2"))),
        ("B03_eta_zero", m(base1, lambda c: c["payload"].__setitem__("eta", "0"))),
        ("B04_eta_gt_1", m(base1, lambda c: c["payload"].__setitem__("eta", "3/2"))),
        ("B05_wrong_V", m(base1, lambda c: c["payload"].__setitem__("expected_V", "20"))),
        ("B06_wrong_det_max", m(base1, lambda c: c["payload"].__setitem__("expected_det_max", "11"))),
        ("B07_wrong_det_ratio", m(base1, lambda c: c["payload"].__setitem__("expected_det_ratio", "1/2"))),
        ("B08_wrong_case1", m(base1, lambda c: c["payload"].__setitem__("expected_rand_case1_bound", "10"))),
        ("B09_wrong_case2", m(base1, lambda c: c["payload"].__setitem__("expected_rand_case2_bound", "10"))),
        ("B10_wrong_rand_ratio", m(base1, lambda c: c["payload"].__setitem__("expected_rand_ratio", "1/2"))),
        ("B11_extra_payload_key", m(base1, lambda c: c["payload"].__setitem__("bonus", 0))),

        # --- Group C: Mode 2 Single-Threshold & Efron-Stein Forgeries (11 attacks) ---
        ("C01_not_downward_closed", m(base2, lambda c: c["payload"]["feasible_family"].remove([0]))),
        ("C02_duplicate_feasible_set", m(base2, lambda c: c["payload"]["feasible_family"].append([0, 1]))),
        ("C03_prob_sum_not_one", m(base2, lambda c: c["payload"]["item_supports"][0][0].__setitem__("prob", "1/3"))),
        ("C04_neg_value", m(base2, lambda c: c["payload"]["item_supports"][0][1].__setitem__("value", "-1"))),
        ("C05_duplicate_support_val", m(base2, lambda c: c["payload"]["item_supports"][0][1].__setitem__("value", "2"))),
        ("C06_zero_threshold", m(base2, lambda c: c["payload"].__setitem__("threshold_z", "0"))),
        ("C07_wrong_V", m(base2, lambda c: c["payload"].__setitem__("expected_V", "99"))),
        ("C08_wrong_B_z", m(base2, lambda c: c["payload"].__setitem__("expected_B_z", "1"))),
        ("C09_wrong_menu_score", m(base2, lambda c: c["payload"].__setitem__("expected_menu_score", "1"))),
        ("C10_wrong_clipped_mean", m(base2, lambda c: c["payload"].__setitem__("expected_clipped_mean", "1"))),
        ("C11_wrong_clipped_var", m(base2, lambda c: c["payload"].__setitem__("expected_clipped_var", "0"))),

        # --- Group D: Mode 3 Bernstein Analytic Forgeries (11 attacks) ---
        ("D01_left_below_2_13", m(base3, lambda c: c["payload"].__setitem__("interval_left", "1/10"))),
        ("D02_right_above_2_3", m(base3, lambda c: c["payload"].__setitem__("interval_right", "3/4"))),
        ("D03_inverted_interval", m(base3, lambda c: c["payload"].update({"interval_left": "2/5", "interval_right": "2/13"}))),
        ("D04_wrong_exp_gap", m(base3, lambda c: c["payload"].__setitem__("expected_exp_gap", "1/100"))),
        ("D05_wrong_case1_gap", m(base3, lambda c: c["payload"].__setitem__("expected_case1_gap", "2"))),
        ("D06_wrong_beta_len", m(base3, lambda c: c["payload"].__setitem__("expected_bernstein_coeffs", ["1"] * 7))),
        ("D07_tampered_beta_0", m(base3, lambda c: c["payload"]["expected_bernstein_coeffs"].__setitem__(0, "1"))),
        ("D08_wrong_min_beta", m(base3, lambda c: c["payload"].__setitem__("expected_min_beta", "1"))),
        ("D09_probe_outside_interval", m(base3, lambda c: c["payload"]["probe_points"].__setitem__(0, "1/2"))),
        ("D10_duplicate_probe", m(base3, lambda c: c["payload"]["probe_points"].append("2/13"))),
        ("D11_too_few_probes", m(base3, lambda c: c["payload"].__setitem__("probe_points", ["2/13"]))),

        # --- Group E: Mode 4 Capped Seed-Reserve Menu & Profile Forgeries (11 attacks) ---
        ("E01_level_le_cap", m(base4, lambda c: c["payload"].__setitem__("level_t", "3/2"))),
        ("E02_zero_cutoff", m(base4, lambda c: c["payload"]["cutoffs"].__setitem__(0, "0"))),
        ("E03_non_bool_open", m(base4, lambda c: c["payload"]["open_cutoffs"].__setitem__(0, 1))),
        ("E04_unknown_body", m(base4, lambda c: c["payload"].__setitem__("body_type", "bogus"))),
        ("E05_reserve_gt_1", m(base4, lambda c: c["payload"].__setitem__("reserve_a", "3/2"))),
        ("E06_upper_le_t", m(base4u, lambda c: c["payload"].__setitem__("upper_u", "4"))),
        ("E07_wrong_seed_count", m(base4, lambda c: c["payload"].__setitem__("expected_seed_count", 0))),
        ("E08_wrong_beats_flag", m(base4, lambda c: c["payload"].__setitem__("expected_beats_29_70", not base4["payload"]["expected_beats_29_70"]))),
        ("E09_wrong_score", m(base4, lambda c: c["payload"].__setitem__("expected_menu_score", "1"))),
        ("E10_non_increasing_levels", m(base4, lambda c: c["payload"].__setitem__("profile_levels", ["2", "1"]))),
        ("E11_oversized_rat_str", m(base4, lambda c: c["payload"].__setitem__("cap_c", "1" * 2005))),
    ]
    assert len(cases) == 60
    return cases


@pytest.mark.parametrize("attack_name,builder", _build_red_team_cases())
def test_red_team_forgery_rejected(attack_name: str, builder: Callable[[], Any]) -> None:
    with pytest.raises(DelegationCertError):
        verify_certificate(builder())


def test_raw_json_float_and_nan_rejected(tmp_path: Path) -> None:
    p1 = tmp_path / "float.cert.json"
    p1.write_text('{"schema":"DELEG-DC-CERT-1.0","mode":"knapsack_impossibility_cert","name":"f","payload":{"eta":0.01}}', encoding="utf-8")
    with pytest.raises(DelegationCertError):
        verify_certificate_file(p1)

    p2 = tmp_path / "nan.cert.json"
    p2.write_text('{"schema":"DELEG-DC-CERT-1.0","mode":"knapsack_impossibility_cert","name":"f","payload":{"eta":NaN}}', encoding="utf-8")
    with pytest.raises(DelegationCertError):
        verify_certificate_file(p2)
