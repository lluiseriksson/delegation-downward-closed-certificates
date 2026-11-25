# Constructive Lean 4 Formalization and Exact-Rational Certificates for Improved Downward-Closed Delegation Bounds

**Author:** Lluis Eriksson (Independent Researcher; prepared with transparent AI assistance via Google Antigravity)
**Licenses:** Code, Lean 4 proofs, and certificates under MIT (`LICENSE`); manuscript and figures under CC-BY-4.0.
**Target Literature:** Hamed Abdi, Kiarash Banihashem, MohammadTaghi Hajiaghayi, and Danny Mittal, *"Improved Downward-Closed Delegation Bounds"*, `arXiv:2611.33095` (November 24, 2026).

## Overview

This repository provides a standalone, zero-dependency **Lean 4.35.0** formalization and a zero-floating-point exact-rational (`DELEG-DC-CERT-1.0`) certificate auditor covering the deterministic impossibility, single-threshold, Efron–Stein, degree-7 Bernstein positivity, seed-reserve menu, safe-singleton normalization, and profile-inequality core of `arXiv:2611.33095`.

### Key Verified Artifacts
- **Lean 4.35.0 Kernel (`lean/DelegationBounds.lean`, `lean/AuditAxioms.lean`):** 18 constructive theorems, 0 `sorry`, 0 warnings, 0 `Classical.choice` (`1` zero-axiom, `1` `[propext]`, `16` `[propext, Quot.sound]`).
- **Zero-Float Exact-$\mathbb{Q}$ Verifier (`src/delegation_exact.py`, `src/delegation_certifier.py`):** Four strict modes (`knapsack_impossibility_cert`, `single_threshold_guarantee_cert`, `bernstein_analytic_cert`, `capped_menu_seed_profile_cert`) hardened against IEEE-754 tokens, Unicode non-ASCII digits, unreduced rationals, oversized strings, booleans-as-integers, duplicate atoms/probes, and deep nesting.
- **16 Canonical Certificates (`certificates/*.cert.json`):** 4 per mode, all replaying in `0.254`–`2.272 ms`.
- **60/60 Red-Team Forgery Suite (`tests/test_suite.py`):** 63 total `pytest` checks including 60 live adversarial mutations and 2 raw JSON IEEE-754/`NaN` rejections.
- **SHA-256 Manifest (`SHA256_MANIFEST.json`):** Exact integrity locking across all 39 tracked repository artifacts.

## Reproducing All Checks

```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
