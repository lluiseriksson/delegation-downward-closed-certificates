"""Generate 3 publication-quality 300-DPI figures for Paper 54 (Downward-Closed Delegation Bounds).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RES_DIR = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 8.6,
    "axes.titlesize": 9.2,
    "axes.labelsize": 8.6,
    "xtick.labelsize": 7.6,
    "ytick.labelsize": 7.6,
    "legend.fontsize": 6.8,
    "figure.dpi": 300,
    "savefig.dpi": 300,
})


def make_fig1() -> None:
    d2 = json.loads((RES_DIR / "exp2_impossibility_sweep.json").read_text(encoding="utf-8"))
    sweep = d2["sweep"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))

    # Panel (a): Universal delegation guarantee spectrum (0.1098 -> 3/10 -> 29/70 vs upper bounds < 1/2)
    labels = [
        "Prior\n0.110",
        "Alg. 1\n3/10",
        "Thm. 5.1\n29/70",
        "App. A\n0.481",
        "Prop. 3.3\n30/61",
        "Prop. 3.1\n500/1011",
        "Matroid\n1/2",
    ]
    vals = [0.1098, 0.3, 29.0 / 70.0, 0.48105, 30.0 / 61.0, 500.0 / 1011.0, 0.5]
    cols = ["#7f8c8d", "#117a65", "#1f618d", "#b7950b", "#d35400", "#922b21", "#34495e"]
    x = np.arange(len(labels))
    ax1.bar(x, vals, color=cols, width=0.60, edgecolor="#222222", lw=0.5)
    ax1.axhline(0.5, color="#34495e", ls=":", lw=1.0)
    for i, v in enumerate(vals):
        ax1.text(i, v + 0.012, f"{v:.3f}", ha="center", va="bottom", fontsize=6.1, fontweight="bold")
    ax1.set_xticks(x)
    ax1.set_xticklabels(labels, fontsize=5.8)
    ax1.set_ylim(0.0, 0.58)
    ax1.set_ylabel("Approximation ratio")
    ax1.set_title("(a) Downward-closed delegation sandwich")
    ax1.grid(True, axis="y", linestyle="--", alpha=0.35)

    # Panel (b): 5-item knapsack ratio convergence to 30/61 as jackpot prob eps -> 0
    eps_v = [r["eps_val"] for r in sweep]
    det_v = [r["det_val"] for r in sweep]
    rnd_v = [r["rand_val"] for r in sweep]
    ax2.semilogx(eps_v, rnd_v, "s-", color="#922b21", lw=1.8, ms=4.5, label=r"Rand. upper bound ($\eta=\varepsilon$)")
    ax2.semilogx(eps_v, det_v, "o-", color="#1f618d", lw=1.8, ms=4.5, label="Det. exact optimum $10/V$")
    ax2.axhline(30.0 / 61.0, color="#117a65", ls="--", lw=1.3, label=r"Universal limit $30/61 \approx 0.4918$")
    ax2.axhline(0.5, color="#555555", ls=":", lw=1.1, label="Matroid barrier $1/2$")
    ax2.invert_xaxis()
    ax2.set_ylim(0.489, 0.526)
    ax2.set_xlabel(r"Jackpot probability $\varepsilon$ (decreasing $\rightarrow$)")
    ax2.set_ylabel("5-item knapsack ratio")
    ax2.set_title(r"(b) Convergence to $30/61 < 1/2$ (Sec. 3)")
    ax2.grid(True, which="major", linestyle="--", alpha=0.35)
    ax2.legend(loc="upper right", frameon=True, fontsize=6.4)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig1_delegation_sandwich.png", bbox_inches="tight")
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((RES_DIR / "exp3_bernstein_profile.json").read_text(encoding="utf-8"))
    samps = d3["samples"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75))

    # Panel (a): Degree-7 polynomial P(b) on [2/13, 2/3] with Bernstein lower bounds
    bs = [r["b_val"] for r in samps]
    ps = [r["P_val"] for r in samps]
    ax1.plot(bs, ps, color="#1f618d", lw=2.1, label=r"Exact $P(b)$ (deg. 7)")
    ax1.hlines(d3["left_min_val"], 2.0 / 13.0, 0.4, colors="#117a65", linestyles="--", lw=1.7,
               label=r"$\min\beta_k = 447966/78125$ on $[2/13,2/5]$")
    ax1.hlines(d3["right_min_val"], 0.4, 2.0 / 3.0, colors="#922b21", linestyles="--", lw=1.7,
               label=r"$\min\beta_k = 6518/118125$ on $[2/5,2/3]$")
    ax1.hlines(129.0 / 128.0, 0.25, 0.5, colors="#7d3c98", linestyles=":", lw=1.5,
               label=r"$\min\beta_k = 129/128$ on $[1/4,1/2]$")
    ax1.hlines(141.0 / 32.0, 0.5, 2.0 / 3.0, colors="#b7950b", linestyles="-.", lw=1.5,
               label=r"$\min\beta_k = 141/32$ on $[1/2,2/3]$")
    ax1.scatter([0.46, 0.5, 2.0 / 3.0], [2.66, 141.0 / 32.0, 33250.0 / 729.0],
                color="#1f618d", s=16, zorder=5)
    ax1.annotate(r"$\min P \approx 2.66$", xy=(0.46, 2.66), xytext=(0.48, 1.35),
                 arrowprops=dict(arrowstyle="->", color="#1f618d", lw=0.8), fontsize=6.0, color="#1f618d")
    ax1.annotate(r"$P(\frac{2}{3})\approx 45.6$", xy=(2.0 / 3.0, 33250.0 / 729.0), xytext=(0.50, 36.0),
                 arrowprops=dict(arrowstyle="->", color="#1f618d", lw=0.8), fontsize=6.0, color="#1f618d")
    ax1.axvline(0.4, color="#555555", ls=":", lw=0.9)
    ax1.set_yscale("log")
    ax1.set_ylim(0.03, 95.0)
    ax1.set_xlabel(r"Parameter $b \in [2/13, 2/3]$")
    ax1.set_ylabel(r"$P(b)$ & Bernstein min (log)")
    ax1.set_title("(a) Lemma 4.4 Bernstein positivity proof")
    ax1.grid(True, which="major", linestyle="--", alpha=0.35)
    ax1.legend(loc="lower left", frameon=True, fontsize=5.4, framealpha=0.92)

    # Panel (b): Exact Bernstein coefficients beta_0..beta_7 on both intervals
    from fractions import Fraction
    left_b = [float(Fraction(x)) for x in d3["left_betas"]]
    right_b = [float(Fraction(x)) for x in d3["right_betas"]]
    ks = np.arange(8)
    w = 0.36
    ax2.bar(ks - w / 2, left_b, width=w, color="#117a65", label=r"$[2/13, 2/5]$")
    ax2.bar(ks + w / 2, right_b, width=w, color="#b7950b", label=r"$[2/5, 2/3]$")
    ax2.set_yscale("log")
    ax2.set_ylim(0.03, 180.0)
    ax2.set_xticks(ks)
    ax2.set_xlabel("Bernstein basis index $k$")
    ax2.set_ylabel(r"Exact coefficient $\beta_k > 0$ (log)")
    ax2.set_title(r"(b) All 16 Bernstein coefficients $> 0$")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    ax2.legend(loc="upper center", ncol=2, frameon=True, fontsize=6.8)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig2_bernstein_positivity.png", bbox_inches="tight")
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RES_DIR / "exp1_certified_atlas.json").read_text(encoding="utf-8"))["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.95), gridspec_kw={"width_ratios": [1.55, 1.0]})

    stems = [r["name"] for r in d1]
    ms = [r["verify_ms"] for r in d1]
    mode_colors = {
        "knapsack_impossibility_cert": "#1f618d",
        "single_threshold_guarantee_cert": "#117a65",
        "bernstein_analytic_cert": "#b7950b",
        "capped_menu_seed_profile_cert": "#922b21",
    }
    cols = [mode_colors[r["mode"]] for r in d1]

    y = np.arange(len(stems))
    ax1.barh(y, ms, color=cols, height=0.72)
    ax1.set_yticks(y)
    ax1.set_yticklabels(stems, fontsize=6.2)
    ax1.invert_yaxis()
    ax1.set_xlabel("Zero-float exact replay latency (ms)")
    ax1.set_title("(a) Replay time across all 16 certificates")
    ax1.grid(True, axis="x", linestyle="--", alpha=0.35)

    groups = [
        ("AST/Uni\n(16)", 16, "#34495e"),
        ("M1\n(11)", 11, "#1f618d"),
        ("M2\n(11)", 11, "#117a65"),
        ("M3\n(11)", 11, "#b7950b"),
        ("M4\n(11)", 11, "#922b21"),
    ]
    gx = np.arange(len(groups))
    ax2.bar(gx, [g[1] for g in groups], color=[g[2] for g in groups], width=0.58)
    ax2.set_xticks(gx)
    ax2.set_xticklabels([g[0] for g in groups], fontsize=6.8)
    ax2.set_ylabel("Rejected live forgeries")
    ax2.set_ylim(0, 19.5)
    ax2.set_title("(b) 60/60 red-team rejections")
    ax2.grid(True, axis="y", linestyle="--", alpha=0.35)
    for idx, g in enumerate(groups):
        ax2.text(idx, g[1] + 0.4, f"{g[1]}/{g[1]}", ha="center", va="bottom", fontsize=6.8, fontweight="bold")

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig3_atlas_and_redteam.png", bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated 3 publication-quality 300-DPI figures in paper/figures/.")


if __name__ == "__main__":
    main()
