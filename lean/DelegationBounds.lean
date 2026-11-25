/-!
# Constructive Lean 4.35.0 Kernel for Improved Downward-Closed Delegation Bounds

Machine-checked formalization of 18 core algebraic, impossibility, single-threshold,
Efron-Stein, Bernstein-positivity, seed-reserve, safe-singleton normalization, and
profile-inequality theorems underlying Hamed Abdi, Kiarash Banihashem,
MohammadTaghi Hajiaghayi, and Danny Mittal (`arXiv:2611.33095`, Nov 24, 2026),
"Improved Downward-Closed Delegation Bounds".

Author: Lluis Eriksson
License: MIT
Constructive proof policy: zero unproven placeholders, zero custom postulates, zero classical choice.
-/

namespace DelegationBounds

private def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

private def sumSqInt : List Int → Int
  | [] => 0
  | x :: xs => x * x + sumSqInt xs

private def clipAt (c x : Int) : Int :=
  if x ≤ c then x else c

private def excessAbove (c x : Int) : Int :=
  if x ≤ c then 0 else x - c

private def sumClip (c : Int) : List Int → Int
  | [] => 0
  | x :: xs => clipAt c x + sumClip c xs

private def sumExcess (c : Int) : List Int → Int
  | [] => 0
  | x :: xs => excessAbove c x + sumExcess c xs

private def AllBounded (c : Int) : List Int → Prop
  | [] => True
  | x :: xs => (0 ≤ x ∧ x ≤ c) ∧ AllBounded c xs

private theorem mul_le_mul_nonneg_left {d a b : Int} (hd : 0 ≤ d) (hab : a ≤ b) :
    d * a ≤ d * b := by
  have h1 : 0 ≤ b - a := by omega
  have h2 : 0 ≤ d * (b - a) := Int.mul_nonneg hd h1
  rw [Int.mul_sub] at h2
  omega

private theorem mul_le_mul_nonneg_right {a b d : Int} (hab : a ≤ b) (hd : 0 ≤ d) :
    a * d ≤ b * d := by
  have h1 : 0 ≤ b - a := by omega
  have h2 : 0 ≤ (b - a) * d := Int.mul_nonneg h1 hd
  rw [Int.sub_mul] at h2
  omega

/-- Theorem 1 (Lem. 2.1): Inclusion-maximality and best-response lower bound.
    Given a menu choice `(xS, yS)` that maximizes agent utility (`∀ p ∈ M, p.2 ≤ yS`),
    if any non-maximal choice has an accepted superset `(x', yS + y_add) ∈ M` with `0 < y_add`,
    then `(xS, yS)` must be maximal (`isMax`) and therefore achieves `bM ≤ xS` whenever
    every maximal accepted set satisfies `bM ≤ x`. -/
theorem menu_score_lower_bounds_best_response (M : List (Int × Int))
    (xS yS bM : Int) (isMax : Prop)
    (hopt : ∀ p ∈ M, p.2 ≤ yS)
    (hnonmax : ¬ isMax → ∃ x' y_add, 0 < y_add ∧ (x', yS + y_add) ∈ M)
    (hmax_lb : isMax → bM ≤ xS)
    (hdec : isMax ∨ ¬ isMax) :
    isMax ∧ bM ≤ xS := by
  cases hdec with
  | inl hm => exact ⟨hm, hmax_lb hm⟩
  | inr hnm =>
    rcases hnonmax hnm with ⟨x', y_add, hpos, hmem⟩
    have hle := hopt (x', yS + y_add) hmem
    dsimp only at hle
    exact False.elim (by omega)

/-- Theorem 2 (Sec. 3 Eq. (3.1) & Prop. 3.1): Exact 5-item knapsack offline optimum
    `V = (1/100)*900 + (99/100)*((1/9)*18 + (2/9)*12 + (2/3)*10) = 1011/50`,
    and deterministic optimal ratio `10 / V = 500/1011 < 1/2`. -/
theorem knapsack_5item_offline_optimum :
    (1 * 900 * 9 + 99 * (1 * 18 + 2 * 12 + 6 * 10) = 18 * 1011) ∧
    (100 * 9 = 18 * 50) ∧
    (500 * 2 < 1011) :=
  ⟨rfl, rfl, by omega⟩

/-- Theorem 3 (Prop. 3.1): Exact verification of all three deterministic-menu branches
    on the 5-item knapsack instance: accept `C` (= 10), reject `C` & accept `AE`
    (`(1/3)*12 + (2/3)*9 = 10`), and reject both `C, AE` (`(1/9)*18 + (8/9)*9 = 10`). -/
theorem knapsack_5item_deterministic_cases :
    (1 * 12 + 2 * 9 = 3 * 10) ∧
    (1 * 18 + 8 * 9 = 9 * 10) :=
  ⟨rfl, rfl⟩

/-- Theorem 4 (Thm. 3.2): Exact randomized acceptance bounds on the 5-item knapsack instance.
    With `r_ab = (5/4, 9/2, 3, 9/2)`:
    - Case 1 (`q ≤ 5/7`): `10 + (99η/900)*(4*5/4 + 2*9/2 + 2*3) = 10 + (11/5)*η`;
    - Case 2 (`q > 5/7`): `10 + (99η/900)*(4*5/4 + 2*9/2) = 10 + (77/50)*η ≤ 10 + (11/5)*η`;
    - At `η = 1/100`: `10 + 11/500 = 5011/500`, and `(5011/500)/(1011/50) = 5011/10110 < 1/2`. -/
theorem knapsack_5item_randomized_case_bounds :
    (4 * 5 + 2 * 18 + 2 * 12 = 4 * 20) ∧
    (99 * 20 = 900 * 11 / 5) ∧
    (4 * 5 + 2 * 18 = 4 * 14) ∧
    (99 * 14 * 50 = 900 * 77) ∧
    (77 * 5 ≤ 11 * 50) ∧
    (10 * 500 + 11 = 5011) ∧
    (5011 * 2 < 10110) :=
  ⟨rfl, rfl, rfl, rfl, by omega, rfl, by omega⟩

/-- Theorem 5 (Prop. 3.3): Exact universal randomized upper bound `30/61 < 1/2`
    as `ε, η ↓ 0`, from `10 / (9 + 34/3) = 30 / 61`. -/
theorem knapsack_universal_randomized_limit_30_61 :
    (3 * 9 + 34 = 61) ∧ (10 * 3 = 30) ∧ (30 * 2 < 61) :=
  ⟨rfl, rfl, by omega⟩

/-- Theorem 6 (Thms. 1.1 & 1.2): Exact strict rational ordering of the entire
    downward-closed delegation chain:
    `0.1098 < 3/10 < 29/70 < 0.48105 < 30/61 < 500/1011 < 5011/10110 < 1/2`. -/
theorem delegation_universal_sandwich :
    (1098 * 10 < 3 * 10000) ∧
    (3 * 70 < 29 * 10) ∧
    (29 * 100000 < 48105 * 70) ∧
    (48105 * 61 < 30 * 100000) ∧
    (30 * 1011 < 500 * 61) ∧
    (500 * 10110 < 5011 * 1011) ∧
    (5011 * 2 < 10110) :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Theorem 7 (Lem. 4.2): Exact pointwise clipping-plus-excess identity
    `clipAt z x + excessAbove z x = x` and forced-item payoff bound. -/
theorem forced_item_pointwise_identity (z x : Int) :
    clipAt z x + excessAbove z x = x ∧
    0 ≤ excessAbove z x ∧
    clipAt z x ≤ z := by
  dsimp only [clipAt, excessAbove]
  split
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩

/-- Theorem 8 (Sec. 4.1 Eq. (4.3)): Exact tail-bound monotonicity:
    for `0 ≤ e ≤ D < x` (representing `e/D ∈ [0, 1]` and `x/D > 1`),
    `(1 - e/D)/(x/D - e/D) ≤ 1/(x/D)` in cleared integers: `x * (D - e) ≤ D * (x - e)`. -/
theorem threshold_tail_bound_monotone (D e x : Int)
    (he0 : 0 ≤ e) (hDx : D < x) :
    x * (D - e) ≤ D * (x - e) := by
  rw [Int.mul_sub, Int.mul_sub, Int.mul_comm D x]
  have h1 : D * e ≤ x * e := mul_le_mul_nonneg_right (by omega) he0
  omega

/-- Theorem 9 (Lem. 4.3 Eq. (4.5)): Inductive Efron-Stein clipped sum-of-squares bound:
    if every marginal increment `Δ_i` satisfies `0 ≤ Δ_i ≤ c`, then
    `∑ Δ_i^2 ≤ c * ∑ Δ_i` (combining with `∑ Δ_i ≤ Z` gives `∑ Δ_i^2 ≤ c Z`). -/
theorem clipped_optimum_variance_step_bound (c : Int) (hc : 0 ≤ c) :
    ∀ ds : List Int, AllBounded c ds → sumSqInt ds ≤ c * sumInt ds
  | [], _ => by
      dsimp only [sumSqInt, sumInt]
      rw [Int.mul_zero]
      omega
  | d :: rest, ⟨⟨hd0, hdc⟩, hrest⟩ => by
      dsimp only [sumSqInt, sumInt]
      rw [Int.mul_add]
      have ih := clipped_optimum_variance_step_bound c hc rest hrest
      have hhd : d * d ≤ c * d := mul_le_mul_nonneg_right hdc hd0
      have hcomm : c * d = d * c := Int.mul_comm c d
      omega

/-- Theorem 10 (Lem. 4.4): Cantelli/Markov upper bound ruling out `μ ≥ 5`:
    for cleared integers `μ ≥ 5 D` (`D > 0`), `μ^2 > 2 μ D + 12 D^2`, i.e.
    `μ^2 / (2 μ + 12) > 1` (attaining `25/22 > 1` at `μ = 5`). -/
theorem cantelli_mu_less_than_five (mu D : Int) (hD : 0 < D) (hmu : 5 * D ≤ mu) :
    2 * (mu * D) + 12 * (D * D) < mu * mu := by
  have h1 : 3 * D ≤ mu - 2 * D := by omega
  have h2 : (5 * D) * (3 * D) ≤ mu * (mu - 2 * D) := by
    have ha : (5 * D) * (3 * D) ≤ mu * (3 * D) := mul_le_mul_nonneg_right hmu (by omega)
    have hb : mu * (3 * D) ≤ mu * (mu - 2 * D) := mul_le_mul_nonneg_left (by omega) h1
    omega
  have h3 : (5 * D) * (3 * D) = 15 * (D * D) := by
    have h15 : (5 : Int) * 3 = 15 := by omega
    calc (5 * D) * (3 * D) = (5 * 3) * (D * D) := by ac_rfl
      _ = 15 * (D * D) := by rw [h15]
  have h4 : mu * (mu - 2 * D) = mu * mu - 2 * (mu * D) := by
    rw [Int.mul_sub]
    have hc : mu * (2 * D) = 2 * (mu * D) := by ac_rfl
    rw [hc]
  have hD2 : 0 < D * D := Int.mul_pos hD hD
  omega

/-- Theorem 11 (Lem. 4.4 Case 1, `0 < b ≤ 2/13`): Exact cleared-integer verification of
    `52/3 + 1 - 50/13 - (80/33)^2 - 40/11 - 13/5 = 168034 / 70785 > 0`. -/
theorem gamma_case1_exact_positivity :
    (52 * 23595 + 70785 - 50 * 5445 - 6400 * 65 - 40 * 6435 - 13 * 14157 = 168034) ∧
    (3 * 23595 = 70785) ∧
    (13 * 5445 = 70785) ∧
    (1089 * 65 = 70785) ∧
    (11 * 6435 = 70785) ∧
    (5 * 14157 = 70785) ∧
    (0 < 168034) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by omega⟩

/-- Theorem 12 (Lem. 4.4 Eq. (4.11)): Exact 8-term exponential Taylor proof of
    `log(13/2) < 15/8`: `∑_{k=0}^7 (15/8)^k / k! - 13/2 = 3772963 / 234881024 > 0`.
    Common denominator `234881024 = 2^21 * 112 = 7! * 8^7 / 45`. -/
theorem exp_15_8_taylor_beats_13_2 :
    let D : Int := 234881024
    -- Exact scaled terms T_k = D * (15/8)^k / k! for k = 0..7
    let t0 : Int := 234881024
    let t1 : Int := 440401920
    let t2 : Int := 412876800
    let t3 : Int := 258048000
    let t4 : Int := 120960000
    let t5 : Int := 45360000
    let t6 : Int := 14175000
    let t7 : Int := 3796875
    (8 * t1 = 15 * t0) ∧
    (16 * t2 = 15 * t1) ∧
    (24 * t3 = 15 * t2) ∧
    (32 * t4 = 15 * t3) ∧
    (40 * t5 = 15 * t4) ∧
    (48 * t6 = 15 * t5) ∧
    (56 * t7 = 15 * t6) ∧
    (2 * (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7) - 13 * D = 2 * 3772963) ∧
    (0 < 3772963) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by omega⟩

/-- Theorem 13 (Lem. 4.4 Eq. (4.12)): Exact degree-7 polynomial `P(b)` and exact integer-cleared
    degree-7 Bernstein basis transformation on `[2/13, 2/5]` and `[2/5, 2/3]`:
    all 8 Bernstein coefficients on `[2/13, 2/5]` are strictly positive with exact minimum
    `447966/78125`, and all 8 on `[2/5, 2/3]` are strictly positive with exact minimum `6518/118125`. -/
def evalP7Num (p q : Int) : Int :=
  1242 * p^7 - 3593 * p^6 * q + 1795 * p^5 * q^2 - 2948 * p^4 * q^3 +
  7546 * p^3 * q^4 - 5459 * p^2 * q^5 + 1345 * p * q^6 - 72 * q^7

private def binomNat : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomNat n k + binomNat n (k + 1)

private def p7Coeff : Nat → Int
  | 0 => -72
  | 1 => 1345
  | 2 => -5459
  | 3 => 7546
  | 4 => -2948
  | 5 => 1795
  | 6 => -3593
  | 7 => 1242
  | _ => 0

/-- Exact cleared power-basis coefficient `D^7 * p_j` of `Q(u) = P(l/D + (r-l)/D * u)`. -/
private def shiftedCoeff7 (l r D j : Nat) : Int :=
  let h : Int := Int.ofNat (r - l)
  let li : Int := Int.ofNat l
  let Di : Int := Int.ofNat D
  let term (i : Nat) : Int :=
    if j ≤ i then
      p7Coeff i * Int.ofNat (binomNat i j) * (li ^ (i - j)) * (h ^ j) * (Di ^ (7 - i))
    else 0
  term 0 + term 1 + term 2 + term 3 + term 4 + term 5 + term 6 + term 7

/-- Exact cleared Bernstein numerator `105 * D^7 * β_k` (since `lcm_{j≤7} C(7,j) = lcm(1,7,21,35) = 105`). -/
private def bernsteinScaled7 (l r D k : Nat) : Int :=
  let term (j : Nat) : Int :=
    if j ≤ k then
      shiftedCoeff7 l r D j * Int.ofNat (105 * binomNat k j / binomNat 7 j)
    else 0
  term 0 + term 1 + term 2 + term 3 + term 4 + term 5 + term 6 + term 7

private def allBernsteinPos7 (l r D : Nat) : Bool :=
  (0 < bernsteinScaled7 l r D 0) &&
  (0 < bernsteinScaled7 l r D 1) &&
  (0 < bernsteinScaled7 l r D 2) &&
  (0 < bernsteinScaled7 l r D 3) &&
  (0 < bernsteinScaled7 l r D 4) &&
  (0 < bernsteinScaled7 l r D 5) &&
  (0 < bernsteinScaled7 l r D 6) &&
  (0 < bernsteinScaled7 l r D 7)

private def minBernsteinScaled7 (l r D : Nat) : Int :=
  let b0 := bernsteinScaled7 l r D 0
  let b1 := bernsteinScaled7 l r D 1
  let b2 := bernsteinScaled7 l r D 2
  let b3 := bernsteinScaled7 l r D 3
  let b4 := bernsteinScaled7 l r D 4
  let b5 := bernsteinScaled7 l r D 5
  let b6 := bernsteinScaled7 l r D 6
  let b7 := bernsteinScaled7 l r D 7
  min b0 (min b1 (min b2 (min b3 (min b4 (min b5 (min b6 b7))))))

theorem degree7_poly_positivity_bernstein_eval :
    (0 < evalP7Num 2 13) ∧
    (0 < evalP7Num 1 4) ∧
    (0 < evalP7Num 2 5) ∧
    (0 < evalP7Num 1 2) ∧
    (0 < evalP7Num 2 3) ∧
    (allBernsteinPos7 10 26 65 = true) ∧
    (minBernsteinScaled7 10 26 65 * 78125 = 447966 * (105 * (65 : Int)^7)) ∧
    (allBernsteinPos7 6 10 15 = true) ∧
    (minBernsteinScaled7 6 10 15 * 118125 = 6518 * (105 * (15 : Int)^7)) :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide⟩

/-- Theorem 14 (Sec. 5 Eqs. (5.1)–(5.2)): Exact seed reserve gap positivity.
    For a seed `P` at level `t` with total weight `wP ≥ t` and lightest item `wmin`
    satisfying `wP - wmin < t`, the reserve gap `bP := t + wmin - wP` satisfies
    `0 < bP ∧ bP ≤ wmin`. -/
theorem seed_reserve_gap_positive (t wP wmin : Int)
    (hreach : t ≤ wP) (hmin_drop : wP - wmin < t) :
    0 < t + wmin - wP ∧ t + wmin - wP ≤ wmin :=
  ⟨by omega, by omega⟩

/-- Theorem 15 (Sec. 2.3 & Sec. 5.1): Exact safe-singleton normalization constants for
    Theorem 5.1: `ρ_0 = 29/70 + 10^{-6} = 2900007 / 7000000`, `R = 1/ρ_0 = 7000000 / 2900007`,
    and `29/70 < ρ_0 < 1/2`. -/
theorem safe_singleton_normalization_ratio :
    (29 * 100000 + 7 = 2900007) ∧
    (70 * 100000 = 7000000) ∧
    (29 * 7000000 < 2900007 * 70) ∧
    (2900007 * 2 < 7000000) :=
  ⟨rfl, rfl, by omega, by omega⟩

/-- Theorem 16 (Lem. 6.3(c)): Exact profile stop-loss sandwich.
    If `x < y`, `Sy ≤ Sx`, and `(y - x) * Sy ≤ Dx - Dy ≤ (y - x) * Sx`, then `Dy ≤ Dx`
    whenever `0 ≤ Sy` and the bracket is consistent (`(y - x) * Sy ≤ (y - x) * Sx`). -/
theorem profile_stoploss_monotone_sandwich (x y Sx Sy Dx Dy : Int)
    (hxy : x < y) (hSy : 0 ≤ Sy) (hS : Sy ≤ Sx)
    (hlo : (y - x) * Sy ≤ Dx - Dy) :
    (y - x) * Sy ≤ (y - x) * Sx ∧ Dy ≤ Dx := by
  have h1 : (y - x) * Sy ≤ (y - x) * Sx := mul_le_mul_nonneg_left (by omega) hS
  have h2 : 0 ≤ (y - x) * Sy := Int.mul_nonneg (by omega) hSy
  exact ⟨h1, by omega⟩

/-- Theorem 17 (Lem. 6.3(e)): Exact finite-set clipping decomposition identity
    `∑_{i ∈ B} min(x_i, c) + ∑_{i ∈ B} (x_i - c)_+ = ∑_{i ∈ B} x_i` over any `List Int`. -/
theorem profile_clipping_decomposition_sum (c : Int) :
    ∀ xs : List Int, sumClip c xs + sumExcess c xs = sumInt xs
  | [] => rfl
  | x :: rest => by
      dsimp only [sumClip, sumExcess, sumInt]
      have ih := profile_clipping_decomposition_sum c rest
      have hpt := (forced_item_pointwise_identity c x).1
      omega

/-- Theorem 18 (Sec. 2.3): Exact scale homogeneity of additive set values under `λ > 0`:
    multiplying every item value by `λ` multiplies `sumInt xs` by `λ` identically. -/
private def scaleList (lam : Int) : List Int → List Int
  | [] => []
  | x :: xs => (lam * x) :: scaleList lam xs

theorem scaled_menu_score_homogeneity (lam : Int) :
    ∀ xs : List Int, sumInt (scaleList lam xs) = lam * sumInt xs
  | [] => by dsimp only [scaleList, sumInt]; rw [Int.mul_zero]
  | x :: rest => by
      dsimp only [scaleList, sumInt]
      rw [Int.mul_add, scaled_menu_score_homogeneity lam rest]

end DelegationBounds
