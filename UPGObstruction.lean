import Mathlib

/-!
# Global obstruction floor and the interface gluing anomaly

Sections 4.2 and 4.3 of the paper.

**Global bound (Theorem 4.2).** With `U_C(T) = (T² - a² I)² + ε I`, every
eigenvalue contributes at least `ε`, strictly more while it crosses the window
`|λ| < a/2`, and on the normalized commuting path `T(t) = t I` the obstruction
is `2∫₀^a (t⁴ - 2a²t² + a⁴ + ε) dt = (16/15) a⁵ + 2aε`. This module proves the
pointwise floor, the window floor `9a⁴/16`, and the closed-form integral. The
passage from pointwise floors to the matrix path integral (Weyl ordering of the
eigenvalues along a path) is not formalized.

**Interface anomaly (Theorem 4.3).** Gluing is a Schur complement. This module
proves the scalar (one-channel) case in full: for `a, b > 0` with `ab - e² > 0`,

    log(ab - e²) = log a + log b + log(1 - e²/(ab)),

the anomaly `log(1 - e²/(ab))` is `≤ 0`, and it vanishes exactly when the
coupling `e` vanishes. For the multi-channel statement it proves the sign part:
if the boundary product has eigenvalues `μₖ ∈ [0, 1)`, then
`Σ log(1 - μₖ) ≤ 0`, with equality exactly when every `μₖ = 0`. The general
block determinant identity is Mathlib's `Matrix.det_fromBlocks₁₁`.
-/

open Real intervalIntegral

namespace UPGObstruction

/-! ### Theorem 4.2: the global bound -/

/-- Every eigenvalue contributes at least `ε` to `U_C`. -/
theorem pointwise_floor (l a ε : ℝ) : ε ≤ (l ^ 2 - a ^ 2) ^ 2 + ε := by
  nlinarith [sq_nonneg (l ^ 2 - a ^ 2)]

/-- Inside the crossing window `|λ| < a/2` the quartic well contributes at least
`9a⁴/16`, which makes the floor `2aε` strict on every continuous path. -/
theorem window_floor (l a : ℝ) (h : |l| < a / 2) : 9 * a ^ 4 / 16 ≤ (l ^ 2 - a ^ 2) ^ 2 := by
  have ha : 0 < a := by linarith [abs_nonneg l]
  have hl : l ^ 2 < a ^ 2 / 4 := by
    have h1 : l ^ 2 = |l| ^ 2 := (sq_abs l).symm
    rw [h1]
    nlinarith [abs_nonneg l]
  have h2 : 3 * a ^ 2 / 4 ≤ a ^ 2 - l ^ 2 := by linarith
  have h3 : 0 ≤ 3 * a ^ 2 / 4 := by positivity
  nlinarith [mul_le_mul h2 h2 h3 (by linarith)]

/-- The minimal obstruction on the normalized commuting path `T(t) = t I`:
`2∫₀^a (t⁴ - 2a²t² + a⁴ + ε) dt = (16/15) a⁵ + 2aε`. -/
theorem normalized_path_obstruction (a ε : ℝ) :
    2 * ∫ t in (0 : ℝ)..a, (t ^ 4 - 2 * a ^ 2 * t ^ 2 + a ^ 4 + ε)
      = 16 / 15 * a ^ 5 + 2 * a * ε := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun t : ℝ => t ^ 5 / 5 - 2 * a ^ 2 * t ^ 3 / 3 + a ^ 4 * t + ε * t)
        (x ^ 4 - 2 * a ^ 2 * x ^ 2 + a ^ 4 + ε) x := by
    intro x _
    have h := ((((hasDerivAt_pow 5 x).div_const 5).sub
      (((hasDerivAt_pow 3 x).const_mul (2 * a ^ 2)).div_const 3)).add
      ((hasDerivAt_id x).const_mul (a ^ 4))).add ((hasDerivAt_id x).const_mul ε)
    exact h.congr_deriv (by norm_num <;> ring)
  have hint : IntervalIntegrable (fun x : ℝ => x ^ 4 - 2 * a ^ 2 * x ^ 2 + a ^ 4 + ε)
      MeasureTheory.volume 0 a := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  norm_num
  try ring

/-- The floor `2aε` is positive whenever `a, ε > 0`, and the normalized path sits
strictly above it by `(16/15) a⁵`. -/
theorem normalized_path_above_floor (a ε : ℝ) (ha : 0 < a) :
    2 * a * ε < 16 / 15 * a ^ 5 + 2 * a * ε := by
  have : 0 < a ^ 5 := by positivity
  linarith

/-! ### Theorem 4.3: the interface anomaly -/

/-- One-channel gluing: `log(ab - e²) = log a + log b + log(1 - e²/(ab))`. -/
theorem scalar_gluing (a b e : ℝ) (ha : 0 < a) (hb : 0 < b) (hM : 0 < a * b - e ^ 2) :
    Real.log (a * b - e ^ 2)
      = Real.log a + Real.log b + Real.log (1 - e ^ 2 / (a * b)) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hx : 0 < 1 - e ^ 2 / (a * b) := by
    have : e ^ 2 / (a * b) < 1 := (div_lt_one hab).mpr (by linarith)
    linarith
  have h1 : a * b - e ^ 2 = a * b * (1 - e ^ 2 / (a * b)) := by
    have hc : e ^ 2 / (a * b) * (a * b) = e ^ 2 := div_mul_cancel₀ _ hab.ne'
    calc a * b - e ^ 2 = a * b - e ^ 2 / (a * b) * (a * b) := by rw [hc]
      _ = a * b * (1 - e ^ 2 / (a * b)) := by ring
  rw [h1, Real.log_mul hab.ne' hx.ne', Real.log_mul ha.ne' hb.ne']

/-- The one-channel anomaly is a discount: `log(1 - e²/(ab)) ≤ 0`. -/
theorem scalar_anomaly_nonpos (a b e : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hM : 0 < a * b - e ^ 2) :
    Real.log (1 - e ^ 2 / (a * b)) ≤ 0 := by
  have hab : 0 < a * b := mul_pos ha hb
  have h0 : 0 ≤ e ^ 2 / (a * b) := div_nonneg (sq_nonneg e) hab.le
  have hlt : e ^ 2 / (a * b) < 1 := (div_lt_one hab).mpr (by linarith)
  exact Real.log_nonpos (by linarith) (by linarith)

/-- The one-channel anomaly vanishes exactly when the seam coupling vanishes. -/
theorem scalar_anomaly_eq_zero_iff (a b e : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hM : 0 < a * b - e ^ 2) :
    Real.log (1 - e ^ 2 / (a * b)) = 0 ↔ e = 0 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hx : 0 < 1 - e ^ 2 / (a * b) := by
    have : e ^ 2 / (a * b) < 1 := (div_lt_one hab).mpr (by linarith)
    linarith
  constructor
  · intro h
    rcases Real.log_eq_zero.mp h with h0 | h1 | hm1
    · linarith
    · have hq : e ^ 2 / (a * b) = 0 := by linarith
      rcases div_eq_zero_iff.mp hq with he | he
      · simpa using he
      · exact absurd he hab.ne'
    · linarith
  · intro he
    subst he
    simp

/-- Multi-channel sign: if the boundary product has eigenvalues `μₖ ∈ [0, 1)`,
the anomaly `Σ log(1 - μₖ)` is `≤ 0`. -/
theorem anomaly_nonpos {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (h0 : ∀ k ∈ s, 0 ≤ μ k) (h1 : ∀ k ∈ s, μ k < 1) :
    ∑ k ∈ s, Real.log (1 - μ k) ≤ 0 :=
  Finset.sum_nonpos (fun k hk => Real.log_nonpos (by linarith [h1 k hk]) (by linarith [h0 k hk]))

/-- Multi-channel equality: the anomaly vanishes exactly when every `μₖ = 0`,
i.e. exactly when the boundary product (and hence the seam coupling) vanishes. -/
theorem anomaly_eq_zero_iff {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (h0 : ∀ k ∈ s, 0 ≤ μ k) (h1 : ∀ k ∈ s, μ k < 1) :
    ∑ k ∈ s, Real.log (1 - μ k) = 0 ↔ ∀ k ∈ s, μ k = 0 := by
  have hterm : ∀ k ∈ s, Real.log (1 - μ k) ≤ 0 :=
    fun k hk => Real.log_nonpos (by linarith [h1 k hk]) (by linarith [h0 k hk])
  rw [Finset.sum_eq_zero_iff_of_nonpos hterm]
  refine forall₂_congr (fun k hk => ?_)
  constructor
  · intro h
    rcases Real.log_eq_zero.mp h with h' | h' | h'
    · linarith [h1 k hk]
    · linarith
    · linarith [h1 k hk]
  · intro h
    rw [h, sub_zero, Real.log_one]

end UPGObstruction
