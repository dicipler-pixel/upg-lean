import Mathlib

/-!
# The noncommutative torus anchor

Section 4.4 of the paper moves the torus anchor onto a pair of unitaries
`U, V ∈ U(d)` with relator `R = U V Uᴴ Vᴴ`. With `λ₁, …, λ_d` the spectrum of
`R` (unit complex numbers), the readouts are

* the defect `δ = (1/d) Σ |λⱼ - 1|²`,
* the branch guard `g = minⱼ |λⱼ + 1|`,
* the winding record `w = (1/2π) Σ arg λⱼ` (principal branch).

This module proves, for any finite family of unit complex numbers standing in
for the spectrum:

* the relator of two unitaries has determinant one, so the eigenvalues
  multiply to one (the reason the record is an integer, Theorem 4.5);
* integrality of the record and its bound `2|w| + 1 ≤ d` when the guard is open
  (Theorem 4.5(i));
* the half-angle readouts `|e^{iθ} - 1|² = 4 sin²(θ/2)`,
  `|e^{iθ} + 1|² = 4 cos²(θ/2)`;
* the admissible domain `δ + g² ≤ 4` (Theorem 4.6) and forced refusal
  (Corollary 4.7);
* the amplitude floor `|w| ≤ (d/4)√δ`, hence `w ≠ 0 ⇒ d²δ ≥ 16`
  (Theorem 4.8);
* the clock and shift: `U V = ω V U`, the scalar relator `R = ω I`, and its
  readouts `δ = 4 sin²(π/d)`, `g² = 4 cos²(π/d)`, `w = 1` for `d ≥ 3`, with
  refusal at `d = 2` (Proposition 4.9).

The passage from a matrix to its spectrum (that the eigenvalues of a unitary
have modulus one and multiply to its determinant) is standard linear algebra
and is not re-proved here; the statements take the spectrum as a family of unit
complex numbers whose product is one. The Exel–Loring identification of the
record with a determinant winding (Theorem 4.5(iv)) is cited, not formalized.
-/

open Complex Finset
open Real (pi_pos)

namespace UPGTorusAnchor

/-! ### The relator has determinant one -/

/-- The relator of two unitary matrices has determinant one. -/
theorem relator_det_one {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ)
    (hU : U * star U = 1) (hV : V * star V = 1) :
    (U * V * star U * star V).det = 1 := by
  have hu : U.det * (star U).det = 1 := by rw [← Matrix.det_mul, hU, Matrix.det_one]
  have hv : V.det * (star V).det = 1 := by rw [← Matrix.det_mul, hV, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (V.det * (star V).det) * hu + hv

/-! ### Unit complex numbers: arguments and half-angles -/

/-- A unit complex number is `exp(i arg z)`. -/
theorem unit_eq_exp_arg (z : ℂ) (hz : ‖z‖ = 1) : Complex.exp (↑(arg z) * I) = z := by
  have e := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at e
  exact e

/-- An open guard keeps the principal argument strictly inside `(-π, π)`. -/
theorem abs_arg_lt_pi (z : ℂ) (hz : ‖z‖ = 1) (h : z ≠ -1) : |arg z| < Real.pi := by
  refine lt_of_le_of_ne (abs_arg_le_pi z) ?_
  intro heq
  have hpi : arg z = Real.pi := by
    rcases (abs_eq Real.pi_pos.le).mp heq with h1 | h1
    · exact h1
    · exact absurd h1 (ne_of_gt (neg_pi_lt_arg z))
  apply h
  have e := unit_eq_exp_arg z hz
  rw [hpi, Complex.exp_pi_mul_I] at e
  exact e.symm

/-- Defect and guard of one unit eigenvalue always sum to four. -/
theorem unit_defect_add_guard (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 + ‖z + 1‖ ^ 2 = 4 := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z
    rw [hz, Complex.normSq_apply, one_pow] at this
    linarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im]
  linear_combination 2 * h

/-- The defect readout is a squared half-angle sine: `|e^{iθ} - 1|² = 4 sin²(θ/2)`. -/
theorem defect_half_angle (θ : ℝ) :
    ‖Complex.exp (↑θ * I) - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
  have hre : (Complex.exp (↑θ * I) - 1).re = Real.cos θ - 1 := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp (↑θ * I) - 1).im = Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  have h2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have : θ = 2 * (θ / 2) := by ring
    conv_lhs => rw [this]
    exact Real.cos_two_mul _
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  linear_combination (Real.sin_sq_add_cos_sq θ) - 2 * h2 - 4 * (Real.sin_sq_add_cos_sq (θ / 2))

/-- The guard readout is a squared half-angle cosine: `|e^{iθ} + 1|² = 4 cos²(θ/2)`. -/
theorem guard_half_angle (θ : ℝ) :
    ‖Complex.exp (↑θ * I) + 1‖ ^ 2 = 4 * Real.cos (θ / 2) ^ 2 := by
  have hre : (Complex.exp (↑θ * I) + 1).re = Real.cos θ + 1 := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp (↑θ * I) + 1).im = Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  have h2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have : θ = 2 * (θ / 2) := by ring
    conv_lhs => rw [this]
    exact Real.cos_two_mul _
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  linear_combination (Real.sin_sq_add_cos_sq θ) + 2 * h2

/-! ### Theorem 4.5(i): the record is an integer, and bounded -/

/-- If unit eigenvalues multiply to one, their principal arguments sum to a
multiple of `2π`: the winding record is an integer. -/
theorem winding_is_integer {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) (hprod : ∏ j ∈ s, z j = 1) :
    ∃ n : ℤ, ∑ j ∈ s, arg (z j) = 2 * Real.pi * n := by
  set S := ∑ j ∈ s, arg (z j) with hSdef
  have hexp : Complex.exp ((S : ℂ) * I) = 1 := by
    rw [hSdef, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← hprod]
    exact Finset.prod_congr rfl (fun j hj => unit_eq_exp_arg (z j) (hz j hj))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have h1 : (S : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [hn]
    push_cast
    ring
  exact_mod_cast h1

/-- With the guard open (no eigenvalue at `-1`), the record obeys
`2|w| + 1 ≤ d`, that is `|w| ≤ ⌊(d-1)/2⌋`. -/
theorem winding_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) (hg : ∀ j ∈ s, z j ≠ -1) (n : ℤ)
    (hn : ∑ j ∈ s, arg (z j) = 2 * Real.pi * n) :
    2 * |n| + 1 ≤ (s.card : ℤ) := by
  have hlt : |∑ j ∈ s, arg (z j)| < s.card * Real.pi := by
    calc |∑ j ∈ s, arg (z j)| ≤ ∑ j ∈ s, |arg (z j)| := Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _j ∈ s, Real.pi :=
          Finset.sum_lt_sum_of_nonempty hs (fun j hj => abs_arg_lt_pi _ (hz j hj) (hg j hj))
      _ = s.card * Real.pi := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hlt
  have key : 2 * |(n : ℝ)| < s.card := by nlinarith [Real.pi_pos, abs_nonneg (n : ℝ)]
  have key' : 2 * |n| < (s.card : ℤ) := by exact_mod_cast key
  exact Int.add_one_le_iff.mpr key'

/-! ### Theorem 4.6 and Corollary 4.7: the admissible domain -/

/-- The admissible domain `δ + g² ≤ 4`: for any `g` not exceeding any guard value
(in particular the minimum guard), the mean defect plus `g²` is at most four. -/
theorem admissible_domain {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) (g : ℝ) (hg : ∀ j ∈ s, g ^ 2 ≤ ‖z j + 1‖ ^ 2) :
    (∑ j ∈ s, ‖z j - 1‖ ^ 2) / s.card + g ^ 2 ≤ 4 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : ∑ j ∈ s, ‖z j - 1‖ ^ 2 + ∑ j ∈ s, ‖z j + 1‖ ^ 2 = 4 * s.card := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun j hj => unit_defect_add_guard (z j) (hz j hj)),
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hle : (s.card : ℝ) * g ^ 2 ≤ ∑ j ∈ s, ‖z j + 1‖ ^ 2 := by
    have := Finset.sum_le_sum hg
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  rw [div_add' _ _ _ (ne_of_gt hc), div_le_iff₀ hc]
  linarith

/-- Corollary 4.7 (forced refusal): a defect above `4 - τ²` closes the guard
below `τ`, in any dimension. -/
theorem forced_refusal (δ g τ : ℝ) (hτ : 0 ≤ τ) (hg0 : 0 ≤ g)
    (hdom : δ + g ^ 2 ≤ 4) (hδ : 4 - τ ^ 2 < δ) : g < τ := by
  nlinarith

/-! ### Theorem 4.8: the amplitude floor -/

/-- For a unit eigenvalue, `|arg z| ≤ (π/2) |z - 1|` (from `sin x ≥ 2x/π`). -/
theorem abs_arg_le_half_pi_mul (z : ℂ) (hz : ‖z‖ = 1) :
    |arg z| ≤ Real.pi / 2 * ‖z - 1‖ := by
  set θ := arg z with hθ
  have hz' : z = Complex.exp (↑θ * I) := (unit_eq_exp_arg z hz).symm
  have hnorm : ‖z - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hz', show (↑θ * I : ℂ) = I * ↑θ from mul_comm _ _,
      Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_two]
  have hθπ : |θ| ≤ Real.pi := abs_arg_le_pi z
  have h0 : 0 ≤ |θ| / 2 := by positivity
  have h1 : |θ| / 2 ≤ Real.pi / 2 := by linarith
  have hm := Real.mul_le_sin h0 h1
  have hpos : 0 ≤ Real.sin (|θ| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have habs : |Real.sin (θ / 2)| = Real.sin (|θ| / 2) := by
    rcases le_or_lt 0 θ with h | h
    · rw [abs_of_nonneg h] at hpos ⊢
      exact abs_of_nonneg hpos
    · rw [abs_of_neg h] at hpos ⊢
      rw [neg_div, Real.sin_neg] at hpos ⊢
      rw [abs_of_nonpos (show Real.sin (θ / 2) ≤ 0 by linarith)]
  rw [hnorm, habs]
  have hpi : 0 < Real.pi := Real.pi_pos
  calc |θ| = |θ| / Real.pi * Real.pi := (div_mul_cancel₀ _ hpi.ne').symm
    _ = (2 / Real.pi * (|θ| / 2)) * Real.pi := by ring
    _ ≤ Real.sin (|θ| / 2) * Real.pi := mul_le_mul_of_nonneg_right hm hpi.le
    _ = Real.pi / 2 * (2 * Real.sin (|θ| / 2)) := by ring

/-- Cauchy–Schwarz in the form used by the floor: `Σ aⱼ ≤ √(d Σ aⱼ²)`. -/
theorem sum_le_sqrt_card_mul_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∑ j ∈ s, a j ≤ Real.sqrt (s.card * ∑ j ∈ s, a j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

/-- Theorem 4.8 (amplitude floor), summed form:
`|Σ arg λⱼ| ≤ (π/2) √(d Σ |λⱼ - 1|²)`. -/
theorem abs_sum_arg_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) :
    |∑ j ∈ s, arg (z j)| ≤
      Real.pi / 2 * Real.sqrt (s.card * ∑ j ∈ s, ‖z j - 1‖ ^ 2) := by
  calc |∑ j ∈ s, arg (z j)| ≤ ∑ j ∈ s, |arg (z j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, Real.pi / 2 * ‖z j - 1‖ :=
        Finset.sum_le_sum (fun j hj => abs_arg_le_half_pi_mul (z j) (hz j hj))
    _ = Real.pi / 2 * ∑ j ∈ s, ‖z j - 1‖ := by rw [Finset.mul_sum]
    _ ≤ Real.pi / 2 * Real.sqrt (s.card * ∑ j ∈ s, ‖z j - 1‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_le_sqrt_card_mul_sum_sq s _) (by positivity)

/-- Theorem 4.8 in the paper's form: `4|w| ≤ √(d · Σ|λⱼ - 1|²) = d √δ`,
i.e. `|w| ≤ (d/4) √δ`. -/
theorem amplitude_floor {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) (n : ℤ) (hn : ∑ j ∈ s, arg (z j) = 2 * Real.pi * n) :
    4 * |(n : ℝ)| ≤ Real.sqrt (s.card * ∑ j ∈ s, ‖z j - 1‖ ^ 2) := by
  have h := abs_sum_arg_le s z hz
  rw [hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h
  nlinarith [Real.pi_pos, abs_nonneg (n : ℝ),
    Real.sqrt_nonneg (s.card * ∑ j ∈ s, ‖z j - 1‖ ^ 2)]

/-- A nonzero record forces the defect: `w ≠ 0 ⇒ d · Σ|λⱼ - 1|² ≥ 16`, that is
`δ ≥ 16 / d²`. -/
theorem nonzero_winding_forces_defect {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) (n : ℤ) (hn : ∑ j ∈ s, arg (z j) = 2 * Real.pi * n)
    (hn0 : n ≠ 0) :
    16 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖z j - 1‖ ^ 2 := by
  have hf := amplitude_floor s z hz n hn
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  have hX : 0 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖z j - 1‖ ^ 2 := by positivity
  have hsq := Real.sq_sqrt hX
  have hs4 : 4 ≤ Real.sqrt ((s.card : ℝ) * ∑ j ∈ s, ‖z j - 1‖ ^ 2) := by linarith
  nlinarith [hs4, hsq]

/-! ### Proposition 4.9: clock and shift -/

section ClockShift

variable (d : ℕ)

/-- The clock `U = diag(1, ω, …, ω^{d-1})`. -/
noncomputable def clock (ω : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun k => ω ^ (k : ℕ))

/-- The cyclic shift `V`, sending basis vector `j` to `j + 1 (mod d)`. -/
def shift : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if (i : ℕ) = ((j : ℕ) + 1) % d then 1 else 0

/-- Powers of a `d`-th root of unity only see the exponent modulo `d`. -/
theorem pow_mod_of_pow_eq_one (ω : ℂ) (hω : ω ^ d = 1) (m : ℕ) :
    ω ^ (m % d) = ω ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m d, pow_add, pow_mul, hω, one_pow, mul_one]

/-- The clock and shift commute up to the scalar `ω`: `U V = ω V U`. -/
theorem clock_mul_shift (ω : ℂ) (hω : ω ^ d = 1) :
    clock d ω * shift d = ω • (shift d * clock d ω) := by
  ext i j
  simp only [clock, shift, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
    smul_eq_mul]
  split_ifs with h
  · rw [h, pow_mod_of_pow_eq_one d ω hω, pow_succ]
    ring
  · ring

end ClockShift

/-- If `U V = ω V U` with `U, V` unitary, the relator is the scalar `ω I`. -/
theorem scalar_relator {n : Type*} [Fintype n] [DecidableEq n] (U V : Matrix n n ℂ) (ω : ℂ)
    (h : U * V = ω • (V * U)) (hU : U * star U = 1) (hV : V * star V = 1) :
    U * V * star U * star V = ω • (1 : Matrix n n ℂ) := by
  rw [h, smul_mul_assoc, smul_mul_assoc, Matrix.mul_assoc V U, hU, Matrix.mul_one, hV]

/-- The clock phase `ω = e^{2πi/d}` has principal argument `2π/d` once `d ≥ 3`. -/
theorem clock_arg (d : ℕ) (hd : 3 ≤ d) :
    arg (Complex.exp (↑(2 * Real.pi / d) * I)) = 2 * Real.pi / d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Complex.exp_mul_I]
  apply Complex.arg_cos_add_sin_mul_I
  rw [Set.mem_Ioc]
  refine ⟨?_, ?_⟩
  · have : 0 < 2 * Real.pi / d := by positivity
    linarith [Real.pi_pos]
  · rw [div_le_iff₀ hdpos]
    nlinarith [Real.pi_pos, hd3]

/-- Proposition 4.9, winding: the `d` equal eigenvalues `ω` of the scalar relator
carry total argument `2π`, so `w = 1` for every `d ≥ 3`. -/
theorem clock_winding_one (d : ℕ) (hd : 3 ≤ d) :
    (d : ℝ) * arg (Complex.exp (↑(2 * Real.pi / d) * I)) = 2 * Real.pi * 1 := by
  have hdpos : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  rw [clock_arg d hd, mul_div_assoc', div_eq_iff hdpos]
  ring

/-- Proposition 4.9, defect: `δ = |ω - 1|² = 4 sin²(π/d)`. -/
theorem clock_defect (d : ℕ) :
    ‖Complex.exp (↑(2 * Real.pi / d) * I) - 1‖ ^ 2 = 4 * Real.sin (Real.pi / d) ^ 2 := by
  rw [defect_half_angle, show 2 * Real.pi / (d : ℝ) / 2 = Real.pi / d by ring]

/-- Proposition 4.9, guard: `g² = |ω + 1|² = 4 cos²(π/d)`; the scalar relator sits
on the boundary `δ + g² = 4` at every `d`. -/
theorem clock_guard (d : ℕ) :
    ‖Complex.exp (↑(2 * Real.pi / d) * I) + 1‖ ^ 2 = 4 * Real.cos (Real.pi / d) ^ 2 := by
  rw [guard_half_angle, show 2 * Real.pi / (d : ℝ) / 2 = Real.pi / d by ring]

/-- Proposition 4.9, refusal at `d = 2`: the relator is `-I` and the guard closes. -/
theorem clock_refused_at_two :
    Complex.exp (↑(2 * Real.pi / (2 : ℕ)) * I) = -1 := by
  have : (2 * Real.pi / ((2 : ℕ) : ℝ)) = Real.pi := by norm_num
  rw [this, Complex.exp_pi_mul_I]

end UPGTorusAnchor
