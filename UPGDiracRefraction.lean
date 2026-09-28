import Mathlib

/-!
# Dirac sector, rigidity and interface refraction

Sections 2, 4.1, 6.1, 6.3 and 8 of the paper.

* **Chiral symmetry (Section 4.1).** Every operator of the twisted torus family is
  off-diagonal in the `σ₃` basis, so it anticommutes with `σ₃`; its spectrum is
  symmetric under `λ ↦ -λ`, and a Hermitian off-diagonal `2 × 2` block squares to
  `|w|² I`, giving the paired eigenvalues `±|w|`.
* **Positive-sector projector (Section 4.1).** For a unit phase `u = Z/|Z|`, the
  matrix `½ [[1, -ū], [-u, 1]]` is a rank-one projector: idempotent with trace one.
* **Phase velocity (Theorem 4.1).** For `Z = x + iy`, `Im(Z̄ Ż) = x ẏ - y ẋ`, the
  numerator of the transport law.
* **Chiral ledger calibration (Section 2).** `a* = e^{π²/12} - 1` solves
  `ln(1 + a) = π²/12`.
* **Rigidity (Section 6.1).** `R_η = 1/(s² + η)` lies in `(0, 1/η]` and reaches
  the cap exactly when `s = 0` (a kernel).
* **Interface refraction (Proposition 6.2).** Tangential momentum and energy
  conservation give `R₁(E - V₁) sin²θ₁ = R₂(E - V₂) sin²θ₂`; the turning barrier;
  and, with the regularized rigidity, `sin²θ₂ = (s₂² + η)/(s₁² + η) · sin²θ₁`.
* **Oblique Riesz projectors (Section 8).** Two rank-one idempotents can have
  `Tr(Π₀ Π₁) = 2`, outside the range `[0, 1]` of a squared cosine.
-/

open Matrix Complex

namespace UPGDiracRefraction

/-! ### Chiral symmetry and the paired spectrum -/

/-- `σ₃ = diag(1, -1)`. -/
def sigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Every off-diagonal `2 × 2` operator anticommutes with `σ₃`: `{σ₃, D} = 0`. -/
theorem sigma3_anticommutes (p q : ℂ) :
    sigma3 * !![0, p; q, 0] + !![0, p; q, 0] * sigma3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigma3, Matrix.mul_apply, Fin.sum_univ_two]

/-- A Hermitian off-diagonal block squares to `|w|² I`, so its eigenvalues are the
chiral pair `±|w|`. -/
theorem hermitian_offdiag_sq (w : ℂ) :
    !![0, w; (starRingEnd ℂ) w, 0] * !![0, w; (starRingEnd ℂ) w, 0]
      = ((Complex.normSq w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : w * (starRingEnd ℂ) w = (Complex.normSq w : ℂ) := Complex.mul_conj w
  have h2 : (starRingEnd ℂ) w * w = (Complex.normSq w : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj w
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

/-- The positive-sector projector `½ [[1, -ū], [-u, 1]]` for a unit phase `u`. -/
noncomputable def sectorProjector (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, -(starRingEnd ℂ) u / 2; -u / 2, 1 / 2]

/-- The sector projector is idempotent. -/
theorem sectorProjector_idem (u : ℂ) (hu : ‖u‖ = 1) :
    sectorProjector u * sectorProjector u = sectorProjector u := by
  have hn : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu, one_pow]
  have hc : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, hn, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorProjector, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (1 / 4 : ℂ) * hc

/-- The sector projector has trace one: it projects onto one line. -/
theorem sectorProjector_trace (u : ℂ) : Matrix.trace (sectorProjector u) = 1 := by
  rw [Matrix.trace_fin_two]
  norm_num [sectorProjector]

/-! ### Theorem 4.1: the numerator of the phase transport law -/

/-- For `Z = x + iy` and `Ż = ẋ + iẏ`, `Im(Z̄ Ż) = x ẏ - y ẋ`. -/
theorem phase_numerator (x y dx dy : ℝ) :
    ((starRingEnd ℂ) (⟨x, y⟩ : ℂ) * (⟨dx, dy⟩ : ℂ)).im = x * dy - y * dx := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ### Section 2: chiral ledger calibration -/

/-- The half-Cauchy calibration `a* = e^{π²/12} - 1` gives `ln(1 + a*) = π²/12`. -/
theorem half_cauchy_calibration :
    Real.log (1 + (Real.exp (Real.pi ^ 2 / 12) - 1)) = Real.pi ^ 2 / 12 := by
  simp

/-! ### Section 6.1: rigidity -/

/-- Rigidity `R_η = 1/(s² + η)` is positive. -/
theorem rigidity_pos (s η : ℝ) (hη : 0 < η) : 0 < 1 / (s ^ 2 + η) := by
  positivity

/-- Rigidity is capped by `1/η`. -/
theorem rigidity_le_cap (s η : ℝ) (hη : 0 < η) : 1 / (s ^ 2 + η) ≤ 1 / η :=
  one_div_le_one_div_of_le hη (by nlinarith [sq_nonneg s])

/-- The cap `1/η` is reached exactly when the declared operator has a kernel,
`s = σ_min = 0`. -/
theorem rigidity_eq_cap_iff (s η : ℝ) (hη : 0 < η) : 1 / (s ^ 2 + η) = 1 / η ↔ s = 0 := by
  have hpos : 0 < s ^ 2 + η := by positivity
  constructor
  · intro h
    have h' : s ^ 2 + η = η := by
      have e := congrArg (fun t => 1 / t) h
      simp only [one_div_one_div] at e
      exact e
    have : s ^ 2 = 0 := by linarith
    exact (pow_eq_zero_iff two_ne_zero).mp this
  · intro h
    subst h
    simp

/-! ### Proposition 6.2: interface refraction -/

/-- The refraction law: with conserved tangential momentum `R₁v₁ sinθ₁ = R₂v₂ sinθ₂`
and energies `E - Vᵢ = ½ Rᵢ vᵢ²`, one has `R₁(E - V₁) sin²θ₁ = R₂(E - V₂) sin²θ₂`. -/
theorem refraction_law (R₁ R₂ E V₁ V₂ v₁ v₂ s₁ s₂ : ℝ)
    (hpar : R₁ * v₁ * s₁ = R₂ * v₂ * s₂)
    (h₁ : E - V₁ = 1 / 2 * R₁ * v₁ ^ 2) (h₂ : E - V₂ = 1 / 2 * R₂ * v₂ ^ 2) :
    R₁ * (E - V₁) * s₁ ^ 2 = R₂ * (E - V₂) * s₂ ^ 2 := by
  linear_combination (R₁ * s₁ ^ 2) * h₁ - (R₂ * s₂ ^ 2) * h₂
    + (1 / 2) * (R₁ * v₁ * s₁ + R₂ * v₂ * s₂) * hpar

/-- Equal potentials: `R₁ sin²θ₁ = R₂ sin²θ₂`. -/
theorem refraction_equal_potentials (R₁ R₂ K s₁ s₂ : ℝ) (hK : K ≠ 0)
    (h : R₁ * K * s₁ ^ 2 = R₂ * K * s₂ ^ 2) : R₁ * s₁ ^ 2 = R₂ * s₂ ^ 2 := by
  have : K * (R₁ * s₁ ^ 2 - R₂ * s₂ ^ 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hK
  · linarith

/-- Turning barrier: a real transmitted angle (`sin²θ₂ ≤ 1`) requires
`R₁ sin²θ₁ ≤ R₂`; beyond the critical angle the path returns to its own side. -/
theorem turning_barrier (R₁ R₂ s₁ s₂ : ℝ) (hR₂ : 0 < R₂)
    (h : R₁ * s₁ ^ 2 = R₂ * s₂ ^ 2) (hs₂ : s₂ ^ 2 ≤ 1) : R₁ * s₁ ^ 2 ≤ R₂ := by
  rw [h]
  nlinarith

/-- With regularized rigidity `Rᵢ = 1/(sᵢ² + η)`, equal potentials give
`sin²θ₂ = (s₂² + η)/(s₁² + η) · sin²θ₁`. -/
theorem regularized_refraction (σ₁ σ₂ η x₁ x₂ : ℝ) (hη : 0 < η)
    (h : 1 / (σ₁ ^ 2 + η) * x₁ = 1 / (σ₂ ^ 2 + η) * x₂) :
    x₂ = (σ₂ ^ 2 + η) / (σ₁ ^ 2 + η) * x₁ := by
  have h2 : σ₂ ^ 2 + η ≠ 0 := by positivity
  calc x₂ = (σ₂ ^ 2 + η) * (1 / (σ₂ ^ 2 + η) * x₂) := by
        rw [← mul_assoc, mul_one_div_cancel h2, one_mul]
    _ = (σ₂ ^ 2 + η) * (1 / (σ₁ ^ 2 + η) * x₁) := by rw [h]
    _ = (σ₂ ^ 2 + η) / (σ₁ ^ 2 + η) * x₁ := by ring

/-! ### Section 8: oblique Riesz projectors -/

/-- `Π₀ = [[1, 1], [0, 0]]`. -/
def obliqueP0 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

/-- `Π₁ = [[1, 0], [1, 0]]`. -/
def obliqueP1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 0]

/-- Both are idempotent (oblique projectors of rank one) and `Tr(Π₀ Π₁) = 2`,
outside the range `[0, 1]` of a squared cosine: persistence readouts must be
taken on the orthogonal projector onto the range, not the Riesz projector. -/
theorem oblique_trace_two :
    obliqueP0 * obliqueP0 = obliqueP0 ∧ obliqueP1 * obliqueP1 = obliqueP1 ∧
      Matrix.trace (obliqueP0 * obliqueP1) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [obliqueP0, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [obliqueP1, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Matrix.trace_fin_two]
    norm_num [obliqueP0, obliqueP1, Matrix.mul_apply, Fin.sum_univ_two]

end UPGDiracRefraction
