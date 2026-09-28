import Mathlib

/-!
# The redistribution operator in any ring, and the complex adapted pair

Section 1 of the paper introduces the redistribution operator

    F(Ω, Π) = (1 - Π) Ω Π + Π Ω (1 - Π)

for a structural transition generator `Ω` and a projector `Π`. The earlier
modules of this library prove its block form for real symmetric blocks. This
module proves the paper's statements in the generality the paper uses:

* Theorem 1.2 (equivalent forms, off-diagonal support) and Theorem 1.3
  (compatibility criterion) for an idempotent `Π` in **any** ring, so they
  hold for real and complex matrices and for operators alike;
* tracelessness of `F` for square matrices over any commutative ring;
* Proposition 1.5 for **complex** blocks with the conjugate transpose, the
  case the paper gates only numerically: the block form of `[H, Π]` and of
  `F(H, Π)`, the square `[H, Π]^2 = -diag(B Bᴴ, Bᴴ B)`, the energy identity
  `Tr([H, Π]ᴴ [H, Π]) = 2 Tr K(0)`, and the equivalence of all four
  diagnostics with `B = 0`.
-/

open Matrix
open scoped ComplexOrder

namespace UPGAlgebra

section Ring

variable {R : Type*} [Ring R]

/-- The redistribution operator `F(Ω, Π) = (1 - Π) Ω Π + Π Ω (1 - Π)`. -/
def redistributionOp (Ω P : R) : R := (1 - P) * Ω * P + P * Ω * (1 - P)

/-- Theorem 1.2, first form: `F = ΩΠ + ΠΩ - 2ΠΩΠ` (no idempotence needed). -/
theorem redistribution_eq_sum_form (Ω P : R) :
    redistributionOp Ω P = Ω * P + P * Ω - 2 * (P * Ω * P) := by
  unfold redistributionOp
  noncomm_ring

/-- Theorem 1.2, commutator form: `F = [Ω, Π] Π + Π [Π, Ω]` for idempotent `Π`. -/
theorem redistribution_eq_commutator_form (Ω P : R) (hP : P * P = P) :
    redistributionOp Ω P = (Ω * P - P * Ω) * P + P * (P * Ω - Ω * P) := by
  rw [redistribution_eq_sum_form]
  calc Ω * P + P * Ω - 2 * (P * Ω * P)
      = Ω * P + P * Ω - 2 * (P * Ω * P) + (Ω * (P * P - P) + (P * P - P) * Ω) := by
        rw [hP, sub_self, mul_zero, zero_mul, add_zero, add_zero]
    _ = (Ω * P - P * Ω) * P + P * (P * Ω - Ω * P) := by noncomm_ring

/-- `Π (1 - Π) = 0` for an idempotent. -/
theorem proj_mul_compl (P : R) (hP : P * P = P) : P * (1 - P) = 0 := by
  rw [mul_sub, mul_one, hP, sub_self]

/-- `(1 - Π) Π = 0` for an idempotent. -/
theorem compl_mul_proj (P : R) (hP : P * P = P) : (1 - P) * P = 0 := by
  rw [sub_mul, one_mul, hP, sub_self]

/-- The complement of an idempotent is idempotent. -/
theorem compl_idempotent (P : R) (hP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]

/-- Theorem 1.2, support: `Π F Π = 0`. -/
theorem proj_redistribution_proj (Ω P : R) (hP : P * P = P) :
    P * redistributionOp Ω P * P = 0 := by
  have e : P * redistributionOp Ω P * P
      = (P * (1 - P)) * Ω * (P * P) + (P * P) * Ω * ((1 - P) * P) := by
    unfold redistributionOp; noncomm_ring
  rw [e, proj_mul_compl P hP, compl_mul_proj P hP]
  simp

/-- Theorem 1.2, support: `(1 - Π) F (1 - Π) = 0`. -/
theorem compl_redistribution_compl (Ω P : R) (hP : P * P = P) :
    (1 - P) * redistributionOp Ω P * (1 - P) = 0 := by
  have e : (1 - P) * redistributionOp Ω P * (1 - P)
      = ((1 - P) * (1 - P)) * Ω * (P * (1 - P))
        + ((1 - P) * P) * Ω * ((1 - P) * (1 - P)) := by
    unfold redistributionOp; noncomm_ring
  rw [e, proj_mul_compl P hP, compl_mul_proj P hP]
  simp

/-- Theorem 1.3 (compatibility criterion): `F(Ω, Π) = 0` if and only if `Ω`
commutes with `Π`. -/
theorem redistribution_eq_zero_iff_commute (Ω P : R) (hP : P * P = P) :
    redistributionOp Ω P = 0 ↔ Ω * P = P * Ω := by
  have h1 := proj_mul_compl P hP
  have h2 := compl_mul_proj P hP
  have hQ := compl_idempotent P hP
  constructor
  · intro hF
    have e1 : (1 - P) * redistributionOp Ω P * P = (1 - P) * Ω * P := by
      have : (1 - P) * redistributionOp Ω P * P
          = ((1 - P) * (1 - P)) * Ω * (P * P) + ((1 - P) * P) * Ω * ((1 - P) * P) := by
        unfold redistributionOp; noncomm_ring
      rw [this, hQ, hP, h2]
      simp
    have e2 : P * redistributionOp Ω P * (1 - P) = P * Ω * (1 - P) := by
      have : P * redistributionOp Ω P * (1 - P)
          = (P * (1 - P)) * Ω * (P * (1 - P)) + (P * P) * Ω * ((1 - P) * (1 - P)) := by
        unfold redistributionOp; noncomm_ring
      rw [this, hQ, hP, h1]
      simp
    rw [hF, mul_zero, zero_mul] at e1 e2
    have a : Ω * P - P * Ω * P = 0 := by
      have : (1 - P) * Ω * P = Ω * P - P * Ω * P := by noncomm_ring
      rw [← this, ← e1]
    have b : P * Ω - P * Ω * P = 0 := by
      have : P * Ω * (1 - P) = P * Ω - P * Ω * P := by noncomm_ring
      rw [← this, ← e2]
    rw [sub_eq_zero] at a b
    exact a.trans b.symm
  · intro hc
    have e : redistributionOp Ω P = ((1 - P) * P) * Ω + Ω * (P * (1 - P)) := by
      unfold redistributionOp
      calc (1 - P) * Ω * P + P * Ω * (1 - P)
          = (1 - P) * (Ω * P) + (P * Ω) * (1 - P) := by noncomm_ring
        _ = (1 - P) * (P * Ω) + (Ω * P) * (1 - P) := by rw [hc]
        _ = ((1 - P) * P) * Ω + Ω * (P * (1 - P)) := by noncomm_ring
    rw [e, h1, h2]
    simp

end Ring

section Trace

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- Theorem 1.2, tracelessness: `Tr F(Ω, Π) = 0` for an idempotent matrix `Π`. -/
theorem trace_redistribution (Ω P : Matrix n n K) (hP : P * P = P) :
    trace (redistributionOp Ω P) = 0 := by
  unfold redistributionOp
  rw [trace_add, trace_mul_cycle, trace_mul_comm (P * Ω) (1 - P), ← Matrix.mul_assoc,
    proj_mul_compl P hP, compl_mul_proj P hP]
  simp

end Trace

section Complex

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Adapted complex Hermitian block Hamiltonian `[[A, B], [Bᴴ, D]]`. -/
def blockHamiltonianC (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    Matrix (r ⊕ h) (r ⊕ h) ℂ :=
  fromBlocks A B Bᴴ D

/-- Retained projector `[[I, 0], [0, 0]]`. -/
def retainedProjectionC : Matrix (r ⊕ h) (r ⊕ h) ℂ := fromBlocks 1 0 0 0

/-- `[H, Π]` for the complex adapted pair. -/
def commutatorC (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    Matrix (r ⊕ h) (r ⊕ h) ℂ :=
  blockHamiltonianC A B D * retainedProjectionC - retainedProjectionC * blockHamiltonianC A B D

/-- The retained projector is idempotent. -/
theorem retainedProjectionC_idem :
    (retainedProjectionC : Matrix (r ⊕ h) (r ⊕ h) ℂ) * retainedProjectionC
      = retainedProjectionC := by
  simp [retainedProjectionC, fromBlocks_multiply]

/-- Proposition 1.5(i), complex case: `[H, Π] = [[0, -B], [Bᴴ, 0]]`, independent
of the diagonal sectors. -/
theorem commutatorC_eq_blocks (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    commutatorC A B D = fromBlocks 0 (-B) Bᴴ 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [commutatorC, blockHamiltonianC, retainedProjectionC, fromBlocks_multiply]

/-- Proposition 1.5(i), complex case: `F(H, Π) = [[0, B], [Bᴴ, 0]]`. -/
theorem redistributionC_eq_blocks (A : Matrix r r ℂ) (B : Matrix r h ℂ)
    (D : Matrix h h ℂ) :
    redistributionOp (blockHamiltonianC A B D) retainedProjectionC
      = fromBlocks 0 B Bᴴ 0 := by
  have hc : (1 : Matrix (r ⊕ h) (r ⊕ h) ℂ) - retainedProjectionC = fromBlocks 0 0 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [retainedProjectionC, Matrix.one_apply]
  unfold redistributionOp
  rw [hc]
  ext i j
  cases i <;> cases j <;>
    simp [blockHamiltonianC, retainedProjectionC, fromBlocks_multiply]

/-- Proposition 1.5(iii), complex case: `[H, Π]^2 = -diag(B Bᴴ, Bᴴ B)`; its
retained block is `-K(0)` with `K(0) = B Bᴴ`. -/
theorem commutatorC_sq (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    commutatorC A B D * commutatorC A B D = fromBlocks (-(B * Bᴴ)) 0 0 (-(Bᴴ * B)) := by
  rw [commutatorC_eq_blocks, fromBlocks_multiply]
  simp

/-- The Gram matrix of `[H, Π]` is `diag(B Bᴴ, Bᴴ B)`. -/
theorem commutatorC_gram (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    (commutatorC A B D)ᴴ * commutatorC A B D = fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B) := by
  rw [commutatorC_eq_blocks, fromBlocks_conjTranspose, fromBlocks_multiply]
  simp

/-- Trace of a block-diagonal matrix. -/
theorem trace_fromBlocks_diag (X : Matrix r r ℂ) (Y : Matrix h h ℂ) :
    trace (fromBlocks X 0 0 Y) = trace X + trace Y := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Proposition 1.5(ii), complex case: `‖[H, Π]‖_F^2 = Tr([H,Π]ᴴ[H,Π]) = 2 Tr K(0)`. -/
theorem commutatorC_energy (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    trace ((commutatorC A B D)ᴴ * commutatorC A B D) = 2 * trace (B * Bᴴ) := by
  rw [commutatorC_gram, trace_fromBlocks_diag, trace_mul_comm Bᴴ B]
  ring

/-- `K(0) = B Bᴴ` has zero trace only when the coupling vanishes. -/
theorem trace_memoryC_eq_zero_iff (B : Matrix r h ℂ) : trace (B * Bᴴ) = 0 ↔ B = 0 :=
  trace_mul_conjTranspose_self_eq_zero_iff

/-- Proposition 1.5(iv), complex case: `[H, Π] = 0 ↔ F(H, Π) = 0 ↔ B = 0 ↔ K(0) = 0`. -/
theorem feedbackC_equivalences (A : Matrix r r ℂ) (B : Matrix r h ℂ) (D : Matrix h h ℂ) :
    (commutatorC A B D = 0 ↔ B = 0) ∧
    (redistributionOp (blockHamiltonianC A B D) retainedProjectionC = 0 ↔ B = 0) ∧
    (B * Bᴴ = 0 ↔ B = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [commutatorC_eq_blocks]
    constructor
    · intro hC
      ext i j
      have := congrArg (fun M : Matrix (r ⊕ h) (r ⊕ h) ℂ => M (Sum.inl i) (Sum.inr j)) hC
      simpa using this
    · intro hB
      subst hB
      simp
  · rw [redistributionC_eq_blocks]
    constructor
    · intro hF
      ext i j
      have := congrArg (fun M : Matrix (r ⊕ h) (r ⊕ h) ℂ => M (Sum.inl i) (Sum.inr j)) hF
      simpa using this
    · intro hB
      subst hB
      simp
  · constructor
    · intro hK
      rw [← trace_memoryC_eq_zero_iff, hK, trace_zero]
    · intro hB
      subst hB
      simp

end Complex

end UPGAlgebra
