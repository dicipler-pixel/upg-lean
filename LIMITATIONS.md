# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The modules are finite: adapted block Hamiltonians over ℝ and ℂ, finite projectors, and explicit
  transport derivative hypotheses. No matrix exponential, continuum limit, or infinite-
  dimensional feedback is formalized.
* No physical dictionary is formalized: nothing here identifies the blocks with electrons,
  light, a spacetime metric, or a measured electrical response. The paper's measurement
  protocol and its data analysis are outside these proofs.
* `UPGProjectorDynamics` takes the endpoint derivatives of the transport as hypotheses; it does
  not construct the transport.
* The torus anchor takes the relator's spectrum as a family of unit complex numbers whose product
  is one; that this is the spectrum of `UVUᴴVᴴ` (unit modulus, product equal to the determinant) is
  standard and not re-proved. The Exel–Loring identification with a determinant winding
  (Theorem 4.5(iv)) and the Bott-index/Chern-number correspondence are cited, not formalized.
  Neither the clock nor the shift is proved unitary here, so `scalar_relator`, which is stated
  for unitaries, is not instantiated at the clock–shift pair.
* Theorem 4.2 is proved pointwise (the floors `ε` and `9a⁴/16`) and on the normalized path; the
  passage along an arbitrary Hermitian path (Weyl ordering, the compressed-window limit, and the
  strictness of the floor `2aε` on every continuous path that the `window_floor` docstring
  mentions) is not.
* Theorem 4.3 is proved in the one-channel case and, for many channels, as a statement about the
  eigenvalues `μₖ`; the block-determinant identity is Mathlib's, and that the glued operator has
  this block form is the paper's assumption. That all `μₖ = 0` forces the boundary product, and
  hence the seam coupling, to vanish (the remark in the `anomaly_eq_zero_iff` docstring) is not
  formalized.
* `UPGDiracRefraction` proves `{σ₃, D} = 0` for `2 × 2` off-diagonal matrices with scalar entries,
  and `D² = |w|² I` for the Hermitian ones `[[0, w], [w̄, 0]]`. The symmetry of the spectrum under
  `λ ↦ −λ` and the eigenvalues `±|w|` named in its docstrings are consequences that are not
  formalized, and the block (matrix-entry) form of the twisted torus family is not treated.
* `sectorProjector u` is proved idempotent (for `|u| = 1`) with trace one. Its identification with
  a spectral projector of the off-diagonal Dirac block, and the sign convention of Section 4.1,
  are not formalized.
* The chiral ledger calibration is checked only as `ln(1 + (e^{π²/12} − 1)) = π²/12`; where the
  value `π²/12` comes from is not formalized.
* Not formalized: the phase transport law as a derivative and its integer loop integrals, the
  metric–curvature bound (proved in `iqgt-grassmannian-lean`), Module II (character varieties,
  the trichotomy), the realization on published tomography data, and the Kato-type Lipschitz
  bound of Section 8.

Formalization is evidence for the mathematics, not for the physical interpretation.
