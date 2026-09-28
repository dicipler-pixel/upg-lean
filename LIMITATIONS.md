# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The modules are finite: real symmetric block Hamiltonians, finite projectors, and explicit
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
  The shift is not proved unitary here.
* Theorem 4.2 is proved pointwise (the floors `ε` and `9a⁴/16`) and on the normalized path; the
  passage along an arbitrary Hermitian path (Weyl ordering, the compressed-window limit) is not.
* Theorem 4.3 is proved in the one-channel case and, for many channels, as a statement about the
  eigenvalues `μₖ`; the block-determinant identity is Mathlib's, and that the glued operator has
  this block form is the paper's assumption.
* Not formalized: the phase transport law as a derivative and its integer loop integrals, the
  metric–curvature bound (proved in `iqgt-grassmannian-lean`), Module II (character varieties,
  the trichotomy), the realization on published tomography data, and the Kato-type Lipschitz
  bound of Section 8.

Formalization is evidence for the mathematics, not for the physical interpretation.
