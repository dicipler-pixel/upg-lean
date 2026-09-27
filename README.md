<div align="center">

# Universal Projector Geometry — Lean proofs

**Machine-checked finite feedback algebra behind the UPG paper: when a retained sector evolves on its own, and how interface coupling shows up in the projector geometry.**

[![Lean proof check](https://github.com/dicipler-pixel/upg-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/upg-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-40-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21305024-blue)](https://doi.org/10.5281/zenodo.21305024)

Jeromie Beasley

</div>

---

## The idea in one line

Split a finite system into a retained sector and a hidden one, coupled by a block `B`. The
retained sector runs on its own exactly when `B = 0`, and every finite diagnostic of that
coupling agrees: the commutator `[H, P]`, the redistribution operator, the zero-time memory
Gram `B Bᵀ` and the cross-block projector metric all vanish together, and a nonzero coupling
is detected by each of them.

## Start here

| If you want to… | Open |
| :--- | :--- |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statement that must be rejected | [`FalseControls/`](FalseControls/) |

## What the library contains

| Subject | File | Theorems |
| :--- | :--- | :-: |
| **Finite feedback criterion**: redistribution zero ⇔ coupling zero ⇔ zero-time memory Gram zero | [`UPGFeedback`](UPGFeedback.lean) | 5 |
| **Adapted block form**: exact block form of `[H, P]`; four equivalent diagnostics of retained–hidden coupling | [`UPGBlockFeedback`](UPGBlockFeedback.lean) | 7 |
| **Projector metric**: the feedback Gram's trace is the squared coupling energy; the two oriented cross blocks of `[H, P]` carry equal energy; the factor-of-two identity | [`UPGProjectorMetric`](UPGProjectorMetric.lean) | 7 |
| **Projector dynamics**: a two-sided transport with endpoint derivatives `K` and `−K`; the finite bridge to the adapted generator | [`UPGProjectorDynamics`](UPGProjectorDynamics.lean) | 3 |
| **Resolvent feedback**: a Gram-factorized hidden response reduces to the zero-time Gram; nonzero coupling cannot give zero factorized feedback | [`UPGResolventFeedback`](UPGResolventFeedback.lean) | 3 |
| **Positive feedback**: a positive-definite hidden response detects every nonzero coupling | [`UPGPositiveFeedback`](UPGPositiveFeedback.lean) | 3 |
| **Interface persistence**: changing either diagonal sector at fixed coupling leaves the cross-block metric unchanged; memory strength equals the one-half squared tangent | [`UPGInterfacePersistence`](UPGInterfacePersistence.lean) | 6 |
| **Interface spectrum**: channel-by-channel Gram weights are nonnegative and vanish exactly when that channel's couplings vanish | [`UPGInterfaceSpectrum`](UPGInterfaceSpectrum.lean) | 6 |
| | **Total** | **40** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False control**: the claim that a nonzero one-channel coupling has zero memory Gram must
   fail to compile, for a mathematical reason.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*Universal Projector Geometry from Electrical Measurements*, Jeromie Beasley. DOI
[10.5281/zenodo.21305024](https://doi.org/10.5281/zenodo.21305024).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
