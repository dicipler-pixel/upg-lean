# Provenance

Every Lean file is a byte-identical copy of a source in the private `operator-first`
repository (directory `research/upg/formal/`). The same files appear with identical hashes on
every UPG branch that carries them.

| Files | Branch | Commit |
| :--- | :--- | :--- |
| `UPGFeedback`, `UPGBlockFeedback`, `UPGProjectorMetric`, `UPGProjectorDynamics`, `UPGResolventFeedback`, `UPGPositiveFeedback` | `formal/upg-positive-shadow-2026-09-14` | `c4e045d41642` |
| `UPGInterfacePersistence`, `UPGInterfaceSpectrum` | `formal/upg-projector-dynamics-2026-09-13` | `264393685128` |
| `FalseControls/ZeroTimeMemory.lean` | `research/upg/formal/FalseControl.lean` on the same branches | same |

The feedback criterion of `UPGFeedback` passed CI in PR #28 (Actions run 34698809495). The
check in this repository is the verification of the complete set.

## Modules written for the v3.2 edition

`UPGAlgebra`, `UPGTorusAnchor`, `UPGObstruction` and `UPGDiracRefraction` were written for this
repository from *Universal Projector Geometry from Electrical Measurements*, edition v3.2
(September 2026, source `upg_final_v3_2.tex`), and are first checked here. Each theorem's
docstring names the section or result it formalizes.
