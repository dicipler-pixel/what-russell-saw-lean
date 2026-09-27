# Provenance

| File | Source |
| :--- | :--- |
| `lean/RussellRebuild.lean`, `lean/Audit.lean`, `lean/axiom_audit.txt` | Byte-identical to `russell-rebuild_v1.zip` (`lean/`), the Lean certificates of the Zenodo deposit |
| `lean/RussellPhyslib.lean` | Written for this repository: the paired-motion and orbit-speed results restated against Physlib's harmonic-oscillator and circular-orbit models |
| `lean/RussellOrbits.lean` | Written for this repository: the orbit claims of §III as derivatives, the apsidal angle and the ISCO from the effective potential |
| `FalseControls/*.lean` | Written for this repository |

The deposit pinned Mathlib at `d13f23b7`; this repository builds the same file against
Mathlib v4.34.1 through Physlib (commit `35d1bb4`). The SHA-256 of every checked file is
written to `verification/report.json` on each run.
