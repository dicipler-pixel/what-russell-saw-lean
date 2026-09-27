<div align="center">

# What Russell Saw — Lean proofs

**The mathematics behind a century-later reading of Walter Russell's universe of paired motion, checked by the Lean kernel on every push.**

[![Lean proof check](https://github.com/dicipler-pixel/what-russell-saw-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/what-russell-saw-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-28-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Physlib](https://img.shields.io/badge/uses-Physlib-8A2BE2)
![License](https://img.shields.io/badge/License-MIT-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22986656-blue)](https://doi.org/10.5281/zenodo.22986656)

Jeromie Beasley

</div>

---

## The idea in one line

Russell's axiom is one substance whose every change is a pair of opposed motions summing to a
constant. That is the oscillator: kinetic and potential energy trade places and their sum never
moves. Where Russell's laws of motion go wrong, they go wrong in a precise way: his planet
speeds `v ∝ 1/a` belong to an inverse-cube pull, and an inverse-cube pull is exactly where
orbits stop closing. General relativity reaches that same steepness at `r = 6M`, the innermost
stable orbit.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| §I | Paired-motion constant for **every** solution of the oscillator's equation of motion (Physlib) | `RussellPhyslib.paired_motion_constant` |
| §I | The explicit solution `A cos ωt` keeps `½kx² + p²/2m = ½kA²` | `pendulum_energy_constant` |
| §II | Mechanical similarity: time exponent `1 − n/2` for `U ∝ rⁿ` | `similarity_time_exponent` |
| §II | Russell's `v ∝ 1/a` forces `n = −2` (an inverse-cube force); period exponents 2 and 3/2 | `russell_speed_forces_inverse_cube`, `period_exponents` |
| §II | Newton's circular orbit: quadrupling the radius halves the speed; Russell's speed law contradicts it (Physlib) | `RussellPhyslib.circular_speed_quarter_radius`, `RussellPhyslib.russell_speed_law_fails` |
| §III | Binet slope at the circular orbit is `p − 2`; restoring coefficient `3 − p` vanishes at Russell's `p = 3` | `binet_slope_at_circle`, `restoring_coefficients` |
| §III | Relativistic effective steepness `2 + 6M/r` equals 3 exactly at `r = 6M` | `gr_effective_steepness`, `isco_is_russell` |
| §IV | The effective potential sits above its minimum by a perfect square; with no spin there is no valley | `ueff_square`, `ueff_min`, `no_spin_no_valley` |
| §V | Neutral point `x = d/(1 + √(m/M))`; mutual centre; the Earth–Moon centre lies inside the Earth | `neutral_point`, `barycentre_balance`, `earth_moon_barycentre_inside` |
| §VI | Maxwell stress: tension along a field line, pressure across; parallel currents attract; the old ampere definition | `maxwell_stress_along_across`, `ampere_sign`, `ampere_definition` |
| §VII | Rankine vortex pressure deficit `ρv²`; 9,720 Pa at 90 m/s | `rankine_total_deficit`, `rankine_90` |
| §VIII | The tide is a difference of pulls: two bulges | `tide_two_bulges` |
| §IX | Mass loss widens orbits; the inspiral step grows as `a^(−3/2)` | `mass_loss_drift`, `inspiral_step` |
| §X | A cone cut is an ellipse exactly when the plane is steeper than the cone | `cone_ellipse_iff` |
| §XI | Periodic-table rows 2, 8, 8, 18, 18, 32, 32 hold 118 elements; the valence wave is symmetric | `row_lengths`, `valence_palindrome` |

Files: [`lean/RussellRebuild.lean`](lean/RussellRebuild.lean) (25 theorems, Mathlib) and
[`lean/RussellPhyslib.lean`](lean/RussellPhyslib.lean) (3 theorems, Physlib). What is not
proved is in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build** against Lean v4.34.1 with [Physlib](https://github.com/leanprover-community/physlib), which brings Mathlib v4.34.1.
2. **Independent replay** of every module in Lean's separate kernel checker.
3. **Axiom audit**: every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
4. **False controls**: three deliberately false statements must fail, for a mathematical reason.

## The paper

*What Russell Saw: Walter Russell's Universe of Paired Motion, Read Against a Century of
Physics*, Jeromie Beasley. DOI [10.5281/zenodo.22986656](https://doi.org/10.5281/zenodo.22986656).
The deposit also holds the paper, the interactive mixer, the ledger grading 386 claims and
199 laws, and the numerical scripts.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code is released under the
[MIT License](LICENSE). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
