/-
What Russell Saw — the paired-motion axiom and the orbit-speed law, stated against Physlib's
own models rather than against one written-out solution.

* Section I of the paper: for every trajectory of a harmonic oscillator that obeys its
  equation of motion (not only `A cos ωt`), kinetic plus potential energy is the same at
  every time. This is Russell's "every change is a pair of opposed motions summing to a
  constant", proved from Physlib's Lagrangian model of the oscillator.
* Section II: in Physlib's circular-orbit model `v² = GM/r`, quadrupling the radius halves
  the speed. Russell's law `v ∝ 1/a` would quarter it, so it cannot hold for an
  inverse-square pull.

Jeromie Beasley, 2026.
-/
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.ClassicalMechanics.OrbitalMechanics.VisViva

namespace RussellPhyslib

open ClassicalMechanics ContDiff

/-- **The paired-motion constant.** Along every solution of the oscillator's equation of
motion, the kinetic store plus the potential store is constant in time. -/
theorem paired_motion_constant (S : HarmonicOscillator) (x : Time → EuclideanSpace ℝ (Fin 1))
    (hx : ContDiff ℝ ∞ x) (h : S.EquationOfMotion x) (t : Time) :
    S.kineticEnergy x t + S.potentialEnergy (x t) =
      S.kineticEnergy x 0 + S.potentialEnergy (x 0) :=
  S.energy_conservation_of_equationOfMotion' x hx h t

/-- **Newton's orbital speed.** For a circular orbit, `v(4r)² = v(r)² / 4`: quadrupling the
radius halves the speed. -/
theorem circular_speed_quarter_radius (sys : VisViva) (r : ℝ) (hr : 0 < r) (hG : 0 < sys.G)
    (hM : 0 < sys.M) :
    (VisViva.speedCircular sys ⟨4 * r⟩) ^ 2 = (VisViva.speedCircular sys ⟨r⟩) ^ 2 / 4 := by
  rw [VisViva.speedCircular_sq sys ⟨4 * r⟩ (by positivity) hG hM,
    VisViva.speedCircular_sq sys ⟨r⟩ hr hG hM]
  field_simp

/-- **Russell's speed law fails for an inverse-square pull.** If `v ∝ 1/a` held, then
`v(4r)² = v(r)² / 16`; together with Newton's `v(4r)² = v(r)² / 4` this forces `v(r) = 0`,
which is impossible for a positive mass. -/
theorem russell_speed_law_fails (sys : VisViva) (r : ℝ) (hr : 0 < r) (hG : 0 < sys.G)
    (hM : 0 < sys.M)
    (hRussell : (VisViva.speedCircular sys ⟨4 * r⟩) ^ 2 =
      (VisViva.speedCircular sys ⟨r⟩) ^ 2 / 16) : False := by
  have hN := circular_speed_quarter_radius sys r hr hG hM
  have hv : 0 < (VisViva.speedCircular sys ⟨r⟩) ^ 2 := by
    rw [VisViva.speedCircular_sq sys ⟨r⟩ hr hG hM]
    positivity
  linarith

end RussellPhyslib
