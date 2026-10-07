# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written. Measured
masses, speeds and distances enter only as numerals or hypotheses.

* Binet's equation and its relativistic form are taken as the starting point; their derivation
  from the force law and from the Schwarzschild metric is not formalized.
* Mechanical similarity is checked as exponent arithmetic. The scalings `v ∝ λ^(n/2)` and
  `T ∝ λ^(1 − n/2)` are inputs; `russell_speed_forces_inverse_cube` proves `n/2 = −1 → n = −2`,
  and the step from `n = −2` to an inverse-cube force is not formalized.
* `restoring_coefficients` checks `3 − 3 = 0` and `3 − 2 = 1`. Its docstring's "the orbit is a
  spiral" is the paper's reading of a vanishing restoring coefficient, not a proved statement
  about orbits. (`RussellRebuild.lean` is kept byte-identical to the deposit, so its comments
  are not edited.)
* `isco_from_potential` locates the circular orbit with `V′ = V″ = 0`, the marginally stable
  one; that no stable circular orbit exists for `r < 6M` is not formalized.
* The cone's eccentricity `e = cos β / cos α` is an input; Lean proves `e < 1 ⇔ α < β` for
  `0 < α < π/2` and `0 ≤ β ≤ π/2`.
* `mass_loss_drift` gives `ȧ = −a Ṁ/M` from `ȧ M + a Ṁ = 0`; the sign of `ȧ` is not stated.
* Reading Russell's axiom as the oscillator is the paper's interpretation. Lean proves energy
  conservation for the oscillator, not the interpretation.
* The apsidal angle is proved for the linearised equation: its solution `A cos(√κ θ)` is
  verified and its half-period is `π/√κ`. Uniqueness of solutions and the error of the
  linearisation for finite departures are not formalized.
* The ISCO is derived from the effective potential `V(r)` as stated; the potential itself is
  an input.
* Maxwell stress, Ampère's force and the Rankine vortex are checked as algebraic identities
  for the stated fields; no electromagnetic or fluid equations are solved.
* The inspiral and mass-loss results assume the stated rate laws; they do not derive them.
* Physlib's circular-orbit model is `v² = GM/r`; general (elliptic) Kepler orbits are not
  used.
* Nothing here tests Russell's physical claims directly; the ledger in the Zenodo deposit
  grades those.
