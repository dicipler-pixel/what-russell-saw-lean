# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written. Measured
masses, speeds and distances enter only as numerals or hypotheses.

* Binet's equation and its relativistic form are taken as the starting point; their derivation
  from the force law and from the Schwarzschild metric is not formalized.
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
