# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written. Measured
masses, speeds and distances enter only as numerals or hypotheses.

* The Binet linearisation is proved at the level of its slope; the apsidal angle `π/√(3 − p)`
  itself, and the derivation of the orbit equation from the force law, are not formalized.
* `gr_effective_steepness` takes the matching of the linearised coefficients as a hypothesis;
  the relativistic orbit equation `u'' + u = M/L² + 3Mu²` is not derived here.
* Maxwell stress, Ampère's force and the Rankine vortex are checked as algebraic identities
  for the stated fields; no electromagnetic or fluid equations are solved.
* The inspiral and mass-loss results assume the stated rate laws; they do not derive them.
* Physlib's circular-orbit model is `v² = GM/r`; general (elliptic) Kepler orbits are not
  used.
* Nothing here tests Russell's physical claims directly; the ledger in the Zenodo deposit
  grades those.
