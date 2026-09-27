/-
# SCRIPT: RussellRebuild
What Russell Saw — machine-checked kernel of the rebuild.
Jeromie Beasley, 2026.

Each theorem certifies one mathematical step used in the paper. Physical inputs
(measured masses, speeds, distances) enter only as hypotheses or as numerals.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace RussellRebuild

open Real

/-! ## I. The cosmic pendulum: one constant, two stores -/

/-- An oscillator `x = A cos(ωt)`, `p = -mωA sin(ωt)`, with `k = mω²`, keeps
`½kx² + p²/2m = ½kA²` at every instant. -/
theorem pendulum_energy_constant (m ω A t : ℝ) (hm : m ≠ 0) :
    (1/2) * (m * ω^2) * (A * cos (ω * t))^2 + (-(m * ω * A * sin (ω * t)))^2 / (2 * m)
      = (1/2) * (m * ω^2) * A^2 := by
  have h : cos (ω * t) ^ 2 + sin (ω * t) ^ 2 = 1 := cos_sq_add_sin_sq (ω * t)
  calc (1/2) * (m * ω^2) * (A * cos (ω * t))^2 + (-(m * ω * A * sin (ω * t)))^2 / (2 * m)
        = (1/2) * (m * ω^2) * A^2 * (cos (ω * t) ^ 2 + sin (ω * t) ^ 2) := by
          field_simp
    _ = (1/2) * (m * ω^2) * A^2 := by rw [h]; ring

/-! ## II. Mechanical similarity: Russell's planet laws form one world -/

/-- Scaling lengths by `λ` and times by `λ^(1-n/2)` matches the force scaling
`λ^(n-1)` of a potential `U ∝ r^n`. -/
theorem similarity_time_exponent (lam n : ℝ) (hl : 0 < lam) :
    lam / (lam ^ (1 - n/2)) ^ (2:ℝ) = lam ^ (n - 1) := by
  rw [← rpow_mul hl.le]
  rw [div_eq_iff (rpow_pos_of_pos hl _).ne']
  rw [← rpow_add hl]
  conv_lhs => rw [← rpow_one lam]
  congr 1; ring

/-- Speeds scale as `λ^(n/2)`; Russell's `v ∝ 1/a` therefore forces `n = -2`. -/
theorem russell_speed_forces_inverse_cube (n : ℝ) (h : n / 2 = -1) : n = -2 := by linarith

/-- With `n = -2` the period exponent `1 - n/2` is `2` (Russell's `T ∝ a²`);
with Newton's `n = -1` it is `3/2` (Kepler's third law). -/
theorem period_exponents : (1 - (-2:ℝ)/2 = 2) ∧ (1 - (-1:ℝ)/2 = 3/2) := by
  constructor <;> norm_num

/-! ## III. The apsidal angle and the spiral -/

/-- Linearising Binet's equation `u'' + u = C u^(p-2)` about its circular orbit
`u₀ = C u₀^(p-2)` gives restoring coefficient `1 - (p-2) = 3 - p`: the slope of the
right-hand side at the circle is exactly `p - 2`. -/
theorem binet_slope_at_circle (C p u0 : ℝ) (hu : 0 < u0) (hc : C * u0 ^ (p - 2) = u0) :
    C * ((p - 2) * u0 ^ (p - 2 - 1)) = p - 2 := by
  have h1 : u0 ^ (p - 2 - 1) = u0 ^ (p - 2) / u0 := by
    rw [rpow_sub_one hu.ne']
  rw [h1]
  have hu' : u0 ≠ 0 := hu.ne'
  field_simp
  linear_combination (p - 2) * hc

/-- At Russell's `p = 3` the restoring coefficient vanishes: no oscillation, no return of
the far point — the orbit is a spiral. At Newton's `p = 2` it is `1`: half a turn. -/
theorem restoring_coefficients : (3 - (3:ℝ) = 0) ∧ (3 - (2:ℝ) = 1) := by
  constructor <;> norm_num

/-- General relativity: `u'' + u = M/L² + 3Mu²` linearised about `u₀` gives coefficient
`1 - 6Mu₀`; matching it to `3 - p` gives the effective steepness `p = 2 + 6Mu₀`. -/
theorem gr_effective_steepness (M u0 p : ℝ) (h : 3 - p = 1 - 6 * M * u0) :
    p = 2 + 6 * M * u0 := by linarith

/-- The effective steepness reaches Russell's `p = 3` exactly at `r = 6M`
(the innermost stable circular orbit, in units `G = c = 1`). -/
theorem isco_is_russell (M r : ℝ) (hr : 0 < r) (hM : 0 < M) :
    2 + 6 * M / r = 3 ↔ r = 6 * M := by
  constructor
  · intro h
    have : 6 * M / r = 1 := by linarith
    field_simp at this; linarith
  · intro h; subst h; field_simp; ring

/-! ## IV. "A true position for every potential" -/

/-- The effective potential `U(r) = -k/r + L²/(2r²)` sits above its value at
`r_c = L²/k` by a perfect square: `r_c` is the unique true position. -/
theorem ueff_square (k L r : ℝ) (hk : 0 < k) (hL : L ≠ 0) (hr : 0 < r) :
    (-k / r + L^2 / (2 * r^2)) - (-k / (L^2/k) + L^2 / (2 * (L^2/k)^2))
      = L^2 / 2 * (1 / r - k / L^2)^2 := by
  have hr' : r ≠ 0 := hr.ne'
  have hk' : k ≠ 0 := hk.ne'
  have hL2 : L^2 ≠ 0 := pow_ne_zero 2 hL
  field_simp
  ring

theorem ueff_min (k L r : ℝ) (hk : 0 < k) (hL : L ≠ 0) (hr : 0 < r) :
    -k / (L^2/k) + L^2 / (2 * (L^2/k)^2) ≤ -k / r + L^2 / (2 * r^2) := by
  have h := ueff_square k L r hk hL hr
  have : 0 ≤ L^2 / 2 * (1 / r - k / L^2)^2 := by positivity
  linarith

/-- With the angular momentum taken away (`L = 0`) there is no valley: `-k/r` rises
strictly with `r`, so the body slides straight in. -/
theorem no_spin_no_valley (k r1 r2 : ℝ) (hk : 0 < k) (h1 : 0 < r1) (h12 : r1 < r2) :
    -k / r1 < -k / r2 := by
  have h2 : 0 < r2 := lt_trans h1 h12
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left hk h1 h12

/-! ## V. Two bodies: the neutral point and the mutual centre -/

/-- The point where two pulls balance: at distance `x = d/(1+√(m/M))` from the mass `M`
(so nearer the smaller mass `m`), `M/x² = m/(d-x)²`. -/
theorem neutral_point (M m d : ℝ) (hM : 0 < M) (hm : 0 < m) (hd : 0 < d) :
    let s := Real.sqrt (m / M)
    let x := d / (1 + s)
    M * (d - x)^2 = m * x^2 := by
  intro s x
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = m / M := Real.sq_sqrt (div_nonneg hm.le hM.le)
  have h1 : 0 < 1 + s := by linarith
  have hx : d - x = d * s / (1 + s) := by
    simp only [x]; field_simp; ring
  rw [hx]
  simp only [x]
  field_simp
  have key : M * s^2 = m := by rw [hs2]; field_simp
  linear_combination key

/-- Russell's "mutual gravitative center": `r_b = d·m/(M+m)` balances `M r_b = m (d - r_b)`. -/
theorem barycentre_balance (M m d : ℝ) (h : 0 < M + m) :
    M * (d * m / (M + m)) = m * (d - d * m / (M + m)) := by
  field_simp; ring

/-- For the Earth and Moon (masses in kg, distance in km) the mutual centre lies within
the Earth's radius of 6,371 km. -/
theorem earth_moon_barycentre_inside :
    (384400 : ℝ) * 7.342e22 / (5.9722e24 + 7.342e22) < 6371 := by norm_num

/-! ## VI. Opposed and parallel flows -/

/-- Maxwell's magnetic stress `T_ij = B_iB_j - ½δ_ij B²` (units μ₀ = 1) for a field along
`x`: along the line it is `+½B²` (tension, the line pulls); across it `-½B²`
(pressure, the line pushes). -/
theorem maxwell_stress_along_across (b : ℝ) :
    (b * b - (1/2) * b^2 = (1/2) * b^2) ∧ (0 * 0 - (1/2) * b^2 = -((1/2) * b^2)) := by
  constructor <;> ring

/-- Ampère: the force per length `μ₀ I₁ I₂ /(2π d)` is attractive (positive) exactly when
the currents run the same way. -/
theorem ampere_sign (mu0 I1 I2 d : ℝ) (hmu : 0 < mu0) (hd : 0 < d) :
    0 < mu0 * I1 * I2 / (2 * π * d) ↔ 0 < I1 * I2 := by
  have hpos : 0 < 2 * π * d := by positivity
  constructor
  · intro h
    have h' : 0 < mu0 * (I1 * I2) := by
      have := (div_pos_iff.mp h)
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith [show mu0 * I1 * I2 = mu0 * (I1 * I2) by ring]
      · linarith
    exact (pos_iff_pos_of_mul_pos h').mp hmu
  · intro h
    apply div_pos _ hpos
    have := mul_pos hmu h
    linarith [show mu0 * I1 * I2 = mu0 * (I1 * I2) by ring]

/-- The old SI definition: one ampere in each of two wires one metre apart,
`μ₀ = 4π×10⁻⁷`, gives exactly `2×10⁻⁷` newton per metre. -/
theorem ampere_definition : (4 * π * 1e-7) * 1 * 1 / (2 * π * 1) = 2e-7 := by
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-! ## VII. The vortex -/

/-- Rankine vortex with core radius `R` and spin `Ω` (peak speed `v = ΩR`): the pressure
deficit inside the core, `ρΩ²R²/2`, plus the deficit outside, `ρv²/2`, total `ρv²`. -/
theorem rankine_total_deficit (ρ Ω R : ℝ) :
    ρ * Ω^2 * R^2 / 2 + ρ * (Ω * R)^2 / 2 = ρ * (Ω * R)^2 := by ring

/-- At 90 m/s and air density 1.2 kg/m³ that deficit is 9,720 Pa (97.2 hPa). -/
theorem rankine_90 : (1.2 : ℝ) * 90^2 = 9720 := by norm_num

/-! ## VIII. The tide is a difference of pulls -/

/-- For `0 < R < d`, the near side of a body is pulled harder than its centre, and the
centre harder than the far side: two bulges. -/
theorem tide_two_bulges (GM d R : ℝ) (hG : 0 < GM) (hR : 0 < R) (hRd : R < d) :
    GM / d^2 < GM / (d - R)^2 ∧ GM / (d + R)^2 < GM / d^2 := by
  have hd : 0 < d := lt_trans hR hRd
  have h1 : 0 < d - R := by linarith
  constructor
  · apply div_lt_div_of_pos_left hG (by positivity)
    nlinarith
  · apply div_lt_div_of_pos_left hG (by positivity)
    nlinarith

/-! ## IX. The slow spiral -/

/-- Constant angular momentum and a slowly shrinking central mass keep `a·M` fixed; then
`ȧ = -a·Ṁ/M`: as the Sun loses mass, every orbit widens. -/
theorem mass_loss_drift (a M adot Mdot : ℝ) (hM : M ≠ 0) (h : adot * M + a * Mdot = 0) :
    adot = -a * Mdot / M := by
  field_simp; linarith

/-- A gravitational-wave inspiral, `ȧ = -K a⁻³`, with period `P = c a^(3/2)`: the step per
turn scales as `a^(-3/2)`, larger as the orbit shrinks. -/
theorem inspiral_step (a : ℝ) (ha : 0 < a) :
    a ^ (-3:ℝ) * a ^ ((3:ℝ)/2) = a ^ (-(3:ℝ)/2) := by
  rw [← rpow_add ha]; norm_num

/-! ## X. The cone -/

/-- Cutting a cone of half-angle `α` with a plane at `β` to the axis gives
`e = cos β / cos α`; the cut is an ellipse (`e < 1`) exactly when `β > α`. -/
theorem cone_ellipse_iff (α β : ℝ) (hα : 0 < α) (hαp : α < π/2) (hβ : 0 ≤ β) (hβp : β ≤ π/2) :
    cos β / cos α < 1 ↔ α < β := by
  have hca : 0 < cos α := cos_pos_of_mem_Ioo ⟨by linarith, hαp⟩
  rw [div_lt_one hca]
  constructor
  · intro h
    by_contra hle0
    have hle : β ≤ α := not_lt.mp hle0
    have : cos α ≤ cos β := cos_le_cos_of_nonneg_of_le_pi hβ (by linarith) hle
    linarith
  · intro h
    exact cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) hβp h

/-! ## XI. The octave, corrected -/

/-- The rows of the periodic table take shell capacities `2n²` in the order
`n = 1,2,2,3,3,4,4`: lengths 2, 8, 8, 18, 18, 32, 32, holding 118 elements. -/
theorem row_lengths :
    [1, 2, 2, 3, 3, 4, 4].map (fun n : ℕ => 2 * n^2) = [2, 8, 8, 18, 18, 32, 32] ∧
    [2, 8, 8, 18, 18, 32, 32].sum = 118 := by
  constructor <;> decide

/-- Russell's valence wave 1,2,3,4,3,2,1 is symmetric about carbon. -/
theorem valence_palindrome : [1, 2, 3, 4, 3, 2, 1].reverse = [1, 2, 3, 4, 3, 2, 1] := by decide

end RussellRebuild
