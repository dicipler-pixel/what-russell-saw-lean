/-
What Russell Saw — the orbit claims as calculus, not just the algebra around them.

* Binet's equation `u'' + u = C u^(p-2)` (force `∝ r^(-p)`): the derivative of its right-hand
  side at a circular orbit is `p - 2`, so small departures obey `δ'' + (3 - p) δ = 0`.
* The apsidal angle: for `κ > 0` the departure `A cos(√κ θ)` solves `δ'' = -κ δ`, falls
  strictly from `A` to `-A` on `[0, π/√κ]` and is flat at both ends, so near point and far
  point are `π/√κ` apart. Newton's `p = 2` gives `π` (a closed ellipse); as `p → 3` from
  below the angle grows without bound, so in the linearised orbit the far point takes ever
  longer to return as the force approaches Russell's inverse cube.
* General relativity: `u'' + u = M/L² + 3Mu²` has right-hand slope `6Mu`, so the restoring
  coefficient `1 - 6Mu₀` vanishes exactly at `r = 6M`.
* The Schwarzschild effective potential `V = -M/r + L²/(2r²) - ML²/r³`: its first and second
  derivatives both vanish exactly when `r = 6M` and `L² = 12M²` — the marginally stable
  circular orbit (the innermost stable circular orbit), derived from the potential itself.

Units `G = c = 1`. Jeromie Beasley, 2026.
-/
import Mathlib

namespace RussellOrbits

open Real Filter Topology Set

/-! ## Binet's equation -/

/-- The right-hand side of Binet's equation has derivative `C (p-2) u^(p-3)`. -/
theorem binet_rhs_hasDerivAt (C p u0 : ℝ) (hu : 0 < u0) :
    HasDerivAt (fun u => C * u ^ (p - 2)) (C * ((p - 2) * u0 ^ (p - 2 - 1))) u0 :=
  (Real.hasDerivAt_rpow_const (Or.inl hu.ne')).const_mul C

/-- **Restoring coefficient.** At a circular orbit `u₀ = C u₀^(p-2)` the linearised Binet
equation `δ'' + (1 - f'(u₀)) δ = 0` has coefficient exactly `3 - p`. -/
theorem binet_restoring_coefficient (C p u0 : ℝ) (hu : 0 < u0)
    (hc : C * u0 ^ (p - 2) = u0) :
    1 - C * ((p - 2) * u0 ^ (p - 2 - 1)) = 3 - p := by
  have h1 : u0 ^ (p - 2 - 1) = u0 ^ (p - 2) / u0 := Real.rpow_sub_one hu.ne' _
  rw [h1]
  have hu' : u0 ≠ 0 := hu.ne'
  have key : C * ((p - 2) * (u0 ^ (p - 2) / u0)) = (p - 2) * (C * u0 ^ (p - 2)) / u0 := by
    ring
  rw [key, hc, mul_div_assoc, div_self hu', mul_one]
  ring

/-! ## The apsidal angle -/

/-- The departure from the circle. -/
noncomputable def departure (A k θ : ℝ) : ℝ := A * cos (k * θ)

/-- Its rate of change. -/
noncomputable def departureRate (A k θ : ℝ) : ℝ := -(A * k) * sin (k * θ)

theorem departure_hasDerivAt (A k θ : ℝ) :
    HasDerivAt (departure A k) (departureRate A k θ) θ := by
  have h := (((hasDerivAt_id' θ).const_mul k).cos).const_mul A
  unfold departure departureRate
  exact h.congr_deriv (by ring)

theorem departureRate_hasDerivAt (A k θ : ℝ) :
    HasDerivAt (departureRate A k) (-(k ^ 2) * departure A k θ) θ := by
  have h := (((hasDerivAt_id' θ).const_mul k).sin).const_mul (-(A * k))
  unfold departure departureRate
  exact h.congr_deriv (by ring)

/-- **The linearised orbit equation is solved**: with `k = √κ`, `δ'' = -κ δ`. -/
theorem departure_solves (A κ θ : ℝ) (hκ : 0 ≤ κ) :
    HasDerivAt (departureRate A (Real.sqrt κ)) (-κ * departure A (Real.sqrt κ) θ) θ := by
  have h := departureRate_hasDerivAt A (Real.sqrt κ) θ
  rwa [Real.sq_sqrt hκ] at h

/-- **Apsidal angle.** On `[0, π/k]` the departure falls strictly from `A` to `-A`, with zero
rate at both ends: near point to far point takes exactly the angle `π/k`. -/
theorem apsidal_angle (A k : ℝ) (hA : 0 < A) (hk : 0 < k) :
    departure A k 0 = A ∧ departure A k (π / k) = -A ∧
    departureRate A k 0 = 0 ∧ departureRate A k (π / k) = 0 ∧
    StrictAntiOn (departure A k) (Icc 0 (π / k)) := by
  have hkπ : k * (π / k) = π := by field_simp
  refine ⟨by simp [departure], by simp [departure, hkπ], by simp [departureRate],
    by simp [departureRate, hkπ], ?_⟩
  intro a ha b hb hab
  have mem : ∀ x ∈ Icc (0 : ℝ) (π / k), k * x ∈ Icc (0 : ℝ) π := by
    intro x hx
    refine ⟨mul_nonneg hk.le hx.1, ?_⟩
    calc k * x ≤ k * (π / k) := mul_le_mul_of_nonneg_left hx.2 hk.le
      _ = π := hkπ
  have hc := Real.strictAntiOn_cos (mem a ha) (mem b hb) (mul_lt_mul_of_pos_left hab hk)
  unfold departure
  exact mul_lt_mul_of_pos_left hc hA

/-- Newton's inverse square (`p = 2`, `κ = 1`): the apsidal angle is `π`, half a turn, so the
orbit closes. -/
theorem newton_apsidal_angle : π / Real.sqrt (3 - 2) = π := by norm_num

/-- As the force steepens toward Russell's inverse cube (`p → 3⁻`), the apsidal angle
`π/√(3 - p)` grows without bound: in the linearised orbit the far point takes ever longer to
return. -/
theorem apsidal_angle_diverges :
    Tendsto (fun p : ℝ => π / Real.sqrt (3 - p)) (𝓝[<] 3) atTop := by
  have h0 : Tendsto (fun p : ℝ => Real.sqrt (3 - p)) (𝓝[<] 3) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun p : ℝ => Real.sqrt (3 - p)) :=
        (continuous_const.sub continuous_id).sqrt
      have := hc.tendsto 3
      simp only [sub_self, Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact Real.sqrt_pos.mpr (sub_pos.mpr hp)
  have h1 := (tendsto_inv_nhdsGT_zero.comp h0).const_mul_atTop Real.pi_pos
  refine h1.congr (fun p => ?_)
  simp [div_eq_mul_inv]

/-! ## General relativity -/

/-- The relativistic Binet right-hand side `M/L² + 3Mu²` has slope `6Mu`. -/
theorem gr_rhs_hasDerivAt (M L u0 : ℝ) :
    HasDerivAt (fun u => M / L ^ 2 + 3 * M * u ^ 2) (6 * M * u0) u0 := by
  have h := ((hasDerivAt_pow 2 u0).const_mul (3 * M)).const_add (M / L ^ 2)
  exact h.congr_deriv (by norm_num <;> ring)

/-- The relativistic restoring coefficient `1 - 6Mu₀` vanishes exactly at `r = 6M`. -/
theorem gr_restoring_zero_iff (M r : ℝ) (hM : 0 < M) (hr : 0 < r) :
    1 - 6 * M * (1 / r) = 0 ↔ r = 6 * M := by
  constructor
  · intro h
    have hr0 : r ≠ 0 := hr.ne'
    field_simp at h
    linarith
  · intro h
    have h6 : 6 * M ≠ 0 := by positivity
    rw [h, one_div, mul_inv_cancel₀ h6, sub_self]

/-! ## The Schwarzschild effective potential and the ISCO -/

/-- `V(r) = -M/r + L²/(2r²) - ML²/r³`, written in powers of `1/r`. -/
noncomputable def effPot (M L r : ℝ) : ℝ :=
  -M * r⁻¹ + L ^ 2 / 2 * r⁻¹ ^ 2 - M * L ^ 2 * r⁻¹ ^ 3

/-- `V'(r) = M/r² - L²/r³ + 3ML²/r⁴`. -/
noncomputable def effPot' (M L r : ℝ) : ℝ :=
  M * r⁻¹ ^ 2 - L ^ 2 * r⁻¹ ^ 3 + 3 * M * L ^ 2 * r⁻¹ ^ 4

/-- `V''(r) = -2M/r³ + 3L²/r⁴ - 12ML²/r⁵`. -/
noncomputable def effPot'' (M L r : ℝ) : ℝ :=
  -2 * M * r⁻¹ ^ 3 + 3 * L ^ 2 * r⁻¹ ^ 4 - 12 * M * L ^ 2 * r⁻¹ ^ 5

theorem effPot_hasDerivAt (M L r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (effPot M L) (effPot' M L r) r := by
  have hw := hasDerivAt_inv hr
  have h := ((hw.const_mul (-M)).add ((hw.pow 2).const_mul (L ^ 2 / 2))).sub
    ((hw.pow 3).const_mul (M * L ^ 2))
  unfold effPot effPot'
  exact h.congr_deriv (by norm_num [inv_pow] <;> field_simp <;> ring)

theorem effPot'_hasDerivAt (M L r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (effPot' M L) (effPot'' M L r) r := by
  have hw := hasDerivAt_inv hr
  have h := (((hw.pow 2).const_mul M).sub ((hw.pow 3).const_mul (L ^ 2))).add
    ((hw.pow 4).const_mul (3 * M * L ^ 2))
  unfold effPot' effPot''
  exact h.congr_deriv (by norm_num [inv_pow] <;> field_simp <;> ring)

theorem effPot'_mul (M L r : ℝ) (hr : r ≠ 0) :
    effPot' M L r * r ^ 4 = M * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2 := by
  unfold effPot'
  field_simp <;> ring

theorem effPot''_mul (M L r : ℝ) (hr : r ≠ 0) :
    effPot'' M L r * r ^ 5 = -2 * M * r ^ 2 + 3 * L ^ 2 * r - 12 * M * L ^ 2 := by
  unfold effPot''
  field_simp <;> ring

/-- **The innermost stable circular orbit from the potential.** A circular orbit
(`V' = 0`) is marginally stable (`V'' = 0`) exactly when `r = 6M` and `L² = 12M²`. -/
theorem isco_from_potential (M L r : ℝ) (hM : 0 < M) (hr : 0 < r) :
    effPot' M L r = 0 ∧ effPot'' M L r = 0 ↔ r = 6 * M ∧ L ^ 2 = 12 * M ^ 2 := by
  have hr0 : r ≠ 0 := hr.ne'
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : M * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2 = 0 := by
      rw [← effPot'_mul M L r hr0, h1, zero_mul]
    have e2 : -2 * M * r ^ 2 + 3 * L ^ 2 * r - 12 * M * L ^ 2 = 0 := by
      rw [← effPot''_mul M L r hr0, h2, zero_mul]
    have hL : L ^ 2 ≠ 0 := by
      intro hL
      rw [hL] at e1
      have : M * r ^ 2 = 0 := by linear_combination e1
      have : 0 < M * r ^ 2 := by positivity
      linarith
    have e3 : L ^ 2 * (r - 6 * M) = 0 := by linear_combination e2 + 2 * e1
    have hr6 : r = 6 * M := by
      have := (mul_eq_zero.mp e3).resolve_left hL
      linarith
    refine ⟨hr6, ?_⟩
    rw [hr6] at e1
    have : M * (3 * L ^ 2 - 36 * M ^ 2) = 0 := by linear_combination (-1 : ℝ) * e1
    have := (mul_eq_zero.mp this).resolve_left hM.ne'
    linarith
  · rintro ⟨hr6, hL⟩
    have e1 : effPot' M L r * r ^ 4 = 0 := by
      rw [effPot'_mul M L r hr0, hr6, hL]
      ring
    have e2 : effPot'' M L r * r ^ 5 = 0 := by
      rw [effPot''_mul M L r hr0, hr6, hL]
      ring
    exact ⟨(mul_eq_zero.mp e1).resolve_right (pow_ne_zero _ hr0),
      (mul_eq_zero.mp e2).resolve_right (pow_ne_zero _ hr0)⟩

end RussellOrbits
