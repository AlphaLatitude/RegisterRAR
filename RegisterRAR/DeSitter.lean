import RegisterRAR.Chain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Order.IntermediateValue

/-!
# The de Sitter horizon: a quarter of a largest ring away, with a largest ring's lap as its period

Two properties of the solution without a mass that Sec. II of *The Radial Acceleration Relation
from the Granularity of Hilbert Space* (v0-13) uses, derived from it.  Both are copied
unchanged from RegisterGravity v11.2 (`DeSitter.lean`), with the surface gravity `a_Λ` defined
here.

* `proper_distance`: with the horizon at `R_Λ` (`Chain.radius_from_geodesics`), the proper distance
  from the observer along a radial line, the function `s` with `s(0) = 0` and `ds/dr = 1/√f`,
  reaches the horizon at `s(R_Λ) = πR_Λ/2 = Lℓ_c/4`, a quarter of a largest ring.  This is the
  distance `L/4` of the horizon in `Distances.horizon_weight_ring`.
* `horizon_period`, `horizon_temperature`: the field of the solution at the horizon is
  `−c²/R_Λ`, so the horizon's surface gravity is `a_Λ = c²/R_Λ`; its thermal period `2πc/a_Λ` is a
  largest ring's lap `Lt_c`; and with `I1` its temperature is the Gibbons–Hawking one,
  `k_BT_dS = ℏc/2πR_Λ = ℏc/Lℓ_c`.
-/

open Real Set

namespace Register
namespace Reg

variable (R : Reg)

/-- the surface gravity of the cosmological horizon, `a_Λ = c²/R_Λ`; `horizon_period` derives it
from the solution -/
noncomputable def aΛ : ℝ := R.c ^ 2 / R.RL

/-- Without a mass, and with the boundary condition, the solution is `f(r) = 1 − r²/R_Λ²`. -/
lemma fdS_eq (G Λ r : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.fSdS G 0 Λ r = 1 - r ^ 2 / R.RL ^ 2 := by
  have hRL := R.RL_pos.ne'
  rw [(R.deSitter G Λ).1 hdS]
  unfold fSdS
  simp only [mul_zero, zero_div, sub_zero]
  field_simp

/-- the proper distance from the observer in de Sitter space, `s(r) = R_Λ arcsin(r/R_Λ)` -/
noncomputable def sdS (r : ℝ) : ℝ := R.RL * Real.arcsin (r / R.RL)

lemma continuous_sdS : Continuous R.sdS :=
  continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const _))

lemma hasDerivAt_sdS (r : ℝ) (hr0 : 0 < r) (hr : r < R.RL) :
    HasDerivAt R.sdS (1 / Real.sqrt (1 - r ^ 2 / R.RL ^ 2)) r := by
  have hRL := R.RL_pos
  have h1 : r / R.RL ≠ -1 := by
    intro h
    have : 0 < r / R.RL := div_pos hr0 hRL
    linarith
  have h2 : r / R.RL ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq hRL.ne'] at h
    linarith
  have hd := ((Real.hasDerivAt_arcsin h1 h2).comp r ((hasDerivAt_id r).div_const R.RL)).const_mul
    R.RL
  have e : R.sdS = fun y => R.RL * (Real.arcsin ∘ fun x => id x / R.RL) y := by
    funext y; rfl
  rw [e]
  convert hd using 1
  rw [div_pow]
  field_simp

/-- **The proper distance exists**: `s(r) = R_Λ arcsin(r/R_Λ)` starts at `0`, is continuous up to
the horizon, and has `ds/dr = 1/√f` inside it. -/
theorem proper_distance_exists (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.sdS 0 = 0 ∧ ContinuousOn R.sdS (Icc 0 R.RL) ∧
    ∀ r ∈ Ioo 0 R.RL, HasDerivAt R.sdS (1 / Real.sqrt (R.fSdS G 0 Λ r)) r := by
  refine ⟨by simp [sdS], R.continuous_sdS.continuousOn, ?_⟩
  intro r hr
  rw [R.fdS_eq G Λ r hdS]
  exact R.hasDerivAt_sdS r hr.1 hr.2

/-- **The horizon is a quarter of a largest ring away** (Sec. II).  In de Sitter space the proper distance from
the observer along a radial line, any `s` with `s(0) = 0`, continuous up to the horizon, and
`ds/dr = 1/√f` inside it, reaches the horizon at `s(R_Λ) = πR_Λ/2`; with the register's `π` the
real one, that is `Lℓ_c/4`, a quarter of a largest ring (`quarter_lap`). -/
theorem proper_distance (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) (s : ℝ → ℝ) (hs0 : s 0 = 0)
    (hcont : ContinuousOn s (Icc 0 R.RL))
    (hds : ∀ r ∈ Ioo 0 R.RL, HasDerivAt s (1 / Real.sqrt (R.fSdS G 0 Λ r)) r) :
    s R.RL = Real.pi * R.RL / 2 ∧ (R.pi = Real.pi → s R.RL = R.L * R.ℓc / 4) := by
  have hRL := R.RL_pos
  obtain ⟨h0, hc0, hd0⟩ := R.proper_distance_exists G Λ hdS
  -- `s − s₀` has derivative `0` inside, so it does not change from `0` to `R_Λ`
  have hg : ∀ r ∈ Ioo 0 R.RL, HasDerivAt (fun y => s y - R.sdS y) 0 r := by
    intro r hr
    have := (hds r hr).fun_sub (hd0 r hr)
    rwa [sub_self] at this
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (fun y => s y - R.sdS y) (fun _ => (0 : ℝ))
    hRL (hcont.sub hc0) hg
  have hsame : s R.RL - R.sdS R.RL = s 0 - R.sdS 0 := by
    have h := hξ.symm
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · exact absurd h (by linarith)
  have hval : s R.RL = Real.pi * R.RL / 2 := by
    rw [hs0, h0] at hsame
    have : R.sdS R.RL = Real.pi * R.RL / 2 := by
      unfold sdS
      rw [div_self hRL.ne', Real.arcsin_one]
      ring
    linarith
  refine ⟨hval, fun hpi => ?_⟩
  rw [hval, ← hpi]
  exact R.quarter_lap

/-- **The period of the horizon is the lap of the largest ring** (Sec. II).  With `hdS`, the field of the solution without a mass at the horizon is
`g(R_Λ) = −c²/R_Λ`, so the horizon's surface gravity is `a_Λ = c²/R_Λ`, here derived.  The ring
of an observer held at that acceleration, `L_a` of `Chain.lean`, whose lap time is the thermal
period `2πc/a` of his horizon, is the largest ring, `L_{a_Λ} = L`; so the period of the horizon,
`2πc/a_Λ = 2πR_Λ/c`, is the lap time `Lt_c` of the largest ring. -/
theorem horizon_period (G Λ : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0) :
    R.gSdS G 0 Λ R.RL = -R.aΛ ∧ R.La R.aΛ = R.L ∧
    R.La R.aΛ * R.tc = 2 * R.pi * R.c / R.aΛ ∧ 2 * R.pi * R.c / R.aΛ = R.L * R.tc := by
  reg_facts R
  have hRL := R.RL_pos
  have haΛ : 0 < R.aΛ := by unfold aΛ; positivity
  refine ⟨?_, ?_, R.La_lap _ haΛ, ?_⟩
  · rw [R.gSdS_eq G 0 Λ R.RL hRL.ne', (R.deSitter G Λ).1 hdS]
    unfold aΛ
    field_simp
    ring
  · unfold La aΛ RL
    field_simp
  · rw [R.lap_time]
    unfold aΛ
    field_simp

/-- **Eq. (2) from the solution**: with `I1` for the ring of an observer held at
the horizon's surface gravity, which is the largest ring (`horizon_period`), the temperature of
the horizon is Unruh's at `a_Λ`, `ℏa_Λ/2πc`, and it is `E_c/L = ℏc/2πR_Λ`, the Gibbons–Hawking
temperature: `ℏ` over the lap time of the largest ring. -/
theorem horizon_temperature (G Λ T : ℝ) (hdS : R.fSdS G 0 Λ R.RL = 0)
    (I1 : R.kB * T = R.ℏ / (R.La R.aΛ * R.tc)) :
    R.kB * T = R.ℏ * R.aΛ / (2 * R.pi * R.c) ∧ R.kB * T = R.Ec / R.L ∧
    R.kB * T = R.ℏ * R.c / (2 * R.pi * R.RL) := by
  reg_facts R
  have hRL := R.RL_pos
  have haΛ : 0 < R.aΛ := by unfold aΛ; positivity
  have hL := (R.horizon_period G Λ hdS).2.1
  refine ⟨R.T_Unruh _ T haΛ I1, ?_⟩
  rw [hL] at I1
  exact R.T_dS T I1

end Reg
end Register
