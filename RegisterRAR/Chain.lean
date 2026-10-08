import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Sec. II of the paper: the inputs, derived from the two postulates and thermodynamics

Formal counterpart of Sec. II, "The inputs", of *The Radial Acceleration Relation from the
Granularity of Hilbert Space* (v0-13).  Every relation that the section derives is a theorem here, with the
physical inputs stated as **named hypotheses** of the theorems that use them, so that a theorem's
statement is its own ledger.  No physical axiom is declared; `Ledger.lean` prints the axioms of
every main theorem, which are the logical minimum of classical mathematics.

Many declarations below come from RegisterGravity v11.2 (`Chain.lean`), where they compiled at the
same Lean and Mathlib versions; their proofs are unchanged, and their docstrings refer to this paper.
The paper's own additions are at the end.

## The inputs, as they appear below

* `I1`, thermodynamics (the Kubo–Martin–Schwinger condition): a horizon whose thermal period is
  `τ` has `k_B T = ℏ/τ`, with the period `2πc/a` of a horizon of surface gravity `a`, which in cells
  is the lap time of the ring `L_a` (`La_lap`).  It gives Unruh's temperature (`T_Unruh`) and, for
  the cosmological horizon, whose period is a largest ring's lap (`DeSitter.horizon_period`), the
  Gibbons–Hawking temperature (`T_dS`).
* `hJ`, thermodynamics (Jacobson): the heat that crosses a local horizon obeys the Clausius
  relation, and with the Raychaudhuri equation this gives Einstein's equations, whose coefficient
  is `8πG/c⁴` exactly when `G = c³k_B/4ℏη` (`einstein_coefficient`), with `η` the entropy per unit
  area, the same on every horizon.  The count fixes `η` (`eta_eq`).
* `hK`, the Komar energy of a static solution: `Mc² = 2T_aS` [Komar 1959; Padmanabhan 2010], a
  classical result of the equations that `hJ` derives.
* `hGeo`, the closed geodesics: without a mass and with the symmetry of space the solution is
  maximally symmetric, and of the maximally symmetric vacua only de Sitter space has closed
  spacelike geodesics, circles of radius `√(3/Λ)` [Hawking–Ellis 1973]; the largest rings are these
  circles, `Lℓ_c = 2π√(3/Λ)`.  The symmetry of space is the one premise from outside the
  postulates and thermodynamics, as in the gravitation paper.

The solution of Einstein's equations is the classical Schwarzschild–de Sitter solution `fSdS`
[Kottler 1918], taken as already proven, as in RegisterGravity; with no mass it is de Sitter space.
-/

open Real

namespace Register

/-- The register's constants: the speed of light, `ℏ`, `k_B`, the cell, the length `L` of the
largest ring (as a real number), `π`, and `ln 2` (positive reals whose values are never used here;
`ln 2 < 1` makes the matter part `1 − ln 2` of a string's energy positive). -/
structure Reg where
  c : ℝ
  ℏ : ℝ
  kB : ℝ
  ℓc : ℝ
  L : ℝ
  pi : ℝ
  ln2 : ℝ
  c_pos : 0 < c
  ℏ_pos : 0 < ℏ
  kB_pos : 0 < kB
  ℓc_pos : 0 < ℓc
  L_pos : 0 < L
  pi_pos : 0 < pi
  ln2_pos : 0 < ln2
  ln2_lt_one : ln2 < 1

namespace Reg

variable (R : Reg)

/-- Introduce the positivity and non-vanishing facts of the register's constants into the
local context, where `positivity` and `field_simp` find them. -/
macro "reg_facts " R:term : tactic => `(tactic| (
  have := ($R).c_pos; have := ($R).ℏ_pos; have := ($R).kB_pos
  have := ($R).ℓc_pos; have := ($R).L_pos; have := ($R).pi_pos; have := ($R).ln2_pos
  have := ($R).c_pos.ne'; have := ($R).ℏ_pos.ne'; have := ($R).kB_pos.ne'
  have := ($R).ℓc_pos.ne'; have := ($R).L_pos.ne'; have := ($R).pi_pos.ne'
  have := ($R).ln2_pos.ne'))

/-- **One bit** (Sec. II, the entropy): a doublet whose two senses are weighted equally holds the
entropy `ln 2`, and no doublet holds more: the binary entropy `−p ln p − (1 − p) ln(1 − p)` is
`ln 2` at `p = 1/2` and at most `ln 2` for every `p` (Mathlib's `Real.binEntropy`). -/
theorem one_bit : Real.binEntropy (1 / 2) = Real.log 2 ∧ ∀ p, Real.binEntropy p ≤ Real.log 2 :=
  ⟨by rw [one_div]; exact Real.binEntropy_two_inv, fun _ => Real.binEntropy_le_log_two⟩

/-! ### Units of the cell and the sphere of the largest rings (Sec. II) -/

/-- the tick, `t_c = ℓ_c/c` -/
noncomputable def tc : ℝ := R.ℓc / R.c
/-- the energy of the cell, `E_c = ℏc/ℓ_c` -/
noncomputable def Ec : ℝ := R.ℏ * R.c / R.ℓc
/-- **The radius of the largest ring** (Sec. II): `R_Λ = Lℓ_c/2π`, the radius of a circle of length
`Lℓ_c`; `radius_from_geodesics` shows that it is the radius of the cosmological horizon. -/
noncomputable def RL : ℝ := R.L * R.ℓc / (2 * R.pi)
/-- the area of the cosmological horizon, `4πR_Λ²` -/
noncomputable def Ahor : ℝ := 4 * R.pi * R.RL ^ 2
/-- the largest rings the horizon counts, `L²/4` to leading order in `1/L`: `Horizon.counts` gives
`L²/4 − L/2 + 1`, and `Positions.horizon_weight_ring` shows that the horizon counts every one -/
noncomputable def Rhor : ℝ := R.L ^ 2 / 4
/-- **The horizon's entropy** (Sec. II), in units of `k_B`: one bit, `ln 2`, for each largest ring.
Every ring carries exactly one string, since a cell holds one bit of each ring through it, and a
string's two senses weighted equally hold one bit (`one_bit`). -/
noncomputable def Shor : ℝ := R.Rhor * R.ln2
/-- the entropy per unit area of the horizon, `η = k_B R ln 2/A_hor` -/
noncomputable def η : ℝ := R.kB * R.Shor / R.Ahor

lemma RL_pos : 0 < R.RL := by reg_facts R; unfold RL; positivity
lemma Ahor_pos : 0 < R.Ahor := by unfold Ahor; have := R.RL_pos; reg_facts R; positivity

/-- The count uses only the area of the sphere of the largest rings, `4πR_Λ² = L²ℓ_c²/π` (Sec. II). -/
theorem area_in_cells : R.Ahor = R.L ^ 2 * R.ℓc ^ 2 / R.pi := by
  reg_facts R
  unfold Ahor RL
  field_simp
  ring

/-- the lap time of a largest ring, `Lt_c = 2πR_Λ/c` -/
theorem lap_time : R.L * R.tc = 2 * R.pi * R.RL / R.c := by
  reg_facts R
  unfold tc RL
  field_simp

/-- **A quarter of a largest ring** (Sec. II): the horizon's proper distance `πR_Λ/2`
(`proper_distance`) is `Lℓ_c/4`. -/
theorem quarter_lap : R.pi * R.RL / 2 = R.L * R.ℓc / 4 := by
  reg_facts R
  unfold RL
  field_simp
  ring

/-! ### The strings a sphere holds -/

/-- the strings a sphere of radius `r` holds: its entropy over `k_B ln 2`, one bit per string.
The entropy of a horizon is proportional to its area, `S = ηA`, which is part of the thermodynamic
input of Jacobson, and the entropy per unit area `η` is the horizon's, fixed by the count
(`eta_eq`). -/
noncomputable def Ns (r : ℝ) : ℝ := R.η * (4 * R.pi * r ^ 2) / (R.kB * R.ln2)
/-! ### The temperature of a horizon (Sec. II, thermodynamics `I1`) -/

/-- **I1 applied to the largest ring**, Eq. (2): `k_B T_dS = E_c/L = ℏc/Lℓ_c = ℏc/2πR_Λ`. -/
theorem T_dS (T : ℝ) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    R.kB * T = R.Ec / R.L ∧ R.kB * T = R.ℏ * R.c / (2 * R.pi * R.RL) := by
  reg_facts R
  rw [I1]
  unfold tc Ec RL
  constructor <;> (field_simp)

/-- the ring of a held observer: the ring whose lap time is the thermal period `2πc/a` of
the Rindler horizon `c²/a` behind him (the period is the geometry of that horizon) -/
noncomputable def La (a : ℝ) : ℝ := 2 * R.pi * R.c ^ 2 / (a * R.ℓc)

theorem La_lap (a : ℝ) (ha : 0 < a) : R.La a * R.tc = 2 * R.pi * R.c / a := by
  reg_facts R
  unfold La tc
  field_simp

/-- **I1 applied to the ring `L_a`**: Unruh's temperature, `k_B T_a = ℏa/2πc`. -/
theorem T_Unruh (a T : ℝ) (ha : 0 < a) (I1 : R.kB * T = R.ℏ / (R.La a * R.tc)) :
    R.kB * T = R.ℏ * a / (2 * R.pi * R.c) := by
  reg_facts R
  rw [I1, R.La_lap a ha]
  field_simp

/-! ### Einstein's equations from the count (Sec. II, Jacobson `hJ`) -/

/-- **The entropy per unit area** (Sec. II): `η = πk_B ln 2/4ℓ_c²`. -/
theorem eta_eq : R.η = R.pi * R.kB * R.ln2 / (4 * R.ℓc ^ 2) := by
  reg_facts R
  unfold η Shor Rhor Ahor RL
  field_simp; ring

/-- **Newton's constant from Einstein's equations** (Sec. II, Jacobson's argument): the coefficient
`2πk_B/(ℏcη)` that the Clausius relation gives Einstein's equations equals `8πG/c⁴` exactly when
`G = c³k_B/4ℏη`, which is the hypothesis `hJ`. -/
theorem einstein_coefficient (G η' : ℝ) (hη : 0 < η') :
    2 * R.pi * R.kB / (R.ℏ * R.c * η') = 8 * R.pi * G / R.c ^ 4 ↔
      G = R.c ^ 3 * R.kB / (4 * R.ℏ * η') := by
  reg_facts R
  have hη' := hη.ne'
  constructor
  · intro h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    rw [eq_div_iff (by positivity)]
    have h2 : (2 * R.pi * R.c) * (R.c ^ 3 * R.kB - G * (4 * R.ℏ * η')) = 0 := by
      linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso
      have : 0 < 2 * R.pi * R.c := by positivity
      linarith
    · linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Jacobson (`hJ`) with the register's entropy density** (Sec. II):
`G = c³ℓ_c²/(πℏ ln 2) = 4πc³R_Λ²/(ℏL² ln 2)`. -/
theorem G_eq (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    G = R.c ^ 3 * R.ℓc ^ 2 / (R.pi * R.ℏ * R.ln2) ∧
    G = 4 * R.pi * R.c ^ 3 * R.RL ^ 2 / (R.ℏ * R.L ^ 2 * R.ln2) := by
  reg_facts R
  rw [hJ, R.eta_eq]
  unfold RL
  constructor <;> (field_simp <;> ring)

/-- The Planck length, defined from `G`. -/
noncomputable def ℓP (G : ℝ) : ℝ := Real.sqrt (R.ℏ * G / R.c ^ 3)

/-- **The cell from Newton's constant** (Sec. II): `ℓ_c = √(π ln 2 ℏG/c³) = √(π ln 2) ℓ_P`. -/
theorem cell_from_G (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.ℓc = Real.sqrt (R.pi * R.ln2 * R.ℏ * G / R.c ^ 3) ∧
    R.ℓc = Real.sqrt (R.pi * R.ln2) * R.ℓP G := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hsq : R.pi * R.ln2 * R.ℏ * G / R.c ^ 3 = R.ℓc ^ 2 := by
    rw [hG]; field_simp
  constructor
  · rw [hsq, Real.sqrt_sq R.ℓc_pos.le]
  · unfold ℓP
    rw [← Real.sqrt_mul (by positivity)]
    have h2 : R.pi * R.ln2 * (R.ℏ * G / R.c ^ 3) = R.ℓc ^ 2 := by rw [← hsq]; ring
    rw [h2, Real.sqrt_sq R.ℓc_pos.le]

/-- **The quarter, with the cell fixed by the measured `G`** (Sec. II): the horizon's entropy is
`(L²/4) ln 2 = π²R_Λ² ln 2/ℓ_c² = πR_Λ²/ℓ_P² = A_hor/4ℓ_P²`, Bekenstein and Hawking's quarter per
Planck area. -/
theorem entropy_quarter (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η)) :
    R.Shor = R.pi ^ 2 * R.RL ^ 2 * R.ln2 / R.ℓc ^ 2 ∧
    R.Shor = R.pi * R.RL ^ 2 / R.ℓP G ^ 2 ∧
    R.Shor = R.Ahor / (4 * R.ℓP G ^ 2) := by
  reg_facts R
  have hℓP : R.ℓP G ^ 2 = R.ℓc ^ 2 / (R.pi * R.ln2) := by
    have h := (R.cell_from_G G hJ).2
    have hs : Real.sqrt (R.pi * R.ln2) ^ 2 = R.pi * R.ln2 := Real.sq_sqrt (by positivity)
    have : R.ℓc ^ 2 = R.pi * R.ln2 * R.ℓP G ^ 2 := by rw [h, mul_pow, hs]
    rw [this]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold Shor Rhor RL; field_simp; ring
  · rw [hℓP]; unfold Shor Rhor RL; field_simp; ring
  · rw [hℓP]; unfold Shor Rhor Ahor RL; field_simp; ring

/-! ### The solution of Einstein's equations -/

/-- **Schwarzschild–de Sitter**, the static solution of Einstein's equation about a mass `M`, with
`Λ` its integration constant: `ds² = −f c²dt² + dr²/f + r²dΩ²` with `f(r) = 1 − 2GM/c²r − Λr²/3`.
Of general relativity it is the one solution the paper uses, taken as already proven
[Kottler 1918]; what the paper takes from general relativity is derived from it below. -/
noncomputable def fSdS (G M Λ r : ℝ) : ℝ := 1 - 2 * G * M / (R.c ^ 2 * r) - Λ * r ^ 2 / 3

/-- the field of the solution, the acceleration toward the mass: `g = (c²/2) df/dr`, the gradient
of the potential `Φ = c²(f − 1)/2` that the time part of the metric carries (the classical
weak-field reading) -/
noncomputable def gSdS (G M Λ r : ℝ) : ℝ := R.c ^ 2 / 2 * deriv (R.fSdS G M Λ) r

theorem hasDerivAt_fSdS (G M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (R.fSdS G M Λ) (2 * G * M / (R.c ^ 2 * r ^ 2) - 2 * Λ * r / 3) r := by
  reg_facts R
  have e : R.fSdS G M Λ = fun s => 1 - 2 * G * M / R.c ^ 2 * s⁻¹ - Λ / 3 * s ^ 2 := by
    funext s; unfold fSdS; ring
  rw [e]
  have h := ((hasDerivAt_const r (1 : ℝ)).fun_sub
    ((hasDerivAt_inv hr).const_mul (2 * G * M / R.c ^ 2))).fun_sub
    ((hasDerivAt_pow 2 r).const_mul (Λ / 3))
  convert h using 1
  norm_num
  field_simp

/-- **The field of the solution**: `g = GM/r² − Λc²r/3`, the pull of the mass less the push of the
vacuum. -/
theorem gSdS_eq (G M Λ r : ℝ) (hr : r ≠ 0) :
    R.gSdS G M Λ r = G * M / r ^ 2 - Λ * R.c ^ 2 * r / 3 := by
  reg_facts R
  unfold gSdS
  rw [(R.hasDerivAt_fSdS G M Λ r hr).deriv]
  field_simp

/-- The field of the mass alone (`Λ = 0`) is Newton's, `g = GM/r²`. -/
theorem gSdS_mass (G M r : ℝ) (hr : r ≠ 0) : R.gSdS G M 0 r = G * M / r ^ 2 := by
  rw [R.gSdS_eq G M 0 r hr]; ring

/-- **The de Sitter horizon.**  Without a mass the solution has its horizon where `f = 0`, and the
register's horizon at `R_Λ` is that horizon exactly when `Λ = 3/R_Λ²`.  In Einstein's equation `Λ`
is an integration constant; this boundary condition fixes it (Sec. II). -/
theorem deSitter (G Λ : ℝ) : R.fSdS G 0 Λ R.RL = 0 ↔ Λ = 3 / R.RL ^ 2 := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  unfold fSdS
  constructor
  · intro h
    simp only [mul_zero, zero_div, sub_zero] at h
    rw [eq_div_iff (by positivity)]
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-! ### The paper's additions (Sec. II) -/

/-- **The strings of a sphere**: `N_s = π²r²/ℓ_c²`, one for each `4ℓ_c²/π` of its area. -/
theorem Ns_eq (r : ℝ) : R.Ns r = R.pi ^ 2 * r ^ 2 / R.ℓc ^ 2 := by
  reg_facts R
  unfold Ns η Shor Rhor Ahor RL
  field_simp
  ring

/-- **The horizon's radius from the closed geodesics** (Sec. II).  The largest rings are the closed
geodesics of the solution without a mass, circles of radius `√(3/Λ)` (hypothesis `hGeo`, see the
module comment).  Then `R_Λ = Lℓ_c/2π = √(3/Λ)`, `Λ = 3/R_Λ²`, and that solution has its horizon at
`R_Λ`. -/
theorem radius_from_geodesics (G Λ : ℝ) (hΛ : 0 < Λ)
    (hGeo : R.L * R.ℓc = 2 * R.pi * Real.sqrt (3 / Λ)) :
    R.RL = Real.sqrt (3 / Λ) ∧ Λ = 3 / R.RL ^ 2 ∧ R.fSdS G 0 Λ R.RL = 0 := by
  reg_facts R
  have h1 : R.RL = Real.sqrt (3 / Λ) := by
    unfold RL
    rw [hGeo, div_eq_iff (by positivity : (2 : ℝ) * R.pi ≠ 0)]
    ring
  have h3 : (0 : ℝ) ≤ 3 / Λ := by positivity
  have h2 : Λ = 3 / R.RL ^ 2 := by
    rw [h1, Real.sq_sqrt h3]
    field_simp
  exact ⟨h1, h2, (R.deSitter G Λ).2 h2⟩

/-- **Newton's law from the Komar energy** (Sec. II).  A sphere of radius `r` on which the
acceleration toward the body is `a` has, by `I1`, the Unruh temperature; its entropy is `ηA`, one
bit for each of its `N_s` strings, `k_B N_s ln 2`; the Komar energy inside it is `Mc² = 2T_aS`
(`hK`); and Jacobson's `G` is `hJ`.  Then `a = GM/r²`: Newton's law is an equal share of the body's
energy among the strings of the sphere, two Landauer energies each. -/
theorem newton_komar (G M r a T : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I1 : R.kB * T = R.ℏ / (R.La a * R.tc))
    (hK : M * R.c ^ 2 = 2 * T * (R.kB * R.Ns r * R.ln2)) :
    a = G * M / r ^ 2 := by
  reg_facts R
  have hr' := hr.ne'
  have hT := R.T_Unruh a T ha I1
  have hG := (R.G_eq G hJ).1
  have h1 : M * R.c ^ 2 = a * (R.ℏ * R.pi * R.ln2 * r ^ 2 / (R.c * R.ℓc ^ 2)) := by
    rw [hK, show 2 * T * (R.kB * R.Ns r * R.ln2) = 2 * (R.kB * T) * R.Ns r * R.ln2 by ring,
      hT, R.Ns_eq r]
    field_simp
  have hK0 : 0 < R.ℏ * R.pi * R.ln2 * r ^ 2 / (R.c * R.ℓc ^ 2) := by positivity
  have ha' : a = M * R.c ^ 2 / (R.ℏ * R.pi * R.ln2 * r ^ 2 / (R.c * R.ℓc ^ 2)) := by
    rw [eq_div_iff hK0.ne']
    exact h1.symm
  rw [ha', hG]
  field_simp

/-- **Eq. (3) at `g_N`**: with Jacobson's `G` and `I1` for the Unruh temperature `T_N` of
`g_N = GM/r²`, the body's energy is two Landauer energies at `T_N` for each string of the sphere,
`Mc² = 2N_s k_BT_N ln 2`. -/
theorem newton_share (G M r T : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (I1 : R.kB * T = R.ℏ / (R.La (G * M / r ^ 2) * R.tc)) :
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * T * R.ln2) := by
  reg_facts R
  have hr' := hr.ne'
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  have hT := R.T_Unruh _ T hgN I1
  rw [show 2 * R.Ns r * (R.kB * T * R.ln2) = 2 * R.Ns r * (R.kB * T) * R.ln2 by ring, hT,
    R.Ns_eq r, hG]
  field_simp

/-- **The vacuum is one Landauer heat per string of the horizon** (Sec. II).  With the horizon at
`R_Λ` (`radius_from_geodesics`), Jacobson's `G`, and the Gibbons–Hawking temperature (`I1` for the
largest ring's lap), the vacuum energy inside the horizon, `(Λc⁴/8πG)(4πR_Λ³/3) = c⁴R_Λ/2G`, equals
the temperature times the horizon's entropy, `T_dS k_B (L²/4) ln 2`, so each of the `L²/4` strings of
the horizon holds `k_BT_dS ln 2` of it. -/
theorem vacuum_per_string (G Λ T : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) :
    Λ * R.c ^ 4 / (8 * R.pi * G) * (4 / 3 * R.pi * R.RL ^ 3) = R.c ^ 4 * R.RL / (2 * G) ∧
    R.c ^ 4 * R.RL / (2 * G) = T * (R.kB * R.Shor) ∧
    R.c ^ 4 * R.RL / (2 * G) / R.Rhor = R.kB * T * R.ln2 := by
  reg_facts R
  have hRL := R.RL_pos.ne'
  have hΛ := (R.deSitter G Λ).1 hdS
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hG0' := hG0.ne'
  have hT := (R.T_dS T I1).1
  refine ⟨?_, ?_, ?_⟩
  · rw [hΛ]
    field_simp
    ring
  · rw [show T * (R.kB * R.Shor) = R.kB * T * R.Shor by ring, hT, hG]
    unfold Shor Rhor Ec RL
    field_simp
    ring
  · rw [hT, hG]
    unfold Rhor Ec RL
    field_simp
    ring

/-- **The split of a string's energy** (Sec. II).  Taking a string's energy to be one horizon
thermal energy, `ε_s = k_BT_dS` (hypothesis `hεs`; Planck's `Ω_Λ` supports it to 1%,
`Numerics.string_energy_check`), its heat, the horizon's temperature times the string's one bit of
entropy, is `ln 2` of it and equals the vacuum's share per string (`vacuum_per_string`), and the
rest, `(1 − ln 2)ε_s`, is matter. -/
theorem string_split (G Λ T εs : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hdS : R.fSdS G 0 Λ R.RL = 0) (I1 : R.kB * T = R.ℏ / (R.L * R.tc)) (hεs : εs = R.kB * T) :
    R.ln2 * εs = R.c ^ 4 * R.RL / (2 * G) / R.Rhor ∧
    εs = R.ln2 * εs + (1 - R.ln2) * εs ∧ 0 < (1 - R.ln2) * εs := by
  reg_facts R
  have hv := (R.vacuum_per_string G Λ T hJ hdS I1).2.2
  have hT := (R.T_dS T I1).2
  have hTpos : 0 < R.kB * T := by rw [hT]; have := R.RL_pos; positivity
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  refine ⟨?_, by ring, ?_⟩
  · rw [hv, hεs]; ring
  · rw [hεs]; exact mul_pos hm hTpos

end Reg

end Register
