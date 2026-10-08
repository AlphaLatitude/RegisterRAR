import RegisterRAR.Law
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The numbers of the paper, certified

Every number that *The Radial Acceleration Relation from the Granularity of Hilbert Space* (v0-13)
computes from its inputs, recomputed from the inputs of Appendix A and certified by an interval:
each theorem states `lo < quantity < hi`, and every number in the interval rounds to the value the
paper quotes.  Observational values and their uncertainties are inputs, not claims.

## Inputs (Appendix A), as exact rationals

`c = 299792458 m/s`, `ℏ = 1.054571817e-34 J s`, `k_B = 1.380649e-23 J/K`,
`G = 6.67430e-11 m³ kg⁻¹ s⁻²`, `H₀ = 67.4 km/s/Mpc` with `1 Mpc = 3.0856775814913673e22 m`,
`Ω_Λ = 0.685`, the heliocentric constant `GM☉ = 1.32712440018e20 m³/s²`, `1 au = 149597870700 m`,
`1 kpc = 3.0856775814913673e19 m`; for comparison, `a₀ = 1.20 ± 0.02 ± 0.24` [McGaugh 2016] and
`1.19 ± 0.04 ± 0.09` [Desmond 2023], in `10⁻¹⁰ m/s²`, `H₀ ± 0.5` and `Ω_Λ ± 0.007` [Planck 2018],
and the local `H₀ = 73`.

## `π`, `ln 2` and `e`

They are Mathlib's `Real.pi`, `Real.log 2` and `Real.exp 1`, and they enter only through Mathlib's
bounds `3.141592 < π < 3.141593`, `0.6931471803 < ln 2 < 0.6931471808`, and
`2.7182818283 < e < 2.7182818286`.  Other values of `exp` are bounded by `1 + x ≤ eˣ` and, for
`0 < x < 1`, `eˣ < 1/(1 − x)`, applied to `x = 0.001` and raised to a power.

## Bridge to the chain

`reg` is the register of `Chain.lean` with these inputs, `π` and `ln 2`, the cell fixed from `G`,
and `L` from the horizon.  Its scale is the certified one (`reg_a0`), and the measured `G` meets
Jacobson's relation for it (`reg_jacobson`).
-/

open Real

-- `norm_num` evaluates powers such as `2.7182818286 ^ 233` exactly; raise Lean's guard on exponents.
set_option exponentiation.threshold 50000

namespace Register
namespace Numerics

local notation "c₀" => (299792458 : ℝ)
local notation "ℏ₀" => ((1054571817 : ℝ) / 10 ^ 43)
local notation "kB₀" => ((1380649 : ℝ) / 10 ^ 29)
local notation "G₀" => ((66743 : ℝ) / 10 ^ 15)
local notation "H₀" => ((67400 : ℝ) / ((30856775814913673 : ℝ) * 10 ^ 6))
local notation "ΩΛ₀" => ((685 : ℝ) / 1000)
local notation "GMs₀" => ((132712440018 : ℝ) * 10 ^ 9)
local notation "au₀" => ((149597870700 : ℝ))
local notation "kpc₀" => ((30856775814913673 : ℝ) * 10 ^ 3)

lemma ln2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

lemma lt_of_sq {Q a : ℝ} (hQ : 0 ≤ Q) (ha : 0 ≤ a) (h : a ^ 2 < Q ^ 2) : a < Q :=
  (pow_lt_pow_iff_left₀ ha hQ two_ne_zero).1 h

lemma lt_of_sq' {Q b : ℝ} (hQ : 0 ≤ Q) (hb : 0 ≤ b) (h : Q ^ 2 < b ^ 2) : Q < b :=
  (pow_lt_pow_iff_left₀ hQ hb two_ne_zero).1 h

/-! ## The horizon and the scale -/

/-- `H_∞ = H₀√Ω_Λ` -/
noncomputable def Hinf : ℝ := H₀ * Real.sqrt ΩΛ₀
/-- the de Sitter radius, `R_Λ = c/H_∞` -/
noncomputable def RL : ℝ := c₀ / Hinf
/-- the coefficient `(1 − ln 2)/2 ln 2` -/
noncomputable def κ : ℝ := (1 - Real.log 2) / (2 * Real.log 2)
/-- the scale, Eq. (7): `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)` -/
noncomputable def a0v : ℝ := (1 - Real.log 2) * c₀ ^ 2 / (2 * Real.log 2 * RL)

lemma Hinf_pos : 0 < Hinf := by unfold Hinf; positivity

lemma Hinf_sq : Hinf ^ 2 = H₀ ^ 2 * ΩΛ₀ := by
  unfold Hinf; rw [mul_pow, Real.sq_sqrt (by norm_num)]

lemma RL_pos : 0 < RL := by unfold RL; have := Hinf_pos; positivity

lemma cHinf_eq : c₀ ^ 2 / RL = c₀ * Hinf := by
  have := Hinf_pos; unfold RL; field_simp

lemma a0v_eq : a0v = κ * (c₀ * Hinf) := by
  have := ln2_pos.ne'; have := Hinf_pos.ne'
  unfold a0v κ RL
  field_simp

theorem Hinf_tight : 1.8078177e-18 < Hinf ∧ Hinf < 1.8078178e-18 := by
  constructor
  · apply lt_of_sq Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num
  · apply lt_of_sq' Hinf_pos.le (by norm_num); rw [Hinf_sq]; norm_num

theorem κ_tight : 0.2213475 < κ ∧ κ < 0.2213476 := by
  have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9; have h0 := ln2_pos
  unfold κ
  constructor
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith

theorem a0_tight : 1.1996372e-10 < a0v ∧ a0v < 1.199638e-10 := by
  obtain ⟨k1, k2⟩ := κ_tight
  obtain ⟨h1, h2⟩ := Hinf_tight
  have hH := Hinf_pos
  rw [a0v_eq]
  constructor
  · calc (1.1996372e-10 : ℝ) < 0.2213475 * (c₀ * 1.8078177e-18) := by norm_num
      _ < κ * (c₀ * Hinf) := mul_lt_mul'' k1 (by linarith) (by norm_num) (by norm_num)
  · calc κ * (c₀ * Hinf) < 0.2213476 * (c₀ * 1.8078178e-18) :=
          mul_lt_mul'' k2 (by linarith) (by linarith) (by positivity)
      _ < 1.199638e-10 := by norm_num

lemma a0v_pos : 0 < a0v := by have := a0_tight.1; linarith

/-- **The scale**, Eq. (13), Table I and Appendix A: `a₀ = 1.1996×10⁻¹⁰ m/s²`, `1.200` to the
precision quoted. -/
theorem a0_val : (1.19963e-10 < a0v ∧ a0v < 1.19964e-10) ∧ (1.1995e-10 < a0v ∧ a0v < 1.2005e-10) := by
  obtain ⟨h1, h2⟩ := a0_tight
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **The coefficient**, Appendix A: `(1 − ln 2)/2 ln 2 = 0.22135`; to four places it is `0.2213`,
so `a₀ = 0.2213 c²/R_Λ` in Eq. (13). -/
theorem coefficient : 0.221345 < κ ∧ κ < 0.221355 := by
  obtain ⟨k1, k2⟩ := κ_tight
  exact ⟨by linarith, by linarith⟩

/-- **The horizon** (Introduction, Appendix A): `H_∞ = 1.808×10⁻¹⁸ s⁻¹`, `R_Λ = 1.658×10²⁶ m`,
`c²/R_Λ = cH_∞ = 5.420×10⁻¹⁰ m/s²`. -/
theorem horizon_values :
    (1.8075e-18 < Hinf ∧ Hinf < 1.8085e-18) ∧ (1.6575e26 < RL ∧ RL < 1.6585e26) ∧
    (5.4195e-10 < c₀ ^ 2 / RL ∧ c₀ ^ 2 / RL < 5.4205e-10) := by
  obtain ⟨h1, h2⟩ := Hinf_tight
  have hH := Hinf_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · unfold RL; rw [lt_div_iff₀ hH]; linarith
  · unfold RL; rw [div_lt_iff₀ hH]; linarith
  · rw [cHinf_eq]; linarith
  · rw [cHinf_eq]; linarith

/-- **The companion's elastic bound** (Introduction, Table II): `πc²/12R_Λ = 1.42×10⁻¹⁰ m/s²`. -/
theorem elastic_bound :
    1.415e-10 < Real.pi * c₀ ^ 2 / (12 * RL) ∧ Real.pi * c₀ ^ 2 / (12 * RL) < 1.425e-10 := by
  have e : Real.pi * c₀ ^ 2 / (12 * RL) = Real.pi * (c₀ * Hinf) / 12 := by
    have := Hinf_pos; unfold RL; field_simp
  rw [e]
  obtain ⟨h1, h2⟩ := Hinf_tight
  have hH := Hinf_pos
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6
  constructor
  · have : 3.141592 * (c₀ * 1.8078177e-18) < Real.pi * (c₀ * Hinf) :=
      mul_lt_mul'' p1 (by linarith) (by norm_num) (by norm_num)
    have : (1.415e-10 : ℝ) < 3.141592 * (c₀ * 1.8078177e-18) / 12 := by norm_num
    linarith
  · have : Real.pi * (c₀ * Hinf) < 3.141593 * (c₀ * 1.8078178e-18) :=
      mul_lt_mul'' p2 (by linarith) Real.pi_pos.le (by positivity)
    have : 3.141593 * (c₀ * 1.8078178e-18) / 12 < (1.425e-10 : ℝ) := by norm_num
    linarith

/-- **The horizon's thermal energy, its temperature, and a string's matter** (Appendix A):
`k_BT_dS = ℏc/2πR_Λ = 3.034×10⁻⁵³ J`, `T_dS = 2.198×10⁻³⁰ K`, `u = (1 − ln 2)k_BT_dS =
9.311×10⁻⁵⁴ J`. -/
theorem thermal_values :
    (3.0335e-53 < ℏ₀ * c₀ / (2 * Real.pi * RL) ∧ ℏ₀ * c₀ / (2 * Real.pi * RL) < 3.0345e-53) ∧
    (2.1975e-30 < ℏ₀ * c₀ / (2 * Real.pi * RL) / kB₀ ∧
      ℏ₀ * c₀ / (2 * Real.pi * RL) / kB₀ < 2.1985e-30) ∧
    (9.3105e-54 < (1 - Real.log 2) * (ℏ₀ * c₀ / (2 * Real.pi * RL)) ∧
      (1 - Real.log 2) * (ℏ₀ * c₀ / (2 * Real.pi * RL)) < 9.3115e-54) := by
  have e : ℏ₀ * c₀ / (2 * Real.pi * RL) = ℏ₀ * Hinf / (2 * Real.pi) := by
    have := Hinf_pos; have := Real.pi_pos; unfold RL; field_simp
  rw [e]
  obtain ⟨h1, h2⟩ := Hinf_tight
  have hH := Hinf_pos
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6; have pp := Real.pi_pos
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  have k1 : 3.03424e-53 < ℏ₀ * Hinf / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have k2 : ℏ₀ * Hinf / (2 * Real.pi) < 3.03425e-53 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · calc (9.3105e-54 : ℝ) < (1 - 0.6931471808) * 3.03424e-53 := by norm_num
      _ < (1 - Real.log 2) * (ℏ₀ * Hinf / (2 * Real.pi)) :=
        mul_lt_mul'' (by linarith) k1 (by norm_num) (by norm_num)
  · calc (1 - Real.log 2) * (ℏ₀ * Hinf / (2 * Real.pi)) < (1 - 0.6931471803) * 3.03425e-53 :=
          mul_lt_mul'' (by linarith) k2 (by linarith) (by positivity)
      _ < (9.3115e-54 : ℝ) := by norm_num

/-- **The split, checked against Planck** (Sec. II): the energy inside the horizon is
`ln 2/Ω_Λ = 1.012` thermal energies per string, and the matter part of a string's energy is
`1 − ln 2 = 0.307`. -/
theorem string_energy_check :
    (1.0115 < Real.log 2 / ΩΛ₀ ∧ Real.log 2 / ΩΛ₀ < 1.0125) ∧
    (0.3065 < 1 - Real.log 2 ∧ 1 - Real.log 2 < 0.3075) := by
  have l1 := Real.log_two_gt_d9; have l2 := Real.log_two_lt_d9
  refine ⟨⟨?_, ?_⟩, ⟨by linarith, by linarith⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-! ## Against observation (Sec. VII) -/

/-- the relative uncertainty of `a₀` from Planck's `H₀ ± 0.5` and `Ω_Λ ± 0.007`, in quadrature -/
noncomputable def relErr : ℝ :=
  Real.sqrt ((1 / 2 / (674 / 10)) ^ 2 + (7 / 1000 / (2 * (685 / 1000))) ^ 2)
/-- McGaugh's total uncertainty, `√(0.02² + 0.24²) × 10⁻¹⁰` -/
noncomputable def SM : ℝ := Real.sqrt ((0.02e-10) ^ 2 + (0.24e-10) ^ 2)
/-- Desmond's total uncertainty, `√(0.04² + 0.09²) × 10⁻¹⁰` -/
noncomputable def SD : ℝ := Real.sqrt ((0.04e-10) ^ 2 + (0.09e-10) ^ 2)

lemma relErr_tight : 0.0090 < relErr ∧ relErr < 0.0091 := by
  unfold relErr
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma SM_tight : 2.408e-11 < SM ∧ SM < 2.409e-11 := by
  unfold SM
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma SD_tight : 9.848e-12 < SD ∧ SD < 9.849e-12 := by
  unfold SD
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **The uncertainty of the scale** (Sec. VII, Appendix A): `±0.011×10⁻¹⁰ m/s²`, a relative
`0.9%`. -/
theorem a0_uncertainty :
    (0.0085 < relErr ∧ relErr < 0.0095) ∧
    (1.05e-12 < a0v * relErr ∧ a0v * relErr < 1.15e-12) := by
  obtain ⟨r1, r2⟩ := relErr_tight
  obtain ⟨a1, a2⟩ := a0_tight
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · calc (1.05e-12 : ℝ) < 1.1996372e-10 * 0.0090 := by norm_num
      _ < a0v * relErr := mul_lt_mul'' a1 r1 (by norm_num) (by norm_num)
  · calc a0v * relErr < 1.199638e-10 * 0.0091 :=
          mul_lt_mul'' a2 r2 (by linarith) (by linarith)
      _ < (1.15e-12 : ℝ) := by norm_num

/-- **Against the measurements** (Sec. VII, Table I): the derived `a₀` lies `0.0σ` from McGaugh's
`1.20` and `0.1σ` from Desmond's `1.19`, counting the systematic errors. -/
theorem a0_sigmas :
    (-0.05 < (a0v - 1.20e-10) / SM ∧ (a0v - 1.20e-10) / SM < 0.05) ∧
    (0.05 < (a0v - 1.19e-10) / SD ∧ (a0v - 1.19e-10) / SD < 0.15) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨m1, m2⟩ := SM_tight
  obtain ⟨d1, d2⟩ := SD_tight
  have hM : 0 < SM := by linarith
  have hD : 0 < SD := by linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hM]; linarith
  · rw [div_lt_iff₀ hM]; linarith
  · rw [lt_div_iff₀ hD]; linarith
  · rw [div_lt_iff₀ hD]; linarith

/-- **With the local `H₀ = 73`** (Sec. VII): `a₀ = 1.30×10⁻¹⁰ m/s²`, `0.4σ` and `1.1σ` from the
measurements. -/
theorem a0_local_H0 :
    (1.295e-10 < a0v * 73 / 67.4 ∧ a0v * 73 / 67.4 < 1.305e-10) ∧
    (0.35 < (a0v * 73 / 67.4 - 1.20e-10) / SM ∧ (a0v * 73 / 67.4 - 1.20e-10) / SM < 0.45) ∧
    (1.05 < (a0v * 73 / 67.4 - 1.19e-10) / SD ∧ (a0v * 73 / 67.4 - 1.19e-10) / SD < 1.15) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨m1, m2⟩ := SM_tight
  obtain ⟨d1, d2⟩ := SD_tight
  have hM : 0 < SM := by linarith
  have hD : 0 < SD := by linarith
  -- `73/67.4 = 365/337`, a ratio `linarith` can clear
  rw [show a0v * 73 / 67.4 = a0v * 365 / 337 by ring]
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hM]; linarith
  · rw [div_lt_iff₀ hM]; linarith
  · rw [lt_div_iff₀ hD]; linarith
  · rw [div_lt_iff₀ hD]; linarith

/-- **The tolerance's mean, read from the data** (Sec. VII): the scale goes as the square of the
mean, so McGaugh's `a₀` puts the mean at `√(1.20/a₀) = 1.00`, with the spread `0.24/(2 × 1.20) =
0.10`. -/
theorem tolerance_mean_from_data :
    (0.995 < Real.sqrt (1.20e-10 / a0v) ∧ Real.sqrt (1.20e-10 / a0v) < 1.005) ∧
    (0.095 < SM / (2 * 1.20e-10) ∧ SM / (2 * 1.20e-10) < 0.105) := by
  obtain ⟨a1, a2⟩ := a0_tight
  obtain ⟨m1, m2⟩ := SM_tight
  have ha := a0v_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]; linarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-! ## The coefficients of Sec. VIII and Table II -/

/-- **In units of `cH₀`** (Sec. VIII, Appendix A): `cH₀ = 6.548×10⁻¹⁰ m/s²`; the derived scale is
`0.1832 cH₀` (`0.183`), the measured `1.20×10⁻¹⁰` is `0.1833 cH₀`; `cH₀/6 = 1.091×10⁻¹⁰` (`1/6 =
0.167`) and `cH₀/2π = 1.042×10⁻¹⁰` (`1/2π = 0.159`). -/
theorem cH0_coefficients :
    (6.5475e-10 < c₀ * H₀ ∧ c₀ * H₀ < 6.5485e-10) ∧
    (0.18315 < a0v / (c₀ * H₀) ∧ a0v / (c₀ * H₀) < 0.18325) ∧
    (0.18325 < 1.20e-10 / (c₀ * H₀) ∧ 1.20e-10 / (c₀ * H₀) < 0.18335) ∧
    (1.0905e-10 < c₀ * H₀ / 6 ∧ c₀ * H₀ / 6 < 1.0915e-10) ∧
    (1.0415e-10 < c₀ * H₀ / (2 * Real.pi) ∧ c₀ * H₀ / (2 * Real.pi) < 1.0425e-10) ∧
    (0.1585 < 1 / (2 * Real.pi) ∧ 1 / (2 * Real.pi) < 0.1595) := by
  obtain ⟨a1, a2⟩ := a0_tight
  have p1 := Real.pi_gt_d6; have p2 := Real.pi_lt_d6; have pp := Real.pi_pos
  have hc : (0 : ℝ) < c₀ * H₀ := by norm_num
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ hc]
    have : (0.18315 : ℝ) * (c₀ * H₀) < 1.1996372e-10 := by norm_num
    linarith
  · rw [div_lt_iff₀ hc]
    have : (1.199638e-10 : ℝ) < 0.18325 * (c₀ * H₀) := by norm_num
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    have : (1.0415e-10 : ℝ) * (2 * 3.141593) < c₀ * H₀ := by norm_num
    exact (mul_lt_mul_of_pos_left (by linarith : 2 * Real.pi < 2 * 3.141593) (by norm_num)).trans this
  · rw [div_lt_iff₀ (by positivity)]
    have : c₀ * H₀ < (1.0425e-10 : ℝ) * (2 * 3.141592) := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left (by linarith : 2 * 3.141592 < 2 * Real.pi) (by norm_num))
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith

/-! ## The law at the scales of Sec. VI and Appendix A -/

/-- **The baryonic Tully–Fisher speeds** (Sec. VI, Table I): `v⁴ = a₀GM` gives `112 km/s` for
`10¹⁰ M☉` and `200 km/s` for `10¹¹ M☉`. -/
theorem tully_fisher_speeds :
    ((111500 : ℝ) ^ 4 < a0v * (1e10 * GMs₀) ∧ a0v * (1e10 * GMs₀) < (112500 : ℝ) ^ 4) ∧
    ((199500 : ℝ) ^ 4 < a0v * (1e11 * GMs₀) ∧ a0v * (1e11 * GMs₀) < (200500 : ℝ) ^ 4) := by
  obtain ⟨a1, a2⟩ := a0_tight
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : (111500 : ℝ) ^ 4 < 1.1996372e-10 * (1e10 * GMs₀) := by norm_num
    exact this.trans (mul_lt_mul_of_pos_right a1 (by norm_num))
  · have : 1.199638e-10 * (1e10 * GMs₀) < (112500 : ℝ) ^ 4 := by norm_num
    exact (mul_lt_mul_of_pos_right a2 (by norm_num)).trans this
  · have : (199500 : ℝ) ^ 4 < 1.1996372e-10 * (1e11 * GMs₀) := by norm_num
    exact this.trans (mul_lt_mul_of_pos_right a1 (by norm_num))
  · have : 1.199638e-10 * (1e11 * GMs₀) < (200500 : ℝ) ^ 4 := by norm_num
    exact (mul_lt_mul_of_pos_right a2 (by norm_num)).trans this

/-- **Where the deep regime begins** (Appendix A): `√(GM/a₀) = 1.05×10¹⁵ m = 7031 au` for the Sun,
and `10.8 kpc` for `10¹¹ M☉`. -/
theorem deep_radii :
    (1.045e15 < Real.sqrt (GMs₀ / a0v) ∧ Real.sqrt (GMs₀ / a0v) < 1.055e15) ∧
    (7030.5 * au₀ < Real.sqrt (GMs₀ / a0v) ∧ Real.sqrt (GMs₀ / a0v) < 7031.5 * au₀) ∧
    (10.75 * kpc₀ < Real.sqrt (1e11 * GMs₀ / a0v) ∧
      Real.sqrt (1e11 * GMs₀ / a0v) < 10.85 * kpc₀) := by
  obtain ⟨a1, a2⟩ := a0_tight
  have ha := a0v_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (1.045e15 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ < (1.055e15 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (7030.5 * au₀) ^ 2 * 1.199638e-10 < GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ < (7031.5 * au₀) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (10.75 * kpc₀) ^ 2 * 1.199638e-10 < 1e11 * GMs₀ := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : 1e11 * GMs₀ < (10.85 * kpc₀) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))

/-- **The solar system** (Sec. VI, Appendix A): at Earth's orbit `g_N = 5.93×10⁻³ m/s²` and
`h = √(g_N/a₀) = 7031`; at Neptune's, `30.07 au`, `g_N = 6.56×10⁻⁶ m/s²` and `h = 233.8`, `234` to
the nearest integer. -/
theorem solar_system :
    (5.925e-3 < GMs₀ / au₀ ^ 2 ∧ GMs₀ / au₀ ^ 2 < 5.935e-3) ∧
    (7030.5 < Real.sqrt (GMs₀ / au₀ ^ 2 / a0v) ∧ Real.sqrt (GMs₀ / au₀ ^ 2 / a0v) < 7031.5) ∧
    (6.555e-6 < GMs₀ / (30.07 * au₀) ^ 2 ∧ GMs₀ / (30.07 * au₀) ^ 2 < 6.565e-6) ∧
    (233.8145 < Real.sqrt (GMs₀ / (30.07 * au₀) ^ 2 / a0v) ∧
      Real.sqrt (GMs₀ / (30.07 * au₀) ^ 2 / a0v) < 233.8151) := by
  obtain ⟨a1, a2⟩ := a0_tight
  have ha := a0v_pos
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩, ⟨by norm_num, by norm_num⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (7030.5 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ / au₀ ^ 2 := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ / au₀ ^ 2 < (7031.5 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ ha]
    have : (233.8145 : ℝ) ^ 2 * 1.199638e-10 < GMs₀ / (30.07 * au₀) ^ 2 := by norm_num
    exact (mul_lt_mul_of_pos_left a2 (by norm_num)).trans this
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ ha]
    have : GMs₀ / (30.07 * au₀) ^ 2 < (233.8151 : ℝ) ^ 2 * 1.1996372e-10 := by norm_num
    exact this.trans (mul_lt_mul_of_pos_left a1 (by norm_num))

/-- **The departure at Neptune** (Sec. VI, Table I, Appendix A): `e^{−h} = 2.9×10⁻¹⁰²`, and the
departure from Newton's law, `e^{−h}/(1 − e^{−h})`, is `3×10⁻¹⁰²` of `g_N`. -/
theorem neptune_departure :
    let hN := Real.sqrt (GMs₀ / (30.07 * au₀) ^ 2 / a0v)
    (2.85e-102 < Real.exp (-hN) ∧ Real.exp (-hN) < 2.95e-102) ∧
    (2.5e-102 < Real.exp (-hN) / (1 - Real.exp (-hN)) ∧
      Real.exp (-hN) / (1 - Real.exp (-hN)) < 3.5e-102) := by
  intro hN
  obtain ⟨-, -, -, ⟨s1, s2⟩⟩ := solar_system
  have s1' : (233.8145 : ℝ) < hN := s1
  have s2' : hN < (233.8151 : ℝ) := s2
  -- `e^{233}`
  have e233 : Real.exp 233 = Real.exp 1 ^ 233 := by rw [← Real.exp_nat_mul]; norm_num
  have E1 : (2.7182818283 : ℝ) ^ 233 < Real.exp 233 := by
    rw [e233]; exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have E2 : Real.exp 233 < (2.7182818286 : ℝ) ^ 233 := by
    rw [e233]; exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  -- `e^{0.001}`
  have f1 : (1.0009999 : ℝ) < Real.exp 0.001 := by
    have := Real.add_one_le_exp (0.001 : ℝ); linarith
  have f2 : Real.exp 0.001 < 1 / (1 - 0.001) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  -- `e^{0.8145} > 1.0009999^814 · 1.0005` and `e^{0.8151} < (1/0.999)^815 · 1/(1 − 0.0001)`
  have g1 : (1.0009999 : ℝ) ^ 814 * 1.0005 < Real.exp 0.8145 := by
    have e : Real.exp 0.8145 = Real.exp 0.001 ^ 814 * Real.exp 0.0005 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    apply mul_lt_mul (pow_lt_pow_left₀ f1 (by norm_num) (by norm_num))
    · have := Real.add_one_le_exp (0.0005 : ℝ); linarith
    · norm_num
    · positivity
  have g2 : Real.exp 0.8151 < (1 / (1 - 0.001)) ^ 815 * (1 / (1 - 0.0001)) := by
    have e : Real.exp 0.8151 = Real.exp 0.001 ^ 815 * Real.exp 0.0001 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    exact mul_lt_mul'' (pow_lt_pow_left₀ f2 (Real.exp_pos _).le (by norm_num))
      (Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num))
      (by positivity) (by positivity)
  -- `e^{h}` lies between `e^{233.8145}` and `e^{233.8151}`
  have hlo : Real.exp 233 * Real.exp 0.8145 < Real.exp hN := by
    rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
  have hhi : Real.exp hN < Real.exp 233 * Real.exp 0.8151 := by
    rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
  have LB : (2.7182818283 : ℝ) ^ 233 * ((1.0009999 : ℝ) ^ 814 * 1.0005) < Real.exp hN :=
    (mul_lt_mul'' E1 g1 (by norm_num) (by norm_num)).trans hlo
  have UB : Real.exp hN <
      (2.7182818286 : ℝ) ^ 233 * ((1 / (1 - 0.001)) ^ 815 * (1 / (1 - 0.0001))) :=
    hhi.trans (mul_lt_mul'' E2 g2 (Real.exp_pos _).le (Real.exp_pos _).le)
  have hE := Real.exp_pos hN
  have hx : Real.exp (-hN) = 1 / Real.exp hN := by rw [Real.exp_neg, one_div]
  have x1 : 2.85e-102 < Real.exp (-hN) := by
    rw [hx, lt_div_iff₀ hE]
    have : (2.85e-102 : ℝ) * ((2.7182818286 : ℝ) ^ 233 * ((1 / (1 - 0.001)) ^ 815 *
      (1 / (1 - 0.0001)))) < 1 := by norm_num
    exact (mul_lt_mul_of_pos_left UB (by norm_num)).trans this
  have x2 : Real.exp (-hN) < 2.95e-102 := by
    rw [hx, div_lt_iff₀ hE]
    have : (1 : ℝ) < 2.95e-102 * ((2.7182818283 : ℝ) ^ 233 * ((1.0009999 : ℝ) ^ 814 * 1.0005)) := by
      norm_num
    exact this.trans (mul_lt_mul_of_pos_left LB (by norm_num))
  have hpos : 0 < 1 - Real.exp (-hN) := by linarith
  refine ⟨⟨x1, x2⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- the relation as a function of `x = g_N/a₀`: `a/g_N = 1/(1 − e^{−√x})` -/
noncomputable def rar (x : ℝ) : ℝ := 1 / (1 - Real.exp (-Real.sqrt x))

lemma rar_eq (s : ℝ) (hs : 0 < s) :
    1 / (1 - Real.exp (-s)) = Real.exp s / (Real.exp s - 1) := by
  have h1 : 1 < Real.exp s := by
    have := Real.exp_lt_exp.2 hs; rwa [Real.exp_zero] at this
  rw [Real.exp_neg]
  have : Real.exp s - 1 ≠ 0 := by linarith
  have : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp

/-- **The relation at four accelerations** (Sec. VI, Appendix A): `a/g_N = 1.04, 1.58, 3.69, 10.5`
at `g_N/a₀ = 10, 1, 0.1, 0.01`; the departure is `4%` at `10a₀` and `58%` at `a₀`. -/
theorem rar_table :
    (1.035 < rar 10 ∧ rar 10 < 1.045) ∧ (1.575 < rar 1 ∧ rar 1 < 1.585) ∧
    (3.685 < rar 0.1 ∧ rar 0.1 < 3.695) ∧ (10.45 < rar 0.01 ∧ rar 0.01 < 10.55) ∧
    (0.035 < rar 10 - 1 ∧ rar 10 - 1 < 0.045) ∧ (0.575 < rar 1 - 1 ∧ rar 1 - 1 < 0.585) := by
  have f1 : (1.0009999 : ℝ) < Real.exp 0.001 := by
    have := Real.add_one_le_exp (0.001 : ℝ); linarith
  have f2 : Real.exp 0.001 < 1 / (1 - 0.001) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  -- `x = 10`: `23.3 < e^{√10} < 24`
  have T10 : 1.035 < rar 10 ∧ rar 10 < 1.045 := by
    have hs1 : (3.1622 : ℝ) < Real.sqrt 10 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs2 : Real.sqrt 10 < 3.1623 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have he3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have hE1 : (23.3 : ℝ) < Real.exp (Real.sqrt 10) := by
      have ha : Real.exp 3 * Real.exp 0.1622 < Real.exp (Real.sqrt 10) := by
        rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
      have hb : (0.1622 : ℝ) + 1 ≤ Real.exp 0.1622 := Real.add_one_le_exp _
      have hc : (2.7182818283 : ℝ) ^ 3 < Real.exp 3 := by
        rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
      have hd : (2.7182818283 : ℝ) ^ 3 * 1.1622 < Real.exp 3 * Real.exp 0.1622 := by
        apply mul_lt_mul hc (by linarith) (by norm_num) (Real.exp_pos _).le
      have : (23.3 : ℝ) < 2.7182818283 ^ 3 * 1.1622 := by norm_num
      linarith
    have hE2 : Real.exp (Real.sqrt 10) < 24 := by
      have ha : Real.exp (Real.sqrt 10) < Real.exp 3 * Real.exp 0.1623 := by
        rw [← Real.exp_add]; exact Real.exp_lt_exp.2 (by linarith)
      have hb : Real.exp 0.1623 < 1 / (1 - 0.1623) :=
        Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
      have hc : Real.exp 3 < (2.7182818286 : ℝ) ^ 3 := by
        rw [he3]; exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
      have hd : Real.exp 3 * Real.exp 0.1623 < (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) := by
        apply mul_lt_mul'' hc hb (Real.exp_pos _).le (Real.exp_pos _).le
      have : (2.7182818286 : ℝ) ^ 3 * (1 / (1 - 0.1623)) < 24 := by norm_num
      linarith
    unfold rar
    rw [rar_eq (Real.sqrt 10) (by linarith)]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  -- `x = 1`: `e` itself
  have T1 : 1.575 < rar 1 ∧ rar 1 < 1.585 := by
    have e1 := Real.exp_one_gt_d9; have e2 := Real.exp_one_lt_d9
    unfold rar
    rw [Real.sqrt_one, rar_eq 1 one_pos]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  -- `x = 0.1`: `0.3162 < √0.1 < 0.3163`, and `e^{0.3162}`, `e^{0.3163}` from `e^{0.001}`
  have T01 : 3.685 < rar 0.1 ∧ rar 0.1 < 3.695 := by
    have hs1 : (0.3162 : ℝ) < Real.sqrt 0.1 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs2 : Real.sqrt 0.1 < 0.3163 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have g1 : (1.0009999 : ℝ) ^ 316 * 1.0002 < Real.exp (Real.sqrt 0.1) := by
      have e : Real.exp 0.3162 = Real.exp 0.001 ^ 316 * Real.exp 0.0002 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h0 : Real.exp 0.3162 < Real.exp (Real.sqrt 0.1) := Real.exp_lt_exp.2 hs1
      have : (1.0009999 : ℝ) ^ 316 * 1.0002 < Real.exp 0.3162 := by
        rw [e]
        apply mul_lt_mul (pow_lt_pow_left₀ f1 (by norm_num) (by norm_num))
        · have := Real.add_one_le_exp (0.0002 : ℝ); linarith
        · norm_num
        · positivity
      linarith
    have g2 : Real.exp (Real.sqrt 0.1) < (1 / (1 - 0.001)) ^ 316 * (1 / (1 - 0.0003)) := by
      have e : Real.exp 0.3163 = Real.exp 0.001 ^ 316 * Real.exp 0.0003 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      have h0 : Real.exp (Real.sqrt 0.1) < Real.exp 0.3163 := Real.exp_lt_exp.2 hs2
      have : Real.exp 0.3163 < (1 / (1 - 0.001)) ^ 316 * (1 / (1 - 0.0003)) := by
        rw [e]
        exact mul_lt_mul'' (pow_lt_pow_left₀ f2 (Real.exp_pos _).le (by norm_num))
          (Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num))
          (by positivity) (by positivity)
      linarith
    have c1 : (1.3711 : ℝ) < 1.0009999 ^ 316 * 1.0002 := by norm_num
    have c2 : ((1 : ℝ) / (1 - 0.001)) ^ 316 * (1 / (1 - 0.0003)) < 1.3724 := by norm_num
    have k1 : (1.3711 : ℝ) < Real.exp (Real.sqrt 0.1) := c1.trans g1
    have k2 : Real.exp (Real.sqrt 0.1) < 1.3724 := g2.trans c2
    unfold rar
    rw [rar_eq (Real.sqrt 0.1) (by linarith)]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  -- `x = 0.01`: `√0.01 = 0.1`, and `e^{0.1} = (e^{0.001})^{100}`
  have T001 : 10.45 < rar 0.01 ∧ rar 0.01 < 10.55 := by
    have hs : Real.sqrt 0.01 = 0.1 := by
      rw [show (0.01 : ℝ) = 0.1 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    have e : Real.exp 0.1 = Real.exp 0.001 ^ 100 := by rw [← Real.exp_nat_mul]; norm_num
    have g1 : (1.0009999 : ℝ) ^ 100 < Real.exp 0.1 := by
      rw [e]; exact pow_lt_pow_left₀ f1 (by norm_num) (by norm_num)
    have g2 : Real.exp 0.1 < (1 / (1 - 0.001)) ^ 100 := by
      rw [e]; exact pow_lt_pow_left₀ f2 (Real.exp_pos _).le (by norm_num)
    have c1 : (1.1048 : ℝ) < 1.0009999 ^ 100 := by norm_num
    have c2 : ((1 : ℝ) / (1 - 0.001)) ^ 100 < 1.1058 := by norm_num
    have k1 : (1.1048 : ℝ) < Real.exp 0.1 := c1.trans g1
    have k2 : Real.exp 0.1 < 1.1058 := g2.trans c2
    unfold rar
    rw [hs, rar_eq 0.1 (by norm_num)]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  exact ⟨T10, T1, T01, T001, ⟨by linarith [T10.1], by linarith [T10.2]⟩,
    ⟨by linarith [T1.1], by linarith [T1.2]⟩⟩

/-! ## The register of the measured constants -/

/-- the cell fixed from `G`: `ℓ_c = √(π ln 2 ℏG/c³)` -/
noncomputable def lc : ℝ := Real.sqrt (Real.pi * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3))

lemma lc_pos : 0 < lc := by
  have := Real.pi_pos; have := ln2_pos; unfold lc; positivity

lemma lc_sq : lc ^ 2 = Real.pi * Real.log 2 * (ℏ₀ * G₀ / c₀ ^ 3) := by
  have := Real.pi_pos; have := ln2_pos; unfold lc; rw [Real.sq_sqrt (by positivity)]

/-- **The register of the measured constants**: `c`, `ℏ`, `k_B` measured, the cell fixed from `G`,
`L = 2πR_Λ/ℓ_c` from the horizon, and Mathlib's `π` and `ln 2`. -/
noncomputable def reg : Reg where
  c := c₀
  ℏ := ℏ₀
  kB := kB₀
  ℓc := lc
  L := 2 * Real.pi * RL / lc
  pi := Real.pi
  ln2 := Real.log 2
  c_pos := by norm_num
  ℏ_pos := by norm_num
  kB_pos := by norm_num
  ℓc_pos := lc_pos
  L_pos := by have := lc_pos; have := RL_pos; have := Real.pi_pos; positivity
  pi_pos := Real.pi_pos
  ln2_pos := ln2_pos
  ln2_lt_one := by have := Real.log_two_lt_d9; linarith

/-- The register's largest ring has the observed de Sitter radius. -/
theorem reg_RL : reg.RL = RL := by
  have := lc_pos; have := Real.pi_pos
  show 2 * Real.pi * RL / lc * lc / (2 * Real.pi) = RL
  field_simp

/-- **The chain's scale is the certified one**: `reg.a₀ = a₀`. -/
theorem reg_a0 : reg.a0 = a0v := by
  unfold Reg.a0 a0v
  rw [reg_RL]
  rfl

/-- **The measured `G` meets Jacobson's relation** for the register of the measured constants. -/
theorem reg_jacobson : G₀ = reg.c ^ 3 * reg.kB / (4 * reg.ℏ * reg.η) := by
  have := lc_pos; have := Real.pi_pos; have := ln2_pos
  rw [reg.eta_eq]
  show G₀ = c₀ ^ 3 * kB₀ / (4 * ℏ₀ * (Real.pi * kB₀ * Real.log 2 / (4 * lc ^ 2)))
  rw [lc_sq]
  field_simp

end Numerics
end Register
