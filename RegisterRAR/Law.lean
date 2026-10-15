import RegisterRAR.Chain
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Secs. III–IX of the paper: the share, the threshold, the law, two bodies, and the scale at every epoch

Formal counterpart of Secs. III–IX of *The Radial Acceleration Relation from the Granularity of
Hilbert Space* (v0-18).  As in `Chain.lean`, each physical input is a named hypothesis of the
theorems that use it, and nothing is declared as an axiom.

* `Law.share_of_equipartition` (Sec. III): by Postulate 1 a body's energy is held by strings, a
  string that does not carry the body's information holds none of the body's energy, and
  equipartition gives each string that carries it the same share; so the energy is the number of
  carriers times that share.
* `Reg.share_acceleration`, Eq. (4): with the body's energy held by the fraction `b` of the
  sphere's strings at two Landauer energies each, against Eq. (3) at `g_N`, the acceleration is
  `g_N/b`.
* `Reg.fill_fraction`, Eqs. (5)–(7): the body's energy per string, two Landauer energies at the
  Unruh temperature of `g_N`, counted in units of a string's matter `u = (1 − ln 2)k_BT_dS`, is
  `f = g_N/a₀` with `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`.
* `Reg.law`, Eq. (10): with the threshold exponential with mean one in amplitude (`hME`, maximum
  entropy with one qubit as the only scale), the fraction of carriers is `b = 1 − e^{−√f}`, and
  `a = g_N/(1 − e^{−√(g_N/a₀)})`.
* `Reg.law_scale_mean` (Sec. VIII): a threshold of mean `μ` would give the scale `μ²a₀`.
* `Law.classical_limit` (Sec. VIII): a classical share, the probability `b = f` in place of the
  amplitude, would give `a = a₀` and rotation speeds rising as `√r`; flat rotation curves
  therefore support Postulate 1.
* `Reg.scale_over_time`, Eq. (16) (Sec. IX): with Jacobson's `G`, `a₀` is a fixed fraction of the
  Planck acceleration `√(c⁷/ℏG)` and `Λ = 12πc³/(L²ℏG ln 2)`; the same formula with another `G'`
  gives twice the scale only if `G' = G/4`.
* `Law.near_limit` (Sec. VI), `Law.deep_limit` and `Law.tully_fisher`, Eqs. (11)–(12): near
  the body `a = g_N(1 + e^{−h}) + g_N e^{−2h}/(1 − e^{−h})`, so Newton's law returns
  exponentially; far from it `a` lies within `a₀h³` of `√(a₀g_N) + g_N/2` for `h ≤ 1/2`; and on
  a circular orbit in the deep regime `v⁴ = a₀GM`.
* `Reg.share_reading`, `Law.two_body_split`, `Law.two_body_deep`, `Law.two_body_equal`
  (Sec. VII): on a sphere the body's share at a string, `Mc²/N_s`, equals the carrier
  fraction times what a carrier holds, `b·2k_BT_a ln 2`, so Eq. (10) is unchanged when the
  share is read from the acceleration at the patch, the reading that conserves momentum
  between two bodies; momentum conservation (`hmom`, Postulate 1) splits the force between two
  bodies as `F/M₁` and `F/M₂`; and Milgrom's virial theorem for the deep regime (`hvir`),
  Eq. (14), gives a force whose test-body limit is Eq. (11) and whose equal-mass value is
  `(4/3)(√2 − 1) M√(GMa₀)/r`.  The field equation and the virial theorem are vector calculus
  and enter as `hvir`; Lean checks what follows from them.

The amplitude `h = √f` follows from Postulate 1 with Palmer's rule (Sec. II): a string that
carries the body's information is one of its qubits, so its share of the body is the fraction `f`
of a whole qubit, and the amplitude of that share is `√f`, in units of one whole qubit.  It
enters through the argument of `hME`.  The fraction `b` of carriers is the probability that the
threshold of a string's receiving cell lies below `h`, and so the fraction of the sphere's
strings that carry the body's information.
-/

open Real Finset

namespace Register

namespace Law

/-- **The share of a body's energy** (Sec. III), in finite form.  The body is all the mass inside
the sphere, so a string's share is of that total, not of each star within it.  The body's energy
`E` is held by the strings `S` of the sphere (`hsum`; by Postulate 1 all the mass and light of the
universe consists of strings); where a string does not carry the body's information, its
receiving cell keeps the state it has without the body, and the string holds none of the body's
Landauer energies there (`hoff`); and equipartition gives each carrier the same share `ε`
(`heq`).  Then `E = |C| ε`: the energy is held by the carriers alone. -/
theorem share_of_equipartition {ι : Type*} (S C : Finset ι) (hCS : C ⊆ S) (e : ι → ℝ) (E ε : ℝ)
    (hsum : ∑ i ∈ S, e i = E) (hoff : ∀ i ∈ S, i ∉ C → e i = 0) (heq : ∀ i ∈ C, e i = ε) :
    E = (C.card : ℝ) * ε := by
  rw [← hsum, ← Finset.sum_subset hCS hoff, Finset.sum_congr rfl heq, Finset.sum_const,
    nsmul_eq_mul]

/-- `e^{−h} < 1` for `h > 0`. -/
lemma exp_neg_lt_one {h : ℝ} (hh : 0 < h) : Real.exp (-h) < 1 := by
  have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
  rwa [Real.exp_zero] at this

/-- Mathlib's Taylor bound for `exp`, with three terms: for `0 ≤ h ≤ 1`,
`e^{−h}` lies within `2h³/9` of `1 − h + h²/2`. -/
lemma exp_neg_taylor {h : ℝ} (hh : 0 ≤ h) (h1 : h ≤ 1) :
    1 - h + h ^ 2 / 2 - 2 / 9 * h ^ 3 ≤ Real.exp (-h) ∧
      Real.exp (-h) ≤ 1 - h + h ^ 2 / 2 + 2 / 9 * h ^ 3 := by
  have hx : |(-h)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hh]; exact h1
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (-h) ^ m / (m.factorial : ℝ) = 1 - h + h ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, pow_one, div_one]
    ring
  have hc : |(-h)| ^ 3 * ((Nat.succ 3 : ℕ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) : ℝ)
      = 2 / 9 * h ^ 3 := by
    rw [abs_neg, abs_of_nonneg hh, show Nat.succ 3 = 4 from rfl, show Nat.factorial 3 = 6 from rfl]
    push_cast
    ring
  rw [hs, hc] at hb
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  constructor <;> linarith

end Law

namespace Reg

variable (R : Reg)

/-- **The scale**, Eq. (7): `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`. -/
noncomputable def a0 : ℝ := (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * R.RL)

lemma a0_pos : 0 < R.a0 := by
  reg_facts R
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hRL := R.RL_pos
  unfold a0
  exact div_pos (mul_pos hm (by positivity)) (by positivity)

/-- **Eq. (4): fewer carriers, the same energy, a higher temperature.**  The body's energy is two
Landauer energies at the Unruh temperature `T_N` of `g_N` for each of the sphere's `N_s` strings
(`hN`, Eq. (3) at `g_N`, `Reg.newton_share`), and it is held by the fraction `b` of them at the
temperature `T_a` of the acceleration `a`, two Landauer energies each (`hS`, the Komar energy held
by the carriers, `Law.share_of_equipartition`).  With `I1` for both temperatures, `a = g_N/b`. -/
theorem share_acceleration (M Ns b TN Ta gN a : ℝ) (hNs : 0 < Ns) (hb : 0 < b) (hgN : 0 < gN)
    (ha : 0 < a)
    (hN : M * R.c ^ 2 = 2 * Ns * (R.kB * TN * R.ln2))
    (hS : M * R.c ^ 2 = 2 * (b * Ns) * (R.kB * Ta * R.ln2))
    (I1N : R.kB * TN = R.ℏ / (R.La gN * R.tc)) (I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc)) :
    a = gN / b := by
  reg_facts R
  have h1 := R.T_Unruh gN TN hgN I1N
  have h2 := R.T_Unruh a Ta ha I1a
  have e := hN.symm.trans hS
  rw [h1, h2] at e
  have hK : 0 < 2 * Ns * (R.ℏ / (2 * R.pi * R.c) * R.ln2) := by positivity
  have e1 : 2 * Ns * (R.ℏ * gN / (2 * R.pi * R.c) * R.ln2)
      = gN * (2 * Ns * (R.ℏ / (2 * R.pi * R.c) * R.ln2)) := by ring
  have e2 : 2 * (b * Ns) * (R.ℏ * a / (2 * R.pi * R.c) * R.ln2)
      = (b * a) * (2 * Ns * (R.ℏ / (2 * R.pi * R.c) * R.ln2)) := by ring
  have key : gN = b * a := by
    apply mul_right_cancel₀ hK.ne'
    rw [← e1, ← e2]
    exact e
  rw [key, mul_comm b a, mul_div_assoc, div_self hb.ne', mul_one]

/-- **The two readings of a string's share** (Sec. VII).  Sec. IV reads the body's share at a
string of the sphere as the body's energy per string, `E = Mc²/N_s`.  Eq. (4), `hS`, reads it as
the carrier fraction times what a carrier holds, two Landauer energies at the sphere's
temperature.  On a sphere the two are the same number, so Eq. (10) is unchanged by the second
reading.  Between two bodies the temperature varies over a surface, and only the second reading
conserves momentum (Sec. VII). -/
theorem share_reading (M Ns b Ta : ℝ) (hNs : Ns ≠ 0)
    (hS : M * R.c ^ 2 = 2 * (b * Ns) * (R.kB * Ta * R.ln2)) :
    M * R.c ^ 2 / Ns = b * (2 * R.kB * Ta * R.ln2) := by
  rw [hS, div_eq_iff hNs]
  ring

/-- **What reaches a string**, Eqs. (5)–(7).  The body's energy per string, two Landauer energies at
the Unruh temperature `T_N` of `g_N` (`I1N`), counted in units of a string's matter
`u = (1 − ln 2)ε_s`, with a string's energy `ε_s = k_BT_dS` (`hεs`, from `string_energy`) and
the Gibbons–Hawking temperature (`I1dS`), is `f = g_N/a₀`. -/
theorem fill_fraction (gN TN TdS εs : ℝ) (hgN : 0 < gN)
    (I1N : R.kB * TN = R.ℏ / (R.La gN * R.tc)) (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (hεs : εs = R.kB * TdS) :
    2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs) = gN / R.a0 := by
  reg_facts R
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hm' := hm.ne'
  have hRL := R.RL_pos.ne'
  have h1 := R.T_Unruh gN TN hgN I1N
  have h2 := (R.T_dS TdS I1dS).2
  rw [hεs, h2, show 2 * R.kB * TN * R.ln2 = 2 * (R.kB * TN) * R.ln2 by ring, h1]
  unfold a0
  field_simp

/-- **The law**, Eq. (10).  The threshold's survival function is `e^{−x}` (`hME`: maximum entropy
for a positive quantity whose only scale, one qubit, is its mean), so the strings whose threshold
lies below the amplitude `√(g_N/a₀)` are the fraction `b = 1 − e^{−√(g_N/a₀)}` (`hb`), and with
`a = g_N/b` (`share_acceleration`) the relation follows. -/
theorem law (gN a b : ℝ) (surv : ℝ → ℝ) (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x))
    (hb : b = 1 - surv (Real.sqrt (gN / R.a0))) (hab : a = gN / b) :
    a = gN / (1 - Real.exp (-Real.sqrt (gN / R.a0))) := by
  rw [hab, hb, hME _ (Real.sqrt_nonneg _)]

/-- **The scale goes as the square of the threshold's mean** (Sec. VIII).  Were the threshold
exponential with mean `μ` instead of one qubit (`hME`), the law would keep its form with the scale
`μ²a₀`; so the measured scale fixes `μ` (`Numerics.threshold_mean_from_data`). -/
theorem law_scale_mean (gN a b μ : ℝ) (hμ : 0 < μ) (surv : ℝ → ℝ)
    (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x / μ))
    (hb : b = 1 - surv (Real.sqrt (gN / R.a0))) (hab : a = gN / b) :
    a = gN / (1 - Real.exp (-Real.sqrt (gN / (μ ^ 2 * R.a0)))) := by
  have hs : Real.sqrt (gN / (μ ^ 2 * R.a0)) = Real.sqrt (gN / R.a0) / μ := by
    rw [show gN / (μ ^ 2 * R.a0) = gN / R.a0 / μ ^ 2 by rw [div_div, mul_comm],
      Real.sqrt_div' _ (sq_nonneg μ), Real.sqrt_sq hμ.le]
  rw [hab, hb, hME _ (Real.sqrt_nonneg _), hs, neg_div]

/-- **The scale and `Λ` at every epoch** (Sec. IX, Eq. (16)).  With Jacobson's `G` (`hJ`, which
gives `G = c³ℓ_c²/(πℏ ln 2)`, `Reg.G_eq`) and `Λ = 3/R_Λ²` (`hΛ`), the scale is a fixed fraction of
the Planck acceleration, `a₀ = (1 − ln 2)√π/((ln 2)^{3/2} L) · √(c⁷/ℏG)`, and
`Λ = 12πc³/(L²ℏG ln 2)`.  The same formula with another value `G'` of Newton's constant gives twice
the scale only if `G' = G/4`.  Lean has no epochs: Sec. IX applies the formula at every epoch
with that epoch's `G`, since `L` and the split of a string's energy do not change and our units
fix `c` and `ℏ`. -/
theorem scale_over_time (G Λ : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (hΛ : Λ = 3 / R.RL ^ 2) :
    R.a0 = (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        Real.sqrt (R.c ^ 7 / (R.ℏ * G)) ∧
    Λ = 12 * R.pi * R.c ^ 3 / (R.L ^ 2 * R.ℏ * G * R.ln2) ∧
    ∀ G' : ℝ, 0 < G' →
      (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        Real.sqrt (R.c ^ 7 / (R.ℏ * G')) = 2 * R.a0 → G' = G / 4 := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hGpos : 0 < G := by rw [hG]; positivity
  have hsp : Real.sqrt R.pi ^ 2 = R.pi := Real.sq_sqrt R.pi_pos.le
  have hsl : Real.sqrt R.ln2 ^ 2 = R.ln2 := Real.sq_sqrt R.ln2_pos.le
  have hs0 : 0 < Real.sqrt R.pi := Real.sqrt_pos.mpr R.pi_pos
  have ht0 : 0 < Real.sqrt R.ln2 := Real.sqrt_pos.mpr R.ln2_pos
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  have hkey : R.c ^ 7 / (R.ℏ * G) =
      (Real.sqrt R.pi * Real.sqrt R.ln2 * R.c ^ 2 / R.ℓc) ^ 2 := by
    rw [hG, div_pow, mul_pow, mul_pow, hsp, hsl]
    field_simp
  have hsqrt : Real.sqrt (R.c ^ 7 / (R.ℏ * G)) =
      Real.sqrt R.pi * Real.sqrt R.ln2 * R.c ^ 2 / R.ℓc := by
    rw [hkey, Real.sqrt_sq (by positivity)]
  have ha0 : R.a0 = (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
      Real.sqrt (R.c ^ 7 / (R.ℏ * G)) := by
    rw [hsqrt]
    unfold a0 RL
    have e : (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) *
        (Real.sqrt R.pi * Real.sqrt R.ln2 * R.c ^ 2 / R.ℓc)
        = (1 - R.ln2) * (Real.sqrt R.pi ^ 2) * R.c ^ 2 / (R.ln2 * R.L * R.ℓc) := by
      field_simp
    rw [e, hsp]
    field_simp
  refine ⟨ha0, ?_, ?_⟩
  · rw [hΛ, hG]
    unfold RL
    field_simp
    ring
  · intro G' hG' h
    rw [ha0] at h
    have hK : 0 < (1 - R.ln2) * Real.sqrt R.pi / (R.ln2 * Real.sqrt R.ln2 * R.L) := by
      positivity
    have h2 : Real.sqrt (R.c ^ 7 / (R.ℏ * G')) = 2 * Real.sqrt (R.c ^ 7 / (R.ℏ * G)) := by
      have := h
      rw [mul_left_comm] at this
      exact mul_left_cancel₀ hK.ne' this
    have h3 : R.c ^ 7 / (R.ℏ * G') = 4 * (R.c ^ 7 / (R.ℏ * G)) := by
      have e1 := Real.sq_sqrt (show 0 ≤ R.c ^ 7 / (R.ℏ * G') by positivity)
      have e2 := Real.sq_sqrt (show 0 ≤ R.c ^ 7 / (R.ℏ * G) by positivity)
      rw [← e1, ← e2, h2]
      ring
    field_simp at h3
    have hc7 : 0 < R.c ^ 7 := by positivity
    nlinarith [h3, hc7, R.ℏ_pos, hG', hGpos, mul_pos hc7 R.ℏ_pos]

end Reg

namespace Law

/-- **Near the body** (Sec. VI).  With `x = e^{−h}`, `a/g_N − 1 = x/(1 − x)`, which exceeds `x`,
and `a − g_N(1 + x) = g_N x²/(1 − x)`: `a = g_N[1 + e^{−h} + O(e^{−2h})]`, so Newton's law returns
exponentially. -/
theorem near_limit (gN h : ℝ) (hgN : 0 < gN) (hh : 0 < h) :
    gN / (1 - Real.exp (-h)) - gN = gN * (Real.exp (-h) / (1 - Real.exp (-h))) ∧
    gN * Real.exp (-h) < gN / (1 - Real.exp (-h)) - gN ∧
    gN / (1 - Real.exp (-h)) - gN * (1 + Real.exp (-h)) =
      gN * Real.exp (-h) ^ 2 / (1 - Real.exp (-h)) := by
  have hx0 : 0 < Real.exp (-h) := Real.exp_pos _
  have hx1 := exp_neg_lt_one hh
  have h1x : 0 < 1 - Real.exp (-h) := by linarith
  have h1x' := h1x.ne'
  have e : gN / (1 - Real.exp (-h)) - gN = gN * (Real.exp (-h) / (1 - Real.exp (-h))) := by
    rw [mul_div_assoc', eq_div_iff h1x', sub_mul, div_mul_cancel₀ gN h1x']
    ring
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    apply mul_lt_mul_of_pos_left _ hgN
    rw [lt_div_iff₀ h1x]
    nlinarith [mul_pos hx0 hx0]
  · rw [eq_div_iff h1x', sub_mul, div_mul_cancel₀ gN h1x']
    ring

/-- **Far from the body**, Eq. (11).  With `g_N = a₀h²`, so that `√(a₀g_N) = a₀h` and
`g_N/2 = a₀h²/2`, and `0 < h ≤ 1/2`, the acceleration `a = a₀h²/(1 − e^{−h})` lies within
`a₀h³ = g_N^{3/2}/√a₀` of `√(a₀g_N) + g_N/2`: the deep law `a → √(a₀g_N)`, with the next term
`g_N/2`. -/
theorem deep_limit (a0 h : ℝ) (ha0 : 0 < a0) (hh : 0 < h) (hh2 : h ≤ 1 / 2) :
    a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3 ≤ a0 * h ^ 2 / (1 - Real.exp (-h)) ∧
    a0 * h ^ 2 / (1 - Real.exp (-h)) ≤ a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3 := by
  obtain ⟨t1, t2⟩ := exp_neg_taylor hh.le (by linarith)
  have hD : 0 < 1 - Real.exp (-h) := by linarith [exp_neg_lt_one hh]
  have hh4 : 0 < a0 * h ^ 4 := by positivity
  constructor
  · rw [le_div_iff₀ hD]
    have hc : 0 ≤ a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3 := by
      have : 0 ≤ 1 + h / 2 - h ^ 2 := by nlinarith
      have e : a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3 = a0 * h * (1 + h / 2 - h ^ 2) := by ring
      rw [e]; positivity
    have key : a0 * h ^ 2 - (a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3) *
        (h - h ^ 2 / 2 + 2 / 9 * h ^ 3) = a0 * h ^ 4 * (37 / 36 - 11 / 18 * h + 2 / 9 * h ^ 2) := by
      ring
    have hq : 0 < 37 / 36 - 11 / 18 * h + 2 / 9 * h ^ 2 := by nlinarith
    calc (a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3) * (1 - Real.exp (-h))
        ≤ (a0 * h + a0 * h ^ 2 / 2 - a0 * h ^ 3) * (h - h ^ 2 / 2 + 2 / 9 * h ^ 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ ≤ a0 * h ^ 2 := by nlinarith [mul_pos hh4 hq]
  · rw [div_le_iff₀ hD]
    have key : (a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3) * (h - h ^ 2 / 2 - 2 / 9 * h ^ 3) -
        a0 * h ^ 2 = a0 * h ^ 4 * (19 / 36 - 11 / 18 * h - 2 / 9 * h ^ 2) := by
      ring
    have hq : 0 < 19 / 36 - 11 / 18 * h - 2 / 9 * h ^ 2 := by nlinarith
    calc a0 * h ^ 2
        ≤ (a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3) * (h - h ^ 2 / 2 - 2 / 9 * h ^ 3) := by
          nlinarith [mul_pos hh4 hq]
      _ ≤ (a0 * h + a0 * h ^ 2 / 2 + a0 * h ^ 3) * (1 - Real.exp (-h)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **A classical share** (Sec. VIII).  If a string's share of the body were classical, the string
would hold a record of the body with the probability `f = g_N/a₀` (`hb`), in place of the
amplitude.  Far from the body, where `f ≤ 1`, the carriers would be the fraction `b = f`, and
`a = g_N/b = a₀`.  On a circular orbit `v² = ar = a₀r`, so rotation speeds would rise as `√r`.
Flat rotation curves therefore support Postulate 1. -/
theorem classical_limit (a0 gN a b r v : ℝ) (hgN : 0 < gN) (hb : b = gN / a0)
    (hab : a = gN / b) (hv : v ^ 2 = a * r) : a = a0 ∧ v ^ 2 = a0 * r := by
  have ha : a = a0 := by
    rw [hab, hb, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hgN.ne', mul_one]
  exact ⟨ha, by rw [hv, ha]⟩

/-- **The baryonic Tully–Fisher relation**, Eq. (12): in the deep regime, `a = √(a₀g_N)` with
`g_N = GM/r²`, a circular orbit, `v² = ar`, has `v⁴ = a₀GM` at every radius: the rotation curve is
flat. -/
theorem tully_fisher (a0 G M r v : ℝ) (ha0 : 0 < a0) (hG : 0 < G) (hM : 0 < M) (hr : 0 < r)
    (hv : v ^ 2 = Real.sqrt (a0 * (G * M / r ^ 2)) * r) : v ^ 4 = a0 * G * M := by
  have hr' := hr.ne'
  have e : v ^ 4 = (v ^ 2) ^ 2 := by ring
  rw [e, hv, mul_pow, Real.sq_sqrt (by positivity), mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero 2 hr')]
  ring

/-! ### Two bodies (Sec. VII) -/

/-- **Two bodies: the split** (Sec. VII).  Momentum is conserved (`hmom`; by Postulate 1 no law
depends on the global phase, so every law commutes with the shift of a ring, whose generator is
the momentum along it), so two bodies pull each other equally, with the force `F = M₁a₁` (`hF`).
Each body then accelerates at `F/M_i`, and the relative acceleration is `F(M₁ + M₂)/M₁M₂`. -/
theorem two_body_split (M₁ M₂ a₁ a₂ F : ℝ) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (hmom : M₁ * a₁ = M₂ * a₂) (hF : F = M₁ * a₁) :
    a₁ = F / M₁ ∧ a₂ = F / M₂ ∧ a₁ + a₂ = F * (M₁ + M₂) / (M₁ * M₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hF, eq_div_iff h₁.ne']
    ring
  · rw [hF, hmom, eq_div_iff h₂.ne']
    ring
  · rw [hF, eq_div_iff (mul_pos h₁ h₂).ne']
    linear_combination (-M₁ : ℝ) * hmom

/-- The algebra behind `two_body_deep`, with `u = √M₁`, `v = √(M₁ + M₂)`, `w = √M₂` and
`s = √(Ga₀)`: the bounds on `F/M₂` reduce to `(v − u)²(2v + u) ≥ 0` and
`(v − u)²(v + 2u) + 2w³ ≥ 0`. -/
lemma two_body_bounds (s u v w r : ℝ) (hs : 0 < s) (hr : 0 < r) (hu : 0 ≤ u) (hw : 0 < w)
    (huv : u ≤ v) (hw2 : w * w = v * v - u * u) :
    s * u / r - 2 / 3 * s * w / r ≤
      2 / 3 * s * (v * v * v - u * u * u - w * w * w) / r / (w * w) ∧
    2 / 3 * s * (v * v * v - u * u * u - w * w * w) / r / (w * w) ≤ s * v / r := by
  have hv : 0 ≤ v := le_trans hu huv
  have hw2' : 0 < w * w := mul_pos hw hw
  have hr' := hr.ne'
  have hw' := hw.ne'
  have h1 : 0 ≤ s * ((v - u) ^ 2 * (2 * v + u)) :=
    mul_nonneg hs.le (mul_nonneg (sq_nonneg _) (by linarith))
  have h2 : 0 ≤ s * ((v - u) ^ 2 * (v + 2 * u)) :=
    mul_nonneg hs.le (mul_nonneg (sq_nonneg _) (by linarith))
  have h3 : 0 ≤ s * (w * (v * v - u * u)) := by
    rw [← hw2]; positivity
  constructor
  · rw [div_div, le_div_iff₀ (mul_pos hr hw2')]
    have e : (s * u / r - 2 / 3 * s * w / r) * (r * (w * w)) =
        s * u * (w * w) - 2 / 3 * s * w * (w * w) := by
      field_simp
    rw [e, hw2]
    nlinarith [h1]
  · rw [div_div, div_le_iff₀ (mul_pos hr hw2')]
    have e : s * v / r * (r * (w * w)) = s * v * (w * w) := by
      field_simp
    rw [e, hw2]
    nlinarith [h2, h3]

/-- **Two bodies in the deep regime** (Sec. VII).  With the carrier fraction at a patch set by the
acceleration there (`Reg.share_reading`), the field equation `∇·(b∇Φ) = 4πGρ` is Bekenstein and
Milgrom's, which comes from an action and conserves momentum.  In the deep regime, where the law
is `a = √(a₀g_N)`, Milgrom's virial theorem gives the force between two bodies `M₁` and `M₂` at a
distance `r` (`hvir`): `rF = (2/3)√(Ga₀)[(M₁ + M₂)^{3/2} − M₁^{3/2} − M₂^{3/2}]`, Eq. (14).  Then
`F/M₂`, the acceleration of `M₂`, lies between `√(GM₁a₀)/r − (2/3)√(Ga₀M₂)/r` and
`√(G(M₁ + M₂)a₀)/r`, so it tends to a test body's `√(GM₁a₀)/r`, Eq. (11), as `M₂ → 0`. -/
theorem two_body_deep (G a0 M₁ M₂ r F : ℝ) (hG : 0 < G) (ha0 : 0 < a0) (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) (hr : 0 < r)
    (hvir : r * F = 2 / 3 * Real.sqrt (G * a0) *
      ((M₁ + M₂) * Real.sqrt (M₁ + M₂) - M₁ * Real.sqrt M₁ - M₂ * Real.sqrt M₂)) :
    Real.sqrt (G * M₁ * a0) / r - 2 / 3 * Real.sqrt (G * a0 * M₂) / r ≤ F / M₂ ∧
    F / M₂ ≤ Real.sqrt (G * (M₁ + M₂) * a0) / r := by
  have hGa : 0 ≤ G * a0 := (mul_pos hG ha0).le
  have hs : 0 < Real.sqrt (G * a0) := Real.sqrt_pos.mpr (mul_pos hG ha0)
  have hu : 0 ≤ Real.sqrt M₁ := Real.sqrt_nonneg _
  have hw : 0 < Real.sqrt M₂ := Real.sqrt_pos.mpr h₂
  have huv : Real.sqrt M₁ ≤ Real.sqrt (M₁ + M₂) := Real.sqrt_le_sqrt (by linarith)
  have huu : Real.sqrt M₁ * Real.sqrt M₁ = M₁ := Real.mul_self_sqrt h₁.le
  have hvv : Real.sqrt (M₁ + M₂) * Real.sqrt (M₁ + M₂) = M₁ + M₂ :=
    Real.mul_self_sqrt (add_pos h₁ h₂).le
  have hww : Real.sqrt M₂ * Real.sqrt M₂ = M₂ := Real.mul_self_sqrt h₂.le
  have hw2 : Real.sqrt M₂ * Real.sqrt M₂ =
      Real.sqrt (M₁ + M₂) * Real.sqrt (M₁ + M₂) - Real.sqrt M₁ * Real.sqrt M₁ := by
    rw [hww, hvv, huu]; ring
  have e1 : Real.sqrt (G * M₁ * a0) = Real.sqrt (G * a0) * Real.sqrt M₁ := by
    rw [← Real.sqrt_mul hGa]; congr 1; ring
  have e2 : 2 / 3 * Real.sqrt (G * a0 * M₂) / r = 2 / 3 * Real.sqrt (G * a0) * Real.sqrt M₂ / r := by
    rw [Real.sqrt_mul hGa]; ring
  have e3 : Real.sqrt (G * (M₁ + M₂) * a0) = Real.sqrt (G * a0) * Real.sqrt (M₁ + M₂) := by
    rw [← Real.sqrt_mul hGa]; congr 1; ring
  have hF : F / M₂ = 2 / 3 * Real.sqrt (G * a0) *
      (Real.sqrt (M₁ + M₂) * Real.sqrt (M₁ + M₂) * Real.sqrt (M₁ + M₂) -
        Real.sqrt M₁ * Real.sqrt M₁ * Real.sqrt M₁ - Real.sqrt M₂ * Real.sqrt M₂ * Real.sqrt M₂) /
      r / (Real.sqrt M₂ * Real.sqrt M₂) := by
    rw [hww, hvv, huu]
    have : F = 2 / 3 * Real.sqrt (G * a0) *
        ((M₁ + M₂) * Real.sqrt (M₁ + M₂) - M₁ * Real.sqrt M₁ - M₂ * Real.sqrt M₂) / r := by
      rw [eq_div_iff hr.ne', mul_comm F r, hvir]
    rw [this]
  rw [e1, e2, e3, hF]
  exact two_body_bounds (Real.sqrt (G * a0)) (Real.sqrt M₁) (Real.sqrt (M₁ + M₂)) (Real.sqrt M₂)
    r hs hr hu hw huv hw2

/-- **Two equal bodies in the deep regime** (Sec. VII): with `M₁ = M₂ = M`, Eq. (14) gives
`F = (4/3)(√2 − 1) M√(GMa₀)/r`. -/
theorem two_body_equal (G a0 M r F : ℝ) (hG : 0 < G) (ha0 : 0 < a0) (hr : 0 < r)
    (hvir : r * F = 2 / 3 * Real.sqrt (G * a0) *
      ((M + M) * Real.sqrt (M + M) - M * Real.sqrt M - M * Real.sqrt M)) :
    F = 4 / 3 * (Real.sqrt 2 - 1) * M * Real.sqrt (G * M * a0) / r := by
  have hGa : 0 ≤ G * a0 := (mul_pos hG ha0).le
  have e1 : Real.sqrt (M + M) = Real.sqrt 2 * Real.sqrt M := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have e2 : Real.sqrt (G * M * a0) = Real.sqrt (G * a0) * Real.sqrt M := by
    rw [← Real.sqrt_mul hGa]; congr 1; ring
  rw [eq_div_iff hr.ne', mul_comm F r, hvir, e1, e2]
  ring

end Law

end Register
