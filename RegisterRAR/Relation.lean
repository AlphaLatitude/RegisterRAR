import RegisterRAR.Law
import RegisterRAR.DeSitter

/-!
# The radial acceleration relation from the claimed inputs, and nothing else

`radial_acceleration_relation` chains Secs. II–VI of *The Radial Acceleration Relation from the
Granularity of Hilbert Space* (v0-13) into one statement.  Its hypotheses
are exactly the inputs the paper claims, each named, and its conclusion is the law with the derived
scale.  Since `#print axioms` of it returns only the logical minimum of classical mathematics
(`Ledger.lean`), the proof uses nothing else: no physical axiom, and no assumption that is not
written in its statement.

The hypotheses, and the paper's name for each:

* `hJ` — thermodynamics, Jacobson: the Clausius relation on every local horizon, with the entropy
  per unit area that the count fixes, gives Einstein's equations with `G = c³k_B/4ℏη`.
* `hΛ`, `hGeo` — the closed geodesics of the solution without a mass, which the symmetry of space
  makes maximally symmetric, are circles of radius `√(3/Λ)`, and the largest rings are these circles
  (Postulates 1–2).
* `I1dS`, `I1N`, `I1a` — thermodynamics, the temperature of a horizon from its period: the
  cosmological horizon, whose period is a largest ring's lap, and the Unruh horizons of `g_N` and of
  `a`.
* `hεs` — taken, with Planck's `Ω_Λ` (`Numerics.string_energy_check`): a string's energy is one
  horizon thermal energy, `k_BT_dS`.
* `hME` — thermodynamics, maximum entropy, with Postulate 1's unit: a string's tolerance has the
  survival function `e^{−x}`, exponential with mean one qubit.
* `hb` — Postulate 1, with Palmer's rule: a string that carries the body is one of its qubits, so
  the body's share at a string enters as the amplitude `√(E/u)`; a string carries the body when
  that amplitude exceeds the string's tolerance, so the carriers are the fraction `b` of the
  strings whose tolerance lies below it.
* `hK` — the Komar energy of the static sphere, held by the carriers at two Landauer energies each
  (Postulate 1 with equipartition, `Law.share_of_equipartition`).

`hypotheses_consistent` shows that the hypotheses can all hold at once, for every register, so that
the theorem does not hold vacuously.
-/

open Real

namespace Register
namespace Relation

/-- **The radial acceleration relation** (Secs. II–VI): from the inputs listed in the module
comment, the acceleration toward a body of mass `M` at radius `r` is
`a = g_N/(1 − e^{−√(g_N/a₀)})`, with `g_N = GM/r²` and `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`,
`R_Λ = √(3/Λ)`; and the body's energy is Newton's equal share, Eq. (3) at `g_N`. -/
theorem radial_acceleration_relation (R : Reg)
    (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (Λ : ℝ) (hΛ : 0 < Λ) (hGeo : R.L * R.ℓc = 2 * R.pi * Real.sqrt (3 / Λ))
    (TdS : ℝ) (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (εs : ℝ) (hεs : εs = R.kB * TdS)
    (M r : ℝ) (hM : 0 < M) (hr : 0 < r)
    (TN : ℝ) (I1N : R.kB * TN = R.ℏ / (R.La (G * M / r ^ 2) * R.tc))
    (a Ta : ℝ) (ha : 0 < a) (I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc))
    (surv : ℝ → ℝ) (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x))
    (b : ℝ) (hb : b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))))
    (hK : M * R.c ^ 2 = 2 * (b * R.Ns r) * (R.kB * Ta * R.ln2)) :
    a = (G * M / r ^ 2) / (1 - Real.exp (-Real.sqrt ((G * M / r ^ 2) / R.a0))) ∧
    R.a0 = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * Real.sqrt (3 / Λ)) ∧
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * TN * R.ln2) := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  -- Eq. (3) at `g_N`: Newton's equal share
  have hN := R.newton_share G M r TN hr hM hJ I1N
  -- Eqs. (5)–(7): the body's energy per string, in units of a string's matter, is `g_N/a₀`
  have hf := R.fill_fraction (G * M / r ^ 2) TN TdS εs hgN I1N I1dS hεs
  have ha0 := R.a0_pos
  have hh : 0 < Real.sqrt ((G * M / r ^ 2) / R.a0) := Real.sqrt_pos.2 (by positivity)
  -- Eq. (9): the carriers are the fraction `1 − e^{−h}`
  have hb' : b = 1 - Real.exp (-Real.sqrt ((G * M / r ^ 2) / R.a0)) := by
    rw [hb, hf, hME _ (Real.sqrt_nonneg _)]
  have hbpos : 0 < b := by rw [hb']; linarith [Law.exp_neg_lt_one hh]
  have hNs : 0 < R.Ns r := by rw [R.Ns_eq r]; positivity
  -- Eq. (4): `a = g_N/b`
  have hab := R.share_acceleration M (R.Ns r) b TN Ta (G * M / r ^ 2) a hNs hbpos hgN ha hN hK
    I1N I1a
  refine ⟨?_, ?_, hN⟩
  · rw [hab, hb']
  · unfold Reg.a0
    rw [(R.radius_from_geodesics G Λ hΛ hGeo).1]

/-- **The hypotheses are consistent** for every register: there are a `G`, a `Λ`, temperatures, a
body, a tolerance and an acceleration that meet all of them at once, so that
`radial_acceleration_relation` does not hold vacuously.  (`Numerics.reg_jacobson` shows that the
measured `G` meets `hJ` for the register of the measured constants.) -/
theorem hypotheses_consistent (R : Reg) :
    ∃ (G Λ TdS εs TN a Ta b : ℝ) (surv : ℝ → ℝ),
      G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧ 0 < Λ ∧
      R.L * R.ℓc = 2 * R.pi * Real.sqrt (3 / Λ) ∧
      R.kB * TdS = R.ℏ / (R.L * R.tc) ∧ εs = R.kB * TdS ∧
      R.kB * TN = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) ∧ 0 < a ∧
      R.kB * Ta = R.ℏ / (R.La a * R.tc) ∧ (∀ x, 0 ≤ x → surv x = Real.exp (-x)) ∧
      b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))) ∧
      1 * R.c ^ 2 = 2 * (b * R.Ns 1) * (R.kB * Ta * R.ln2) := by
  reg_facts R
  have hRL := R.RL_pos
  have hRL' := hRL.ne'
  have htc : 0 < R.tc := by unfold Reg.tc; positivity
  have htc' := htc.ne'
  have hm : 0 < 1 - R.ln2 := by linarith [R.ln2_lt_one]
  -- Jacobson's `G`
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) := ⟨_, rfl⟩
  have hG := (R.G_eq G hGdef).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * 1 / 1 ^ 2 := by positivity
  -- the `Λ` whose closed geodesics are the largest rings
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = 3 / R.RL ^ 2 := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by rw [hΛdef]; positivity
  have hGeo : R.L * R.ℓc = 2 * R.pi * Real.sqrt (3 / Λ) := by
    have e : 3 / Λ = R.RL ^ 2 := by rw [hΛdef]; field_simp
    rw [e, Real.sqrt_sq hRL.le]
    unfold Reg.RL
    field_simp
  -- the temperatures, as `I1` gives them
  obtain ⟨TdS, hTdS⟩ : ∃ T : ℝ, T = R.ℏ / (R.L * R.tc) / R.kB := ⟨_, rfl⟩
  have I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc) := by rw [hTdS]; field_simp
  have hεs0 : 0 < R.kB * TdS := by rw [I1dS]; positivity
  obtain ⟨TN, hTN⟩ : ∃ T : ℝ, T = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) / R.kB := ⟨_, rfl⟩
  have hLa : 0 < R.La (G * 1 / 1 ^ 2) := by unfold Reg.La; positivity
  have hLa' := hLa.ne'
  have I1N : R.kB * TN = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) := by rw [hTN]; field_simp
  have hTN0 : 0 < R.kB * TN := by rw [I1N]; positivity
  -- the carriers, and the acceleration `g_N/b`
  have harg : 0 < 2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * (R.kB * TdS)) := by
    rw [show 2 * R.kB * TN * R.ln2 = 2 * (R.kB * TN) * R.ln2 by ring]
    exact div_pos (by positivity) (mul_pos hm hεs0)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ,
      b = 1 - Real.exp (-Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * (R.kB * TdS)))) :=
    ⟨_, rfl⟩
  have hbpos : 0 < b := by rw [hbdef]; linarith [Law.exp_neg_lt_one (Real.sqrt_pos.2 harg)]
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = G * 1 / 1 ^ 2 / b := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; positivity
  obtain ⟨Ta, hTa⟩ : ∃ T : ℝ, T = R.ℏ / (R.La a * R.tc) / R.kB := ⟨_, rfl⟩
  have hLaa : 0 < R.La a := by unfold Reg.La; positivity
  have hLaa' := hLaa.ne'
  have I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc) := by rw [hTa]; field_simp
  refine ⟨G, Λ, TdS, R.kB * TdS, TN, a, Ta, b, fun x => Real.exp (-x), hGdef, hΛ, hGeo, I1dS,
    rfl, I1N, ha, I1a, fun _ _ => rfl, hbdef, ?_⟩
  -- the Komar energy held by the carriers: Eq. (3) at `g_N`, with `T_a = T_N/b`
  have hN := R.newton_share G 1 1 TN one_pos one_pos hGdef I1N
  have h1 := R.T_Unruh _ TN hgN I1N
  have h2 := R.T_Unruh a Ta ha I1a
  have hb' := hbpos.ne'
  rw [hN, h1, h2, hadef]
  field_simp

end Relation
end Register
