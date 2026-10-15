import RegisterRAR.Law
import RegisterRAR.DeSitter

/-!
# The radial acceleration relation from the claimed inputs, and nothing else

`radial_acceleration_relation` chains Secs. II–VI of *The Radial Acceleration Relation from the
Granularity of Hilbert Space* (v0-18) into one statement.  Its hypotheses
are exactly the inputs the paper claims, each named, and its conclusion is the law with the derived
scale.  Since `#print axioms` of it returns only the logical minimum of classical mathematics
(`Ledger.lean`), the proof uses nothing else: no physical axiom, and no assumption that is not
written in its statement.

The hypotheses, and the paper's name for each:

* `hJ` — thermodynamics, Jacobson: the Clausius relation on every local horizon, with the entropy
  per unit area that the count fixes, gives Einstein's equations with `G = c³k_B/4ℏη`.
* `hΛ`, `hGeo` — the closed geodesics of the solution without a mass, which the symmetry of space
  makes maximally symmetric, are circles of radius `√(3/Λ)`, and a largest ring has the length of
  these circles (Postulates 1–2; Sec. II excludes the quotients).
* `I1dS`, `I1N`, `I1a` — thermodynamics, the temperature of a horizon from its period: the
  cosmological horizon, whose period is a largest ring's lap, and the Unruh horizons of `g_N` and of
  `a`.
* `hDP` — Palmer's relation: the energy that goes with a qubit is `ℏ` over its reduction time.
* `hClock` — Postulate 1 with `L` the same for every qubit: a free string's reduction time is the
  lap of a largest ring, `Lt_c`.  With `I1dS` these give a string the energy `k_BT_dS`
  (`Reg.string_energy`); Planck's and DESI's `Ω_Λ` test the predicted vacuum share `ln 2`
  (`Numerics.vacuum_share`).
* `hME` — thermodynamics, maximum entropy, with Postulate 1's unit: the receiving cell's threshold
  has the survival function `e^{−x}`, exponential with mean one qubit.
* `hb` — Postulate 1, with Palmer's rule: a string that carries the body's information is one of
  its qubits, so the body's share at a string enters as the amplitude `√(E/u)`; a string carries
  that information when the amplitude exceeds the threshold of its receiving cell, the cell where
  it crosses the sphere, so the carriers are the fraction `b` of the strings whose threshold lies
  below it.
* `hcar`, `hNcar` — Postulate 1 with equipartition: the body's energy, with `M` all the mass
  inside the sphere, is held by the carriers alone, in equal shares (`Law.share_of_equipartition`
  gives this in finite form), and the carriers are the fraction `b` of the sphere's `N_s` strings.
* `hκ`, `hκN` — equipartition: a string's share is proportional to its temperature, `κT`, with
  one `κ` for every string.  The carriers are at the sphere's temperature `T_a` (`hκ`), and
  Newton's equal share, Eq. (5), is that of every string at the Unruh temperature of `g_N`
  (`hκN`).  With Eq. (3) this gives `κ = 2k_B ln 2`, two Landauer energies per string, and so
  Eq. (4).

`hypotheses_consistent` shows that the hypotheses can all hold at once, for every register, so that
the theorem does not hold vacuously.
-/

open Real

namespace Register
namespace Relation

/-- **The radial acceleration relation** (Secs. II–VI): from the inputs listed in the module
comment, the acceleration toward all the mass `M` inside a sphere of radius `r` is
`a = g_N/(1 − e^{−√(g_N/a₀)})`, with `g_N = GM/r²` and `a₀ = (1 − ln 2)c²/(2 ln 2 R_Λ)`,
`R_Λ = √(3/Λ)`; the body's energy is Newton's equal share, Eq. (3) at `g_N`; and a string's
share at the temperature `T` is two Landauer energies, `κT` with `κ = 2k_B ln 2`. -/
theorem radial_acceleration_relation (R : Reg)
    (G : ℝ) (hJ : G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η))
    (Λ : ℝ) (hΛ : 0 < Λ) (hGeo : R.L * R.ℓc = 2 * R.pi * Real.sqrt (3 / Λ))
    (TdS : ℝ) (I1dS : R.kB * TdS = R.ℏ / (R.L * R.tc))
    (τred εs : ℝ) (hDP : εs = R.ℏ / τred) (hClock : τred = R.L * R.tc)
    (M r : ℝ) (hM : 0 < M) (hr : 0 < r)
    (TN : ℝ) (I1N : R.kB * TN = R.ℏ / (R.La (G * M / r ^ 2) * R.tc))
    (a Ta : ℝ) (ha : 0 < a) (I1a : R.kB * Ta = R.ℏ / (R.La a * R.tc))
    (surv : ℝ → ℝ) (hME : ∀ x, 0 ≤ x → surv x = Real.exp (-x))
    (b : ℝ) (hb : b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))))
    (Ncar εc κ : ℝ) (hcar : M * R.c ^ 2 = Ncar * εc) (hNcar : Ncar = b * R.Ns r)
    (hκ : εc = κ * Ta) (hκN : M * R.c ^ 2 = R.Ns r * (κ * TN)) :
    a = (G * M / r ^ 2) / (1 - Real.exp (-Real.sqrt ((G * M / r ^ 2) / R.a0))) ∧
    R.a0 = (1 - R.ln2) * R.c ^ 2 / (2 * R.ln2 * Real.sqrt (3 / Λ)) ∧
    M * R.c ^ 2 = 2 * R.Ns r * (R.kB * TN * R.ln2) ∧ κ = 2 * R.kB * R.ln2 := by
  reg_facts R
  have hG := (R.G_eq G hJ).1
  have hG0 : 0 < G := by rw [hG]; positivity
  have hgN : 0 < G * M / r ^ 2 := by positivity
  -- Eq. (3) at `g_N`: Newton's equal share
  have hN := R.newton_share G M r TN hr hM hJ I1N
  have hNs : 0 < R.Ns r := by rw [R.Ns_eq r]; positivity
  -- equipartition with Eq. (3): a string's share is two Landauer energies at its temperature
  have hTN : 0 < R.kB * TN := by rw [R.T_Unruh _ TN hgN I1N]; positivity
  have hTN' : TN ≠ 0 := by
    intro h
    rw [h, mul_zero] at hTN
    exact lt_irrefl 0 hTN
  have hκv : κ = 2 * R.kB * R.ln2 := by
    have e : R.Ns r * (κ * TN) = R.Ns r * (2 * R.kB * R.ln2 * TN) := by
      rw [← hκN, hN]
      ring
    exact mul_right_cancel₀ hTN' (mul_left_cancel₀ hNs.ne' e)
  -- Eq. (4): the carriers alone hold the body's energy, two Landauer energies each
  have hK : M * R.c ^ 2 = 2 * (b * R.Ns r) * (R.kB * Ta * R.ln2) := by
    rw [hcar, hNcar, hκ, hκv]
    ring
  -- Sec. II: Palmer's relation, with the reduction time one lap, gives a string `k_BT_dS`
  have hεs : εs = R.kB * TdS := R.string_energy τred εs TdS hDP hClock I1dS
  -- Eqs. (5)–(7): the body's energy per string, in units of a string's matter, is `g_N/a₀`
  have hf := R.fill_fraction (G * M / r ^ 2) TN TdS εs hgN I1N I1dS hεs
  have ha0 := R.a0_pos
  have hh : 0 < Real.sqrt ((G * M / r ^ 2) / R.a0) := Real.sqrt_pos.2 (by positivity)
  -- Eq. (9): the carriers are the fraction `1 − e^{−h}`
  have hb' : b = 1 - Real.exp (-Real.sqrt ((G * M / r ^ 2) / R.a0)) := by
    rw [hb, hf, hME _ (Real.sqrt_nonneg _)]
  have hbpos : 0 < b := by rw [hb']; linarith [Law.exp_neg_lt_one hh]
  -- Eq. (4): `a = g_N/b`
  have hab := R.share_acceleration M (R.Ns r) b TN Ta (G * M / r ^ 2) a hNs hbpos hgN ha hN hK
    I1N I1a
  refine ⟨?_, ?_, hN, hκv⟩
  · rw [hab, hb']
  · unfold Reg.a0
    rw [(R.radius_from_geodesics G Λ hΛ hGeo).1]

/-- **The hypotheses are consistent** for every register: there are a `G`, a `Λ`, temperatures, a
body, a threshold and an acceleration that meet all of them at once, so that
`radial_acceleration_relation` does not hold vacuously.  (`Numerics.reg_jacobson` shows that the
measured `G` meets `hJ` for the register of the measured constants.) -/
theorem hypotheses_consistent (R : Reg) :
    ∃ (G Λ TdS τred εs TN a Ta b Ncar εc κ : ℝ) (surv : ℝ → ℝ),
      G = R.c ^ 3 * R.kB / (4 * R.ℏ * R.η) ∧ 0 < Λ ∧
      R.L * R.ℓc = 2 * R.pi * Real.sqrt (3 / Λ) ∧
      R.kB * TdS = R.ℏ / (R.L * R.tc) ∧ εs = R.ℏ / τred ∧ τred = R.L * R.tc ∧
      R.kB * TN = R.ℏ / (R.La (G * 1 / 1 ^ 2) * R.tc) ∧ 0 < a ∧
      R.kB * Ta = R.ℏ / (R.La a * R.tc) ∧ (∀ x, 0 ≤ x → surv x = Real.exp (-x)) ∧
      b = 1 - surv (Real.sqrt (2 * R.kB * TN * R.ln2 / ((1 - R.ln2) * εs))) ∧
      1 * R.c ^ 2 = Ncar * εc ∧ Ncar = b * R.Ns 1 ∧ εc = κ * Ta ∧
      1 * R.c ^ 2 = R.Ns 1 * (κ * TN) := by
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
  -- Eq. (3) at `g_N`, and the Unruh temperatures of `g_N` and of `a = g_N/b`
  have hN := R.newton_share G 1 1 TN one_pos one_pos hGdef I1N
  have h1 := R.T_Unruh _ TN hgN I1N
  have h2 := R.T_Unruh a Ta ha I1a
  have hb' := hbpos.ne'
  refine ⟨G, Λ, TdS, R.L * R.tc, R.kB * TdS, TN, a, Ta, b, b * R.Ns 1, 2 * R.kB * R.ln2 * Ta,
    2 * R.kB * R.ln2, fun x => Real.exp (-x), hGdef, hΛ, hGeo, I1dS, I1dS, rfl, I1N, ha, I1a,
    fun _ _ => rfl, hbdef, ?_, rfl, rfl, ?_⟩
  -- the carriers hold the body's energy, two Landauer energies each at `T_a = T_N/b`
  · show 1 * R.c ^ 2 = b * R.Ns 1 * (2 * R.kB * R.ln2 * Ta)
    rw [show b * R.Ns 1 * (2 * R.kB * R.ln2 * Ta) = 2 * (b * R.Ns 1) * (R.kB * Ta * R.ln2) by
      ring]
    rw [hN, h1, h2, hadef]
    field_simp
  -- Newton's equal share, two Landauer energies per string at `T_N`
  · show 1 * R.c ^ 2 = R.Ns 1 * (2 * R.kB * R.ln2 * TN)
    rw [hN]
    ring

end Relation
end Register
