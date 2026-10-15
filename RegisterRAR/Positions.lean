import RegisterRAR.Horizon
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The horizon counts every largest ring (Sec. II)

Formal counterpart of the paragraph of Sec. II of *The Radial Acceleration Relation from the Granularity of Hilbert Space*
(v0-18) that begins "Postulate 2 gives every cell a distance from the observer's cell".  The largest
rings carry their cyclic order: each ring's cells sit at the positions `0, …, L − 1` of `ZMod L`,
one step per cell (Postulate 1: the shift moves a bit to the next cell), and the opposite of a cell
lies halfway round, `L/2` steps on (Postulate 2).  Postulate 2 then gives every cell not opposite
the observer's cell `B` a distance from it: the number of steps along the one largest ring through
both, the shorter way round.

What is proved, for `L ≥ 4`:

* `dist_opp`: the two cells of an opposite pair lie at the distances `d` and `L/2 − d`;
* `horizon_weight_ring`: every largest ring has half its cells, `L/2` of them, inside the horizon
  `L/4` cells out, counting a cell on it as half; so the horizon counts every largest ring;
* `card_dist_eq`: at each distance `d` with `1 ≤ d < L/2` there are exactly `L` cells.

The horizon's distance `L/4` is a quarter of a largest ring: the de Sitter solution puts the
horizon at the proper distance `πR_Λ/2 = Lℓ_c/4` (`Reg.proper_distance` in `DeSitter.lean`).  The
positions also give the paper's reason that `L` is even, the opposite lying halfway round
(`even_of_halfway`).

The declarations are those of `RouteB.lean` in RegisterGravity v11.2 without its last three
theorems (`sphere_count`, `per_distance_count`, `route_B_fraction`), which concern a share the
present paper does not use; they sit in the namespace `Register`.
-/

namespace Register

open Finset

namespace Horizon

variable {L : ℕ} (H : Horizon L)

include H in
/-- `L` is even (`Horizon.even_L`): write it `2h`. -/
lemma exists_half (hL : 4 ≤ L) : ∃ h, L = 2 * h ∧ L / 2 = h := by
  obtain ⟨h, hh⟩ := H.even_L hL
  exact ⟨h, by omega, by omega⟩

/-- Any two cells lie on a common largest ring (for opposite cells, any ring through one). -/
lemma exists_loop_through (hL : 4 ≤ L) (B X : H.Cell) : ∃ l, B ∈ H.cells l ∧ X ∈ H.cells l := by
  by_cases h1 : X = B
  · subst h1
    obtain ⟨l₁, -, -⟩ := H.two_loops
    -- a ring through `X`: join `X` to a cell of `l₁` outside its pair
    obtain ⟨y, -, hyX, hyX'⟩ := H.exists_mem_notMem_pair hL l₁ X (H.opp X)
    obtain ⟨l, hXl, -⟩ := H.exists_loop X y hyX hyX'
    exact ⟨l, hXl, hXl⟩
  · by_cases h2 : X = H.opp B
    · subst h2
      obtain ⟨l₁, -, -⟩ := H.two_loops
      obtain ⟨y, -, hyB, hyB'⟩ := H.exists_mem_notMem_pair hL l₁ B (H.opp B)
      obtain ⟨l, hBl, -⟩ := H.exists_loop B y hyB hyB'
      exact ⟨l, hBl, H.opp_mem l B hBl⟩
    · exact H.exists_loop B X h1 h2

/-- **The cyclic order of the largest rings.**  Each ring's cells carry positions in `ZMod L`,
distinct on the ring (Postulate 1: the shift moves a bit to the next cell), and the opposite of a
cell lies `L/2` steps on (Postulate 2: the cell halfway around every largest ring through it). -/
structure Positions (H : Horizon L) where
  /-- the position of a cell on a largest ring through it -/
  pos : H.Loop → H.Cell → ZMod L
  /-- distinct cells of a ring sit at distinct positions -/
  pos_inj : ∀ l x y, x ∈ H.cells l → y ∈ H.cells l → pos l x = pos l y → x = y
  /-- the opposite lies halfway round -/
  pos_opp : ∀ l x, x ∈ H.cells l → pos l (H.opp x) = pos l x + ((L / 2 : ℕ) : ZMod L)

namespace Positions

variable {H} (P : H.Positions)

/-- the steps from `x` to `y` along the ring `l`, in the direction of the shift -/
def offset (l : H.Loop) (x y : H.Cell) : ℕ := (P.pos l y - P.pos l x).val

/-- the ring distance: the steps from `x` to `y` along `l`, the shorter way round -/
def ringDist (l : H.Loop) (x y : H.Cell) : ℕ := min (P.offset l x y) (L - P.offset l x y)

/-- **The distance of a cell from the body's cell `B`** (Postulate 2): along the one largest ring
through both; `0` for `B` itself and `L/2` for its opposite. -/
noncomputable def dist (B X : H.Cell) : ℕ :=
  if hB : X = B then 0 else if hB' : X = H.opp B then L / 2 else
    P.ringDist (Classical.choose (H.exists_loop B X hB hB')) B X

lemma ringDist_self (l : H.Loop) (x : H.Cell) : P.ringDist l x x = 0 := by
  simp [ringDist, offset]

/-- `L/2` as an element of `ZMod L` has value `L/2`. -/
lemma val_half (hL : 4 ≤ L) : ((L / 2 : ℕ) : ZMod L).val = L / 2 :=
  ZMod.val_cast_of_lt (by omega)

lemma dist_self (B : H.Cell) : P.dist B B = 0 := by simp [dist]

include P in
/-- **`L` is even** (Sec. II): an opposite lies halfway around a ring of `L` cells.  The opposite
of a cell lies `L/2` steps on, and the opposite of the opposite is the cell itself, so `2(L/2)`
steps bring a cell back to itself, which for `L ≥ 2` needs `2(L/2) = L`. -/
theorem even_of_halfway (hL : 2 ≤ L) (l : H.Loop) (x : H.Cell) (hx : x ∈ H.cells l) :
    Even L := by
  have h1 := P.pos_opp l (H.opp x) (H.opp_mem l x hx)
  rw [H.opp_opp, P.pos_opp l x hx] at h1
  -- `h1 : pos x = pos x + L/2 + L/2` in `ZMod L`
  have h2 : ((2 * (L / 2) : ℕ) : ZMod L) = 0 := by
    push_cast
    linear_combination (-1 : ZMod L) * h1
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h2
  have hle := Nat.mul_div_le L 2
  have hk' : 2 * (L / 2) = L := by
    rcases k with _ | _ | k
    · omega
    · omega
    · exfalso
      nlinarith
  exact ⟨L / 2, by omega⟩

/-- The arithmetic of the opposite: moving on by `L/2` turns the ring distance `d` into `L/2 − d`. -/
lemma half_shift (k h : ℕ) (hk : k < 2 * h) :
    min ((k + h) % (2 * h)) (2 * h - (k + h) % (2 * h)) = h - min k (2 * h - k) := by
  by_cases hkh : k < h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

variable [NeZero L]

lemma offset_lt (l : H.Loop) (x y : H.Cell) : P.offset l x y < L := ZMod.val_lt _

lemma ringDist_le (l : H.Loop) (x y : H.Cell) : P.ringDist l x y ≤ L / 2 := by
  have := P.offset_lt l x y
  unfold ringDist
  omega

/-- The ring distance from `x` to the opposite of `y` is `L/2` less the ring distance to `y`. -/
lemma ringDist_opp (hL : 4 ≤ L) (l : H.Loop) (x y : H.Cell) (hy : y ∈ H.cells l) :
    P.ringDist l x (H.opp y) = L / 2 - P.ringDist l x y := by
  obtain ⟨h, hL2, hh⟩ := H.exists_half hL
  have hoff : P.offset l x (H.opp y) = (P.offset l x y + h) % L := by
    unfold offset
    rw [P.pos_opp l y hy]
    have e : P.pos l y + ((L / 2 : ℕ) : ZMod L) - P.pos l x
        = (P.pos l y - P.pos l x) + ((L / 2 : ℕ) : ZMod L) := by ring
    rw [e, ZMod.val_add, val_half hL, hh]
  have hk := P.offset_lt l x y
  have key := half_shift (P.offset l x y) h (by omega)
  rw [← hL2] at key
  unfold ringDist
  rw [hoff, hh]
  exact key

/-- On a ring through `B`, the opposite of `B` is `L/2` steps away. -/
lemma ringDist_opp_self (hL : 4 ≤ L) (l : H.Loop) (B : H.Cell) (hB : B ∈ H.cells l) :
    P.ringDist l B (H.opp B) = L / 2 := by
  rw [P.ringDist_opp hL l B B hB, P.ringDist_self]
  simp

/-- **The distance is read along any largest ring through both cells.** -/
lemma dist_eq (hL : 4 ≤ L) {l : H.Loop} {B X : H.Cell} (hB : B ∈ H.cells l)
    (hX : X ∈ H.cells l) : P.dist B X = P.ringDist l B X := by
  unfold dist
  by_cases h1 : X = B
  · subst h1; simp [P.ringDist_self]
  · by_cases h2 : X = H.opp B
    · subst h2; simp [h1, P.ringDist_opp_self hL l B hB]
    · simp only [h1, h2, dite_false]
      have hs := Classical.choose_spec (H.exists_loop B X h1 h2)
      have : Classical.choose (H.exists_loop B X h1 h2) = l :=
        H.unique_loop B X _ l h1 h2 hs.1 hs.2 hB hX
      rw [this]

lemma dist_le (hL : 4 ≤ L) (B X : H.Cell) : P.dist B X ≤ L / 2 := by
  obtain ⟨l, hB, hX⟩ := H.exists_loop_through hL B X
  rw [P.dist_eq hL hB hX]
  exact P.ringDist_le l B X

/-- **The two cells of an opposite pair lie at the distances `d` and `L/2 − d`.** -/
theorem dist_opp (hL : 4 ≤ L) (B X : H.Cell) : P.dist B (H.opp X) = L / 2 - P.dist B X := by
  obtain ⟨l, hB, hX⟩ := H.exists_loop_through hL B X
  rw [P.dist_eq hL hB (H.opp_mem l X hX), P.dist_eq hL hB hX, P.ringDist_opp hL l B X hX]

/-- Only `B` is at distance `0`. -/
lemma dist_eq_zero (hL : 4 ≤ L) {B X : H.Cell} (h : P.dist B X = 0) : X = B := by
  by_contra hXB
  obtain ⟨l, hB, hX⟩ := H.exists_loop_through hL B X
  rw [P.dist_eq hL hB hX] at h
  have hne : P.pos l X - P.pos l B ≠ 0 := by
    intro h0
    exact hXB (P.pos_inj l X B hX hB (sub_eq_zero.1 h0))
  have hv : P.offset l B X ≠ 0 := by
    unfold offset
    intro hv
    exact hne ((ZMod.val_eq_zero _).1 hv)
  have := P.offset_lt l B X
  unfold ringDist at h
  omega


/-! ### The count at each distance -/

omit [NeZero L] in
/-- The ring distance as a function of the position difference. -/
lemma ringDist_eq_val (l : H.Loop) (B X : H.Cell) :
    P.ringDist l B X = min (P.pos l X - P.pos l B).val (L - (P.pos l X - P.pos l B).val) := rfl

/-- **Two cells at each distance on a ring.**  On a largest ring through `B`, exactly two cells
lie at each distance `d` with `1 ≤ d < L/2`: one each way round. -/
theorem card_ringDist (l : H.Loop) (B : H.Cell) {d : ℕ} (hd1 : 1 ≤ d) (hd2 : 2 * d < L) :
    ((H.cells l).filter (fun X => P.ringDist l B X = d)).card = 2 := by
  classical
  set φ : H.Cell → ZMod L := fun X => P.pos l X - P.pos l B with hφ
  have hinj : Set.InjOn φ (H.cells l) := by
    intro x hx y hy hxy
    simp only [hφ, sub_left_inj] at hxy
    exact P.pos_inj l x y hx hy hxy
  -- the positions of the ring's cells fill `ZMod L`
  have himage : (H.cells l).image φ = univ := by
    apply Finset.eq_univ_of_card
    rw [card_image_of_injOn hinj, H.card_cells, ZMod.card]
  set q : ZMod L → Prop := fun z => min z.val (L - z.val) = d with hq
  have hfilt : (H.cells l).filter (fun X => P.ringDist l B X = d)
      = (H.cells l).filter (fun X => q (φ X)) :=
    Finset.filter_congr (fun X _ => Iff.rfl)
  have hcard : ((H.cells l).filter (fun X => q (φ X))).card = (univ.filter q).card := by
    rw [← himage, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]
  rw [hfilt, hcard]
  -- the positions at distance `d` are `d` and `L − d`
  have hdL : d < L := by omega
  have hLd : L - d < L := by omega
  have hq' : univ.filter q = {((d : ℕ) : ZMod L), ((L - d : ℕ) : ZMod L)} := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hq]
    have hz := ZMod.val_lt z
    constructor
    · intro h
      by_cases h1 : z.val ≤ L - z.val
      · left
        rw [← ZMod.natCast_zmod_val z]
        congr 1
        omega
      · right
        rw [← ZMod.natCast_zmod_val z]
        congr 1
        omega
    · rintro (rfl | rfl)
      · rw [ZMod.val_cast_of_lt hdL]; omega
      · rw [ZMod.val_cast_of_lt hLd]; omega
  rw [hq', card_pair]
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt hdL, ZMod.val_cast_of_lt hLd] at this
  omega

/-- **`L` cells at each distance** (Sec. II): at each distance `d` from `B` with `1 ≤ d < L/2`
there are exactly `L` cells, two on each of the `L/2` rings through `B`. -/
theorem card_dist_eq (hL : 4 ≤ L) (B : H.Cell) {d : ℕ} (hd1 : 1 ≤ d) (hd2 : 2 * d < L) :
    (univ.filter (fun X => P.dist B X = d)).card = L := by
  classical
  obtain ⟨h, hL2, hh⟩ := H.exists_half hL
  have hsplit : univ.filter (fun X => P.dist B X = d)
      = (H.through B).biUnion (fun l => (H.cells l).filter (fun X => P.ringDist l B X = d)) := by
    ext X
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_through]
    constructor
    · intro hX
      obtain ⟨l, hBl, hXl⟩ := H.exists_loop_through hL B X
      exact ⟨l, hBl, hXl, by rw [← P.dist_eq hL hBl hXl]; exact hX⟩
    · rintro ⟨l, hBl, hXl, hd⟩
      rw [P.dist_eq hL hBl hXl]; exact hd
  have hdisj : ((H.through B : Finset H.Loop) : Set H.Loop).PairwiseDisjoint
      (fun l => (H.cells l).filter (fun X => P.ringDist l B X = d)) := by
    intro l₁ hl₁ l₂ hl₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro X hX₁ hX₂
    rw [mem_filter] at hX₁ hX₂
    have hB₁ : B ∈ H.cells l₁ := (H.mem_through).1 (mem_coe.1 hl₁)
    have hB₂ : B ∈ H.cells l₂ := (H.mem_through).1 (mem_coe.1 hl₂)
    have hXB : X ≠ B := by
      rintro rfl; have h1 := hX₁.2; rw [P.ringDist_self] at h1; omega
    have hXB' : X ≠ H.opp B := by
      rintro rfl; have h1 := hX₁.2; rw [P.ringDist_opp_self hL l₁ B hB₁] at h1; omega
    exact hne (H.unique_loop B X l₁ l₂ hXB hXB' hB₁ hX₁.1 hB₂ hX₂.1)
  rw [hsplit, card_biUnion hdisj]
  have hc : ∀ l ∈ H.through B,
      ((H.cells l).filter (fun X => P.ringDist l B X = d)).card = 2 :=
    fun l _ => P.card_ringDist l B hd1 hd2
  rw [sum_congr rfl hc, sum_const, smul_eq_mul]
  have := H.two_mul_card_through hL B
  omega

/-- The cells within distance `n` of `B`: `B` itself and `L` at each distance `1, …, n`. -/
theorem card_dist_le (hL : 4 ≤ L) (B : H.Cell) (n : ℕ) (hn : 2 * n < L) :
    (univ.filter (fun X => P.dist B X ≤ n)).card = 1 + n * L := by
  classical
  induction n with
  | zero =>
    have : univ.filter (fun X => P.dist B X ≤ 0) = {B} := by
      ext X
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Nat.le_zero]
      exact ⟨P.dist_eq_zero hL, fun h => h ▸ P.dist_self B⟩
    rw [this, card_singleton]; ring
  | succ k ih =>
    have hsplit : univ.filter (fun X => P.dist B X ≤ k + 1)
        = univ.filter (fun X => P.dist B X ≤ k) ∪ univ.filter (fun X => P.dist B X = k + 1) := by
      ext X; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
    have hdisj : Disjoint (univ.filter (fun X => P.dist B X ≤ k))
        (univ.filter (fun X => P.dist B X = k + 1)) := by
      rw [Finset.disjoint_filter]; intro X _ h1 h2; omega
    rw [hsplit, card_union_of_disjoint hdisj, ih (by omega),
      P.card_dist_eq hL B (by omega) (by omega)]
    ring

/-! ### The horizon, a quarter lap out -/

/-- the share of a cell inside the horizon, `L/4` cells from the body: `1` inside, `1/2` on it,
`0` beyond -/
noncomputable def weight (d : ℕ) : ℝ := if 4 * d < L then 1 else if 4 * d = L then 1 / 2 else 0

omit [NeZero L] in
/-- The cells of an opposite pair share the inside of the horizon: `w(d) + w(L/2 − d) = 1`, with
`L = 2h`. -/
lemma weight_pair {h : ℕ} (hL2 : L = 2 * h) {d : ℕ} (hd : d ≤ h) :
    weight (L := L) d + weight (L := L) (h - d) = 1 := by
  unfold weight
  by_cases h1 : 4 * d < L
  · have h2 : ¬ 4 * (h - d) < L := by omega
    have h3 : ¬ 4 * (h - d) = L := by omega
    simp [h1, h2, h3]
  · by_cases h4 : 4 * d = L
    · have h2 : ¬ 4 * (h - d) < L := by omega
      have h3 : 4 * (h - d) = L := by omega
      simp [h4, h3]; norm_num
    · have h2 : 4 * (h - d) < L := by omega
      simp [h1, h4, h2]

/-- **Half of every ring lies inside the horizon** (Sec. II): the cells of a largest ring come in
`L/2` opposite pairs at the distances `d` and `L/2 − d`, one on each side of the horizon or both on
it, so the ring has `L/2` cells inside, counting a cell on the horizon as half. -/
theorem horizon_weight_ring (hL : 4 ≤ L) (B : H.Cell) (l : H.Loop) :
    ∑ X ∈ H.cells l, weight (L := L) (P.dist B X) = (L : ℝ) / 2 := by
  classical
  set f : H.Cell → ℝ := fun X => weight (L := L) (P.dist B X) with hf
  have hswap : ∑ X ∈ H.cells l, f (H.opp X) = ∑ X ∈ H.cells l, f X := by
    apply sum_nbij' H.opp H.opp
    · intro X hX; exact H.opp_mem l X hX
    · intro X hX; exact H.opp_mem l X hX
    · intro X _; exact H.opp_opp X
    · intro X _; exact H.opp_opp X
    · intro X _; rfl
  obtain ⟨h, hL2, hh⟩ := H.exists_half hL
  have hpair : ∀ X ∈ H.cells l, f X + f (H.opp X) = 1 := by
    intro X _
    simp only [hf]
    rw [P.dist_opp hL B X, hh]
    have := P.dist_le hL B X
    rw [hh] at this
    exact weight_pair hL2 this
  have htwo : 2 * ∑ X ∈ H.cells l, f X = L := by
    calc 2 * ∑ X ∈ H.cells l, f X = ∑ X ∈ H.cells l, f X + ∑ X ∈ H.cells l, f (H.opp X) := by
          rw [hswap]; ring
      _ = ∑ X ∈ H.cells l, (f X + f (H.opp X)) := by rw [sum_add_distrib]
      _ = ∑ X ∈ H.cells l, (1 : ℝ) := sum_congr rfl hpair
      _ = L := by rw [sum_const, H.card_cells, nsmul_eq_mul, mul_one]
  linarith

end Positions

end Horizon

end Register
