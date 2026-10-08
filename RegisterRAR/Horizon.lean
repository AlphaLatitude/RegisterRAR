import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# The count of the register (Sec. II)

Formal counterpart of the paragraph of Sec. II of *The Radial Acceleration Relation from the Granularity of Hilbert Space*
(v0-13) that begins "Postulate 2 fixes how many largest rings there are":

  ρ = L/2 largest rings through every cell,
  C = 2 + ρ(L − 2) = L²/2 − L + 2 cells,
  R = Cρ/L = L²/4 − L/2 + 1 largest rings,
  C = 2R.

The declarations are those of `Horizon.lean` in RegisterGravity v11.2, unchanged except that they
sit in the namespace `Register`.

## What is assumed

`Horizon L` packages exactly what the argument uses:

* Postulate 2, first clause: every cell `x` has one opposite `opp x` (an involution without fixed
  points), and the opposite lies on every largest ring through `x` (`opp_mem`).
* Postulate 2, second clause: two cells that are not opposite lie on exactly one largest ring
  (`exists_loop`, `unique_loop`).
* Postulate 2, third clause: any two largest rings share a cell (`loops_meet`).
* Every largest ring has `L` cells (`card_cells`), and, by the last clause of Postulate 2, no ring
  holds every cell, so the register has more than one largest ring (`two_loops`).

The theorems below need `4 ≤ L` (a largest ring has at least two opposite pairs).  Nothing else is
assumed: no metric, no area, no Bekenstein–Hawking.  The proof follows the paper: a largest ring
`E` that misses a cell `P` (`exists_loop_not_mem`, by the paper's construction), then `ρ = L/2` by
counting the pairs of `E` (`two_mul_card_through`), then `C` and `R` (`counts`).  That `L` is even
follows here from `ρ = L/2` (`even_L`), and in `Positions.lean` from the opposite lying halfway
round (`Positions.even_of_halfway`), which is the paper's reason.
-/

namespace Register

open Finset

/-- The horizon of the register: a finite set of cells with an opposite map, and the largest
rings (`Loop`s) of `L` cells on it. -/
structure Horizon (L : ℕ) where
  /-- the cells of the horizon -/
  Cell : Type
  /-- the largest rings on the horizon -/
  Loop : Type
  [fintypeCell : Fintype Cell]
  [fintypeLoop : Fintype Loop]
  [decEqCell : DecidableEq Cell]
  [decEqLoop : DecidableEq Loop]
  /-- the opposite of a cell -/
  opp : Cell → Cell
  /-- the cells of a largest ring -/
  cells : Loop → Finset Cell
  /-- the opposite of the opposite is the cell itself -/
  opp_opp : ∀ x, opp (opp x) = x
  /-- no cell is its own opposite -/
  opp_ne : ∀ x, opp x ≠ x
  /-- every largest ring has `L` cells -/
  card_cells : ∀ l, (cells l).card = L
  /-- Postulate 2, first clause: the opposite lies on every largest ring through the cell -/
  opp_mem : ∀ l x, x ∈ cells l → opp x ∈ cells l
  /-- Postulate 2, second clause (existence): two cells not opposite lie on a largest ring -/
  exists_loop : ∀ x y, y ≠ x → y ≠ opp x → ∃ l, x ∈ cells l ∧ y ∈ cells l
  /-- Postulate 2, second clause (uniqueness): two cells not opposite lie on one largest ring -/
  unique_loop : ∀ x y l₁ l₂, y ≠ x → y ≠ opp x →
    x ∈ cells l₁ → y ∈ cells l₁ → x ∈ cells l₂ → y ∈ cells l₂ → l₁ = l₂
  /-- Postulate 2, third clause: any two largest rings share a cell -/
  loops_meet : ∀ l₁ l₂, ∃ x, x ∈ cells l₁ ∧ x ∈ cells l₂
  /-- Postulate 2, last clause: no ring holds every cell, so the register has more than one largest
  ring -/
  two_loops : ∃ l₁ l₂ : Loop, l₁ ≠ l₂

namespace Horizon

attribute [instance] Horizon.fintypeCell Horizon.fintypeLoop Horizon.decEqCell Horizon.decEqLoop

variable {L : ℕ} (H : Horizon L)

lemma opp_mem_iff (l : H.Loop) (x : H.Cell) : H.opp x ∈ H.cells l ↔ x ∈ H.cells l := by
  constructor
  · intro h
    have := H.opp_mem l _ h
    rwa [H.opp_opp] at this
  · exact H.opp_mem l x

lemma ne_opp_symm {x y : H.Cell} (h : y ≠ H.opp x) : x ≠ H.opp y := by
  intro hx
  apply h
  rw [hx, H.opp_opp]

/-- Two distinct largest rings share exactly one opposite pair. -/
lemma inter_eq_pair {l₁ l₂ : H.Loop} (h : l₁ ≠ l₂) :
    ∃ x, H.cells l₁ ∩ H.cells l₂ = {x, H.opp x} := by
  obtain ⟨x, hx₁, hx₂⟩ := H.loops_meet l₁ l₂
  refine ⟨x, ?_⟩
  ext y
  simp only [mem_inter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hy₁, hy₂⟩
    by_contra hy
    push Not at hy
    exact h (H.unique_loop x y l₁ l₂ hy.1 hy.2 hx₁ hy₁ hx₂ hy₂)
  · rintro (rfl | rfl)
    · exact ⟨hx₁, hx₂⟩
    · exact ⟨H.opp_mem _ _ hx₁, H.opp_mem _ _ hx₂⟩

/-- The largest rings through a cell. -/
def through (x : H.Cell) : Finset H.Loop := univ.filter (fun l => x ∈ H.cells l)

lemma mem_through {x : H.Cell} {l : H.Loop} : l ∈ H.through x ↔ x ∈ H.cells l := by
  simp [through]

/-- A cell of a largest ring that lies outside a given pair (needs `4 ≤ L`). -/
lemma exists_mem_notMem_pair (hL : 4 ≤ L) (l : H.Loop) (a b : H.Cell) :
    ∃ y ∈ H.cells l, y ≠ a ∧ y ≠ b := by
  have hlt : ({a, b} : Finset H.Cell).card < (H.cells l).card := by
    rw [H.card_cells]
    exact lt_of_le_of_lt card_le_two (by omega)
  obtain ⟨y, hy, hy'⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨y, hy, ?_, ?_⟩
  · intro h; apply hy'; simp [h]
  · intro h; apply hy'; simp [h]

/-- A largest ring through a given cell (needs `4 ≤ L`): join the cell to a cell of any largest
ring outside its pair. -/
lemma exists_loop_mem (hL : 4 ≤ L) (P : H.Cell) : ∃ A : H.Loop, P ∈ H.cells A := by
  obtain ⟨l₁, -, -⟩ := H.two_loops
  obtain ⟨y, -, hyP, hyP'⟩ := H.exists_mem_notMem_pair hL l₁ P (H.opp P)
  obtain ⟨A, hPA, -⟩ := H.exists_loop P y hyP hyP'
  exact ⟨A, hPA⟩

/-- **A cell off a given largest ring** (needs `4 ≤ L`), Postulate 2's last clause.  Here it comes
from `two_loops`: another ring meets the given one in one opposite pair (`inter_eq_pair`), and its
other cells lie off it. -/
lemma exists_cell_not_mem (hL : 4 ≤ L) (l : H.Loop) : ∃ x : H.Cell, x ∉ H.cells l := by
  obtain ⟨l₁, l₂, hne⟩ := H.two_loops
  -- one of the two rings differs from `l`
  have : ∃ m : H.Loop, m ≠ l := by
    by_cases h : l₁ = l
    · exact ⟨l₂, fun h₂ => hne (h.trans h₂.symm)⟩
    · exact ⟨l₁, h⟩
  obtain ⟨m, hm⟩ := this
  obtain ⟨x, hx⟩ := H.inter_eq_pair hm
  obtain ⟨y, hym, hyx, hyx'⟩ := H.exists_mem_notMem_pair hL m x (H.opp x)
  refine ⟨y, fun hyl => ?_⟩
  have : y ∈ H.cells m ∩ H.cells l := mem_inter.2 ⟨hym, hyl⟩
  rw [hx] at this
  simp only [mem_insert, mem_singleton] at this
  tauto

/-- **A largest ring that misses a given cell** (Sec. II, the paper's construction).  Take a
largest ring `A` through `P` and a cell `Q` off it (`exists_cell_not_mem`).  With `S` a cell of `A`
other than `P` and its opposite, `Q` and `S` are not opposite, since the opposite of `S` lies on
`A`, so one largest ring `E` passes through both.  It misses `P`, since the one ring through `P`
and `S` is `A`, which does not hold `Q`. -/
lemma exists_loop_not_mem (hL : 4 ≤ L) (P : H.Cell) : ∃ E : H.Loop, P ∉ H.cells E := by
  obtain ⟨A, hPA⟩ := H.exists_loop_mem hL P
  obtain ⟨Q, hQ⟩ := H.exists_cell_not_mem hL A
  obtain ⟨S, hSA, hSP, hSP'⟩ := H.exists_mem_notMem_pair hL A P (H.opp P)
  have hQS : Q ≠ S := fun h => hQ (h ▸ hSA)
  have hQS' : Q ≠ H.opp S := fun h => hQ (h ▸ H.opp_mem A S hSA)
  obtain ⟨E, hSE, hQE⟩ := H.exists_loop S Q hQS hQS'
  refine ⟨E, fun hPE => hQ ?_⟩
  -- `E` holds `S` and `P`, which are not opposite, so `E` is `A`
  have hE : E = A := H.unique_loop S P E A (Ne.symm hSP) (H.ne_opp_symm hSP') hSE hPE hSA hPA
  exact hE ▸ hQE

/-- **`ρ = L/2`** (Sec. II): twice the number of largest rings through any cell is `L`.  Each ring
through `P` meets the ring `E` that misses `P` in one opposite pair, and each cell of `E` lies on
exactly one ring through `P`; counting the pairs (ring through `P`, cell of `E` on it) both ways
gives `2ρ = L`. -/
theorem two_mul_card_through (hL : 4 ≤ L) (P : H.Cell) : 2 * (H.through P).card = L := by
  obtain ⟨E, hPE⟩ := H.exists_loop_not_mem hL P
  have hP'E : H.opp P ∉ H.cells E := fun h => hPE ((H.opp_mem_iff E P).1 h)
  -- double count the pairs (ring through `P`, cell of `E` on it)
  have key : ∑ l ∈ H.through P, ((H.cells E).filter (fun y => y ∈ H.cells l)).card
      = ∑ y ∈ H.cells E, ((H.through P).filter (fun l => y ∈ H.cells l)).card := by
    simp only [card_filter]
    exact sum_comm
  -- each ring through `P` meets `E` in one opposite pair
  have hleft : ∀ l ∈ H.through P, ((H.cells E).filter (fun y => y ∈ H.cells l)).card = 2 := by
    intro l hl
    rw [mem_through] at hl
    have hne : E ≠ l := fun h => hPE (h ▸ hl)
    obtain ⟨x, hx⟩ := H.inter_eq_pair hne
    rw [filter_mem_eq_inter, hx, card_pair (H.opp_ne x).symm]
  -- each cell of `E` lies on exactly one ring through `P`
  have hright : ∀ y ∈ H.cells E, ((H.through P).filter (fun l => y ∈ H.cells l)).card = 1 := by
    intro y hy
    have hyP : y ≠ P := fun h => hPE (h ▸ hy)
    have hyP' : y ≠ H.opp P := fun h => hP'E (h ▸ hy)
    obtain ⟨l, hPl, hyl⟩ := H.exists_loop P y hyP hyP'
    rw [card_eq_one]
    refine ⟨l, ?_⟩
    ext m
    simp only [mem_filter, mem_through, mem_singleton]
    constructor
    · rintro ⟨hPm, hym⟩
      exact H.unique_loop P y m l hyP hyP' hPm hym hPl hyl
    · rintro rfl
      exact ⟨hPl, hyl⟩
  rw [sum_congr rfl hleft, sum_congr rfl hright] at key
  simp only [sum_const, smul_eq_mul, mul_one, H.card_cells] at key
  omega

/-- `C = 2 + ρ(L − 2)`: the rings through `P` cut the cells other than `P` and its opposite
into disjoint sets of `L − 2`. -/
theorem card_cell_eq (P : H.Cell) :
    Fintype.card H.Cell = 2 + (H.through P).card * (L - 2) := by
  set S : Finset H.Cell := {P, H.opp P} with hS
  have hSc : S.card = 2 := card_pair (H.opp_ne P).symm
  have hmemS : ∀ y, y ∈ S ↔ y = P ∨ y = H.opp P := by
    intro y; simp [hS]
  have hcover : (univ : Finset H.Cell) = S ∪ (H.through P).biUnion (fun l => H.cells l \ S) := by
    ext y
    simp only [mem_univ, true_iff, mem_union, mem_biUnion, mem_sdiff, mem_through]
    by_cases hy : y ∈ S
    · exact Or.inl hy
    · right
      rw [hmemS] at hy
      push Not at hy
      obtain ⟨l, hPl, hyl⟩ := H.exists_loop P y hy.1 hy.2
      refine ⟨l, hPl, hyl, ?_⟩
      rw [hmemS]; push Not; exact hy
  have hdisj : Disjoint S ((H.through P).biUnion (fun l => H.cells l \ S)) := by
    rw [disjoint_biUnion_right]
    intro l _
    exact disjoint_sdiff
  have hpair : ((H.through P : Finset H.Loop) : Set H.Loop).PairwiseDisjoint
      (fun l => H.cells l \ S) := by
    intro l₁ hl₁ l₂ hl₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy₁ hy₂
    rw [mem_sdiff] at hy₁ hy₂
    have hy := hy₁.2
    rw [hmemS] at hy
    push Not at hy
    exact hne (H.unique_loop P y l₁ l₂ hy.1 hy.2 ((H.mem_through).1 (mem_coe.1 hl₁)) hy₁.1
      ((H.mem_through).1 (mem_coe.1 hl₂)) hy₂.1)
  have hcard : ∀ l ∈ H.through P, (H.cells l \ S).card = L - 2 := by
    intro l hl
    rw [card_sdiff_of_subset, H.card_cells, hSc]
    intro y hy
    rw [hmemS] at hy
    rcases hy with rfl | rfl
    · exact (H.mem_through).1 hl
    · exact H.opp_mem _ _ ((H.mem_through).1 hl)
  rw [← card_univ, hcover, card_union_of_disjoint hdisj, hSc, card_biUnion hpair,
    sum_congr rfl hcard, sum_const, smul_eq_mul]

/-- `C = 2R`: counting incidences (cell, ring through it) in both orders. -/
theorem card_cell_eq_two_mul_card_loop (hL : 4 ≤ L) :
    Fintype.card H.Cell = 2 * Fintype.card H.Loop := by
  have key : ∑ l : H.Loop, (H.cells l).card = ∑ x : H.Cell, (H.through x).card := by
    have h1 : ∀ l : H.Loop,
        (H.cells l).card = ∑ x : H.Cell, if x ∈ H.cells l then 1 else 0 := by
      intro l
      rw [← card_filter, filter_mem_eq_inter, univ_inter]
    have h2 : ∀ x : H.Cell,
        (H.through x).card = ∑ l : H.Loop, if x ∈ H.cells l then 1 else 0 := by
      intro x
      rw [through, card_filter]
    simp only [h1, h2]
    exact sum_comm
  have hR : ∑ l : H.Loop, (H.cells l).card = Fintype.card H.Loop * L := by
    simp only [H.card_cells, sum_const, card_univ, smul_eq_mul]
  have hC : 2 * ∑ x : H.Cell, (H.through x).card = Fintype.card H.Cell * L := by
    rw [mul_sum]
    simp only [H.two_mul_card_through hL, sum_const, card_univ, smul_eq_mul]
  have hLpos : 0 < L := by omega
  have : 2 * Fintype.card H.Loop * L = Fintype.card H.Cell * L := by
    rw [mul_assoc, ← hR, key, hC]
  exact (Nat.eq_of_mul_eq_mul_right hLpos this).symm

/-- A cell exists (a largest ring has `L ≥ 4` cells). -/
lemma exists_cell (hL : 4 ≤ L) : Nonempty H.Cell := by
  obtain ⟨l, -, -⟩ := H.two_loops
  have : (H.cells l).Nonempty := by
    rw [← card_pos, H.card_cells]; omega
  obtain ⟨P, -⟩ := this
  exact ⟨P⟩

/-- **Eq. (counts) of the paper.**  With `ρ = L/2` rings through every cell,
`2C = L² − 2L + 4` (that is, `C = L²/2 − L + 2` cells), `4R = L² − 2L + 4` (that is,
`R = L²/4 − L/2 + 1` largest rings), and `C = 2R`. -/
theorem counts (hL : 4 ≤ L) :
    (∀ P : H.Cell, 2 * (H.through P).card = L) ∧
    2 * Fintype.card H.Cell + 2 * L = L ^ 2 + 4 ∧
    4 * Fintype.card H.Loop + 2 * L = L ^ 2 + 4 ∧
    Fintype.card H.Cell = 2 * Fintype.card H.Loop := by
  obtain ⟨P⟩ := H.exists_cell hL
  have hρ := H.two_mul_card_through hL P
  have hC := H.card_cell_eq P
  have hCR := H.card_cell_eq_two_mul_card_loop hL
  have h2 : 2 ≤ L := by omega
  refine ⟨H.two_mul_card_through hL, ?_, ?_, hCR⟩
  · zify [h2] at hρ hC ⊢
    linear_combination 2 * hC + ((L : ℤ) - 2) * hρ
  · zify [h2] at hρ hC hCR ⊢
    linear_combination 2 * hC + ((L : ℤ) - 2) * hρ - 2 * hCR

include H in
/-- `L` is even: a consequence, not an assumption. -/
theorem even_L (hL : 4 ≤ L) : Even L := by
  obtain ⟨P⟩ := H.exists_cell hL
  exact ⟨(H.through P).card, by have := H.two_mul_card_through hL P; omega⟩

end Horizon

end Register
