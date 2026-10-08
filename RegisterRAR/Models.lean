import RegisterRAR.Positions
import Mathlib.Data.Fin.VecNotation

/-!
# The axioms of `Horizon` and `Positions` have a model

A theorem proved from contradictory axioms would hold vacuously, so the axioms of `Horizon L` need
a model.  The smallest is `L = 6`: the Fano plane, the projective plane of order `2 = L/2 − 1`,
with each point doubled into a cell and its opposite.  Every axiom is checked by `decide`, and the
counts of `Horizon.counts` come out as `14 = L²/2 − L + 2` cells and `7 = L²/4 − L/2 + 1` rings.
The cyclic order of `Positions.lean` has a model on it too: each ring runs through its three points
on one side and back through them on the other, so that the opposite of a cell lies three steps,
half the ring, on.
-/

open Finset

namespace Register
namespace Models

/-- The seven lines of the Fano plane on the points `0, …, 6`. -/
def fanoLines : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

/-- **A horizon with `L = 6`**: cells are (point, side), the opposite flips the side, and a largest
ring is a Fano line with both sides of each of its three points. -/
def fano : Horizon 6 where
  Cell := Fin 7 × Bool
  Loop := Fin 7
  opp x := (x.1, !x.2)
  cells l := fanoLines l ×ˢ univ
  opp_opp := by decide
  opp_ne := by decide
  card_cells := by decide
  opp_mem := by decide
  exists_loop := by decide
  unique_loop := by decide
  loops_meet := by decide
  two_loops := by decide

/-- The counts of Sec. II for the model: `14` cells, `7` rings, `ρ = 3` rings per cell. -/
theorem fano_counts :
    Fintype.card fano.Cell = 14 ∧ Fintype.card fano.Loop = 7 ∧
    2 * Fintype.card fano.Cell + 2 * 6 = 6 ^ 2 + 4 ∧
    4 * Fintype.card fano.Loop + 2 * 6 = 6 ^ 2 + 4 := by
  have h := fano.counts (by norm_num)
  refine ⟨by decide, by decide, h.2.1, h.2.2.1⟩

/-- The three points of each Fano line, in order. -/
def fanoList : Fin 7 → Fin 3 → Fin 7 :=
  ![![0, 1, 2], ![0, 3, 4], ![0, 5, 6], ![1, 3, 5], ![1, 4, 6], ![2, 3, 6], ![2, 4, 5]]

/-- the place of a point on a Fano line, `0`, `1` or `2` -/
def fanoIdx (l p : Fin 7) : ZMod 6 :=
  if fanoList l 0 = p then 0 else if fanoList l 1 = p then 1 else 2

/-- **Positions on the Fano horizon**: a ring runs through the three points of its line on one
side, at the positions `0, 1, 2`, and back through them on the other, at `3, 4, 5`; the opposite of
a cell lies three steps, half the ring, on. -/
def fanoPositions : fano.Positions where
  pos l x := fanoIdx l x.1 + (if x.2 then 3 else 0)
  pos_inj := by decide
  pos_opp := by decide

/-- In the model, `L = 6` is even because the opposite lies halfway round
(`Positions.even_of_halfway`). -/
theorem fano_even : Even 6 := by
  have hx : (((0 : Fin 7), false) : fano.Cell) ∈ fano.cells (0 : Fin 7) := by
    show ((0 : Fin 7), false) ∈ fanoLines 0 ×ˢ (univ : Finset Bool)
    decide
  exact fanoPositions.even_of_halfway (by norm_num) _ _ hx

end Models
end Register
