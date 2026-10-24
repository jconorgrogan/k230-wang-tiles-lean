module
public import Std

/- Independent arithmetic bound for the finite computing boards. -/
public section
namespace K230Verification

/-- A Turing head starts at logical column zero and moves one column per step. -/
def UnitHeadPath (position : Nat → Int) : Prop :=
  position 0 = 0 ∧ ∀ t, position (t+1) = position t + 1 ∨
    position (t+1) = position t - 1

theorem unit_head_bound {position : Nat → Int} (hp : UnitHeadPath position) :
    ∀ t : Nat, -(t : Int) ≤ position t ∧ position t ≤ (t : Int) := by
  intro t
  induction t with
  | zero => simp [hp.1]
  | succ t ih =>
    rcases hp.2 t with h | h <;> constructor <;> omega

/-- A board with H columns to the left and H columns from the start to the
    right has logical tape interval [-H,H-1]. Every pre-final head lies inside. -/
theorem head_inside_before_last {position : Nat → Int} (hp : UnitHeadPath position)
    {H t : Nat} (ht : t < H) :
    -(H : Int) ≤ position t ∧ position t < (H : Int) := by
  have hb := unit_head_bound hp t
  constructor <;> omega

/-- Within H transitions, the head cannot cross the left board edge. -/
theorem no_left_exit {position : Nat → Int} (hp : UnitHeadPath position)
    {H t : Nat} (ht : t ≤ H) : -(H : Int) ≤ position t := by
  have hb := unit_head_bound hp t
  omega

/-- The right absorber can be reached in H rows only on the final row. -/
theorem right_exit_only_last {position : Nat → Int} (hp : UnitHeadPath position)
    {H t : Nat} (ht : t ≤ H) (exit : (H : Int) ≤ position t) :
    t = H ∧ position t = (H : Int) := by
  have hb := unit_head_bound hp t
  constructor <;> omega

#print axioms unit_head_bound
#print axioms head_inside_before_last
#print axioms no_left_exit
#print axioms right_exit_only_last
end K230Verification
