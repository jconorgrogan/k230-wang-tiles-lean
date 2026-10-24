module
public import Distinctness
public import FullPlaneCount
public import Mathlib.Data.Finset.Card
public section
namespace K230Verification
/-- The exact generated set, not a multiset count: every listed tile is distinct. -/
@[expose] def fullPlaneSet : Finset (Quad FullColor) := exactFullPlaneTiles.toFinset
theorem fullPlaneSet_card : fullPlaneSet.card = 11487 := by
  rw [fullPlaneSet,List.toFinset_card_of_nodup exact_fullplane_nodup]
  exact exact_fullplane_count
#print axioms fullPlaneSet_card
end K230Verification
