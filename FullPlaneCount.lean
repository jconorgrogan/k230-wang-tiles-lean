module
public import FullPlaneData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

theorem exact_move_count : tmMoves.length = 255 := by decide
theorem exact_comp_count : tmComp.length = 972 := by decide
theorem exact_fullplane_count : exactFullPlaneTiles.length = 11487 := by decide
#print axioms exact_fullplane_count
end K230Verification
