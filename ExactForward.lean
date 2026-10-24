module
public import ActualRoutedAssembly
public import ActualBoardTraces
public section
namespace K230Verification

/-- Unseeded whole-plane tiling forces the ordinary blank-tape machine run
    to survive every finite number of transitions. No origin, initial tile,
    finite-window evidence or board-routing assumption is imposed. -/
theorem exact_plane_implies_neverHalts (h : ExactPlane) : K230NeverHalts := by
  obtain ⟨T,hT⟩ := h
  change NeverHalts k230Machine blankConfiguration
  apply cofinal_finiteBoards_iff_neverHalts.mp
  intro k
  obtain ⟨v,b,hv,hb⟩ := exact_computing_board_occurrence T hT k
  exact ⟨actualFiniteBoard T hT k v b hv hb (actual_board_traces T hT k v b hv hb)⟩

/-- Contrapositive with the literal exact tile alphabet. -/
theorem k230_halts_implies_no_exact_plane (h : ¬K230NeverHalts) : ¬ExactPlane :=
  fun hp => h (exact_plane_implies_neverHalts hp)

#print axioms exact_plane_implies_neverHalts
#print axioms k230_halts_implies_no_exact_plane
end K230Verification
