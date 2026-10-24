module
public import ExactForward
public import ExposedBoardWitness
public import ReverseReduction
public import Distinctness
public section
namespace K230Verification

/-- Every nonhalting blank-tape run supplies finite exact decorated boards
    of unbounded size. Recursive child filling and compactness produce a
    whole-plane tiling, without a distinguished origin or a prescribed tile. -/
theorem neverHalts_implies_exact_plane (h : K230NeverHalts) : ExactPlane := by
  have hrun : NeverHalts k230Machine blankConfiguration := h
  apply exactPlane_of_exposed_boards
  intro k v hv left bottom
  obtain ⟨F⟩ := neverHalts_finiteBoard hrun (2^k)
  exact ⟨computingExposedBoard F v hv left bottom⟩

/-- Unconditional equivalence for the literal 11,487-tile alphabet and the
    exact 230-state transition table, with the ordinary all-blank initial tape. -/
theorem exact_plane_iff_neverHalts : ExactPlane ↔ K230NeverHalts :=
  ⟨exact_plane_implies_neverHalts,neverHalts_implies_exact_plane⟩

theorem full_plane_objective : FullPlaneObjective := exact_plane_iff_neverHalts


/-- Cardinality, nonduplication, and the full-plane computation equivalence
    certified together for one and the same literal tile list. -/
theorem exact_11487_equivalence :
    exactFullPlaneTiles.length=11487 ∧ exactFullPlaneTiles.Nodup ∧
      (ExactPlane ↔ K230NeverHalts) :=
  ⟨exact_fullplane_count,exact_fullplane_nodup,exact_plane_iff_neverHalts⟩

end K230Verification
#print axioms K230Verification.neverHalts_implies_exact_plane
#print axioms K230Verification.exact_plane_iff_neverHalts
#print axioms K230Verification.full_plane_objective

#print axioms K230Verification.exact_11487_equivalence
