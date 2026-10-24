module
public import FullPlaneCount
public import MachineRun
public import WangCompactness
public section
namespace K230Verification
/-- The literal finite tile alphabet, with the exact verified enumeration size. -/
@[expose] def indexedFullTile (i : Fin 11487) : Quad FullColor :=
  exactFullPlaneTiles[i.val]'(by rw [exact_fullplane_count]; exact i.isLt)
@[expose] def indexedWangTile (i : Fin 11487) : WangTile FullColor :=
  let t := indexedFullTile i
  ⟨t.n,t.e,t.s,t.w⟩
/-- No seed, origin, boundary, or initialization constraint is imposed on the plane. -/
@[expose] def ExactPlane : Prop := TilesPlane indexedWangTile
@[expose] def ExactWindows : Prop := TilesEveryWindow indexedWangTile
/-- Initial state0, head at0, and the completely blank two-way tape. -/
@[expose] def k230Initial : Configuration := ⟨0,0,fun _ => false⟩
@[expose] def K230NeverHalts : Prop := NeverHalts k230Machine k230Initial
/-- This compactness reduction is unconditional. Constructing every decorated
    window remains a separate obligation; no finite sample implies it. -/
theorem exact_plane_iff_windows : ExactPlane ↔ ExactWindows :=
  tilesPlane_iff_everyWindow indexedWangTile
/-- The full intended endpoint. No inhabitant/proof of this definition is
    asserted merely by giving the goal a name. -/
@[expose] def FullPlaneObjective : Prop := ExactPlane ↔ K230NeverHalts
end K230Verification
