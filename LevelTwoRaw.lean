module
public import LevelTwoPatch
public section
namespace K230Verification

theorem levelTwo_tile_mem (v : Fin 4) (l b : Bool) (x y : Nat) (hx : x<5) (hy : y<5) :
    levelTwoTile v.val l b x y ∈ exactFullPlaneTiles := by
  apply List.mem_flatMap.mpr
  refine ⟨levelTwoGroup v.val l b x y,levelTwo_groups_mem v l b ⟨x,hx⟩ ⟨y,hy⟩,?_⟩
  exact List.mem_map.mpr ⟨levelTwoTM x y,levelTwo_tm_mem x y,rfl⟩

/-- The inert level-2 board with mandatory iX seed, for each exact base-core
    variant and independent allowed outward left/bottom channel choices. -/
@[expose] def levelTwoRawSquare (v : Fin 4) (left bottom : Bool) : RawSquare 4 where
  tile := fun p => levelTwoTile v.val left bottom p.1.toNat p.2.toNat
  member := by
    intro x y hx hxR hy hyR
    exact levelTwo_tile_mem v left bottom x.toNat y.toNat (by omega) (by omega)
  horizontal := by
    intro x y hx hxR hy hyR
    have h := levelTwo_horizontal v left bottom ⟨x.toNat,by omega⟩ ⟨y.toNat,by omega⟩
    have he : (x+1).toNat=x.toNat+1 := by omega
    simpa only [he] using h
  vertical := by
    intro x y hx hxR hy hyR
    have h := levelTwo_vertical v left bottom ⟨x.toNat,by omega⟩ ⟨y.toNat,by omega⟩
    have he : (y+1).toNat=y.toNat+1 := by omega
    simpa only [he] using h

theorem levelTwo_raw_exists (v : Fin 4) (left bottom : Bool) : Nonempty (RawSquare 4) :=
  ⟨levelTwoRawSquare v left bottom⟩
theorem levelTwo_boundary_channels (v : Nat) (left bottom : Bool) :
    (levelTwoTile v left bottom 0 3).w.2.1=(if left then 3 else 2) ∧
    (levelTwoTile v left bottom 0 3).e.2.1=2 ∧
    (levelTwoTile v left bottom 4 3).e.2.1=3 ∧
    (levelTwoTile v left bottom 4 3).w.2.1=2 ∧
    (levelTwoTile v left bottom 3 0).s.2.1=(if bottom then 3 else 2) ∧
    (levelTwoTile v left bottom 3 0).n.2.1=2 ∧
    (levelTwoTile v left bottom 3 4).n.2.1=3 ∧
    (levelTwoTile v left bottom 3 4).s.2.1=2 := by
  cases left <;> cases bottom <;> simp [levelTwoTile,decorate,levelTwoGroup,levelTwoChannels]
theorem levelTwo_center_iX (v : Nat) (left bottom : Bool) :
    (levelTwoTile v left bottom 2 2).e.2.2=.iX ∧
    (levelTwoTile v left bottom 2 2).w.2.2=.iL := ⟨rfl,rfl⟩
#print axioms levelTwo_raw_exists
end K230Verification
