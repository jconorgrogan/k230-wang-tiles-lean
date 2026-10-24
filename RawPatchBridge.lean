module
public import ExactTarget
public import FinitePatchCompactness
public section
namespace K230Verification

theorem exact_tile_has_index {t : Quad FullColor} (ht : t ∈ exactFullPlaneTiles) :
    ∃ i : Fin 11487, indexedFullTile i = t := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ht
  have hbound : i < 11487 := by simpa only [exact_fullplane_count] using hi
  exact ⟨⟨i,hbound⟩,he⟩

@[expose] noncomputable def chooseExactIndex (t : Quad FullColor) : Fin 11487 := by
  classical
  exact if h : t ∈ exactFullPlaneTiles then Classical.choose (exact_tile_has_index h) else ⟨0,by decide⟩

theorem chooseExactIndex_spec {t : Quad FullColor} (ht : t ∈ exactFullPlaneTiles) :
    indexedFullTile (chooseExactIndex t) = t := by
  classical
  simp only [chooseExactIndex,dif_pos ht]
  exact Classical.choose_spec (exact_tile_has_index ht)

/-- Actual decorated colors on a finite square. Membership is required only
    inside that square; no external completion or cross-size coherence is assumed. -/
structure RawSquare (R : Nat) where
  tile : Cell → Quad FullColor
  member : ∀ x y : Int, 0≤x → x≤R → 0≤y → y≤R → tile (x,y) ∈ exactFullPlaneTiles
  horizontal : ∀ x y : Int, 0≤x → x<R → 0≤y → y≤R →
    (tile (x,y)).e = (tile (x+1,y)).w
  vertical : ∀ x y : Int, 0≤x → x≤R → 0≤y → y<R →
    (tile (x,y)).n = (tile (x,y+1)).s

@[expose] noncomputable def RawSquare.indices {R : Nat} (B : RawSquare R) : Cell → Fin 11487 :=
  fun p => chooseExactIndex (B.tile p)

theorem RawSquare.square_valid {R : Nat} (B : RawSquare R) :
    SquareValid indexedWangTile B.indices R := by
  constructor
  · intro x y hx hxR hy hyR
    have h1 := chooseExactIndex_spec (B.member x y hx (by omega) hy hyR)
    have h2 := chooseExactIndex_spec (B.member (x+1) y (by omega) (by omega) hy hyR)
    simpa only [RawSquare.indices,indexedWangTile,h1,h2] using B.horizontal x y hx hxR hy hyR
  · intro x y hx hxR hy hyR
    have h1 := chooseExactIndex_spec (B.member x y hx hxR hy (by omega))
    have h2 := chooseExactIndex_spec (B.member x (y+1) hx hxR (by omega) (by omega))
    simpa only [RawSquare.indices,indexedWangTile,h1,h2] using B.vertical x y hx hxR hy hyR

theorem exactPlane_of_cofinal_raw_squares
    (patches : ∀ n : Nat, ∃ R : Nat, n≤R ∧ Nonempty (RawSquare R)) : ExactPlane := by
  apply tilesPlane_of_cofinal_squares indexedWangTile
  intro n
  obtain ⟨R,hR,⟨B⟩⟩ := patches n
  exact ⟨R,hR,B.indices,B.square_valid⟩
end K230Verification
