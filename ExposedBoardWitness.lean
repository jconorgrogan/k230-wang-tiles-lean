module
public import ExposedTemplateMembership
public import ExposedBoardContract
public import LowerPieceChannels
public import RedBoardMatching
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace K230Verification
open K230Concrete

@[expose] def combineLayers (b c : Quad Nat) (t : Quad TMColor) : Quad FullColor :=
  ⟨(b.n,c.n,t.n),(b.e,c.e,t.e),(b.s,c.s,t.s),(b.w,c.w,t.w)⟩

theorem combineLayers_member {b : Fin 156} {c : Quad Nat} {t : Quad TMColor}
    {g : Nat × Nat × Nat} (hg : g ∈ exactGroups.toList) (hb : g.1=b.val)
    (hc : groupChannel g=c) (ht : t ∈ tmFamily g.2.2) :
    combineLayers (baseTileQuad b) c t ∈ exactFullPlaneTiles := by
  have he : combineLayers (baseTileQuad b) c t=decorate g t := by
    rw [←hc]
    unfold combineLayers baseTileQuad
    rw [←hb]
    rfl
  rw [he]
  apply List.mem_flatMap.mpr
  exact ⟨g,hg,List.mem_map.mpr ⟨t,ht,rfl⟩⟩

@[expose] noncomputable def exposedTile {k : Nat} (F : FiniteBoard k230Machine (2^k))
    (v : Nat) (left bottom : Int → Bool) (p : Cell) : Quad FullColor :=
  let r := p.1-2*squareSize (k+1)
  let s := p.2-2*squareSize (k+1)
  combineLayers (baseTileQuad (redBoard (k+1) v p.1.toNat p.2.toNat))
    (boolPieceChannels (k+2) left bottom r s) (stretchedTM F r s)

theorem exposedTile_member {k : Nat} (F : FiniteBoard k230Machine (2^k)) (v : Nat)
    (hv : v<4) (left bottom : Int → Bool) (x y : Int)
    (hx : 0≤x) (hxR : x≤4*squareSize (k+1)) (hy : 0≤y) (hyR : y≤4*squareSize (k+1))
    (he : ¬RootCovered (k+2) (x-2*squareSize (k+1),y-2*squareSize (k+1))) :
    exposedTile F v left bottom (x,y) ∈ exactFullPlaneTiles := by
  let r := x-2*squareSize (k+1)
  let s := y-2*squareSize (k+1)
  have hh := computingBoard_half k
  have hn : boardHalf (k+1+1)=boardHalf (k+2) := rfl
  have hr : -(boardHalf (k+2) : Int)≤r ∧ r≤boardHalf (k+2) := by dsimp [r]; omega
  have hs : -(boardHalf (k+2) : Int)≤s ∧ s≤boardHalf (k+2) := by dsimp [s]; omega
  have hexp : ¬BoardCovered (k+2) r s := fun h => he ((rootCovered_iff_boardCovered hr).mpr h)
  have hc := boolPieceChannels_legal (k+1) v (by omega) hv left bottom r s hr hs hexp
  obtain ⟨g,hg,hbase,hchan⟩ := legal_channels_have_group hc
  have ht := piece_template_member F hv (outerChoice left) (outerChoice bottom) hg hr hs hexp hbase hchan
  have hxr : (boardHalf (k+2) : Int)+r=x := by dsimp [r]; omega
  have hyr : (boardHalf (k+2) : Int)+s=y := by dsimp [s]; omega
  have hrelative : boardAtRelative (k+1) v r s=redBoard (k+1) v x.toNat y.toNat := by
    simp only [boardAtRelative,hn,hxr,hyr]
  change combineLayers (baseTileQuad (redBoard (k+1) v x.toNat y.toNat))
    (boolPieceChannels (k+2) left bottom r s) (stretchedTM F r s) ∈ exactFullPlaneTiles
  exact combineLayers_member hg (hbase.trans (congrArg Fin.val hrelative)) hchan ht

theorem exposedTile_horizontal {k : Nat} (F : FiniteBoard k230Machine (2^k)) (v : Nat)
    (hv : v<4) (left bottom : Int → Bool) (x y : Int)
    (hx : 0≤x) (hxR : x<4*squareSize (k+1)) (hy : 0≤y) (hyR : y≤4*squareSize (k+1)) :
    (exposedTile F v left bottom (x,y)).e=(exposedTile F v left bottom (x+1,y)).w := by
  have hinc : (x+1).toNat=x.toNat+1 := by omega
  have hshift : x+1-2*squareSize (k+1)=(x-2*squareSize (k+1))+1 := by omega
  have hb := redBoard_horizontal (k+1) v x.toNat y.toNat hv (by omega) (by omega)
  dsimp only [exposedTile,combineLayers,baseTileQuad]
  rw [hinc,hshift]
  exact Prod.ext hb (Prod.ext (boolPieceChannels_match_h (k+2) left bottom (x-2*squareSize (k+1)) (y-2*squareSize (k+1))) (stretchedTM_horizontal F _ _))

theorem exposedTile_vertical {k : Nat} (F : FiniteBoard k230Machine (2^k)) (v : Nat)
    (hv : v<4) (left bottom : Int → Bool) (x y : Int)
    (hx : 0≤x) (hxR : x≤4*squareSize (k+1)) (hy : 0≤y) (hyR : y<4*squareSize (k+1)) :
    (exposedTile F v left bottom (x,y)).n=(exposedTile F v left bottom (x,y+1)).s := by
  have hinc : (y+1).toNat=y.toNat+1 := by omega
  have hshift : y+1-2*squareSize (k+1)=(y-2*squareSize (k+1))+1 := by omega
  have hb := redBoard_vertical (k+1) v x.toNat y.toNat hv (by omega) (by omega)
  dsimp only [exposedTile,combineLayers,baseTileQuad]
  rw [hinc,hshift]
  exact Prod.ext hb (Prod.ext (boolPieceChannels_match_v (k+2) left bottom (x-2*squareSize (k+1)) (y-2*squareSize (k+1))) (stretchedTM_vertical F _ _))

/-- All holes are blank in the root's TM layer, and every outer/lower-ring
    channel contract is concrete. This is the input to finite recursive
    child-board replacement, not an assumed completion. -/
noncomputable def computingExposedBoard {k : Nat} (F : FiniteBoard k230Machine (2^k))
    (v : Nat) (hv : v<4) (left bottom : Int → Bool) : ExposedBoard (k+1) v left bottom where
  tile := exposedTile F v left bottom
  member := exposedTile_member F v hv left bottom
  horizontal := exposedTile_horizontal F v hv left bottom
  vertical := exposedTile_vertical F v hv left bottom
  base := by
    intro x y hx hy
    simp only [exposedTile,combineLayers,fullBase,Int.toNat_natCast]
  west := by
    intro j hj
    have hh := computingBoard_half k
    have he : (0:Int)-2*squareSize (k+1)=-(boardHalf (k+2) : Int) := by omega
    change (boolPieceChannels (k+2) left bottom ((0:Int)-2*squareSize (k+1)) ((j:Int)-2*squareSize (k+1))).w=_ ∧
      (stretchedTM F ((0:Int)-2*squareSize (k+1)) ((j:Int)-2*squareSize (k+1))).w=.blank
    rw [he]
    exact ⟨boolPieceChannels_west _ _ _ _,stretchedTM_outer_west F _⟩
  east := by
    intro j hj
    have hh := computingBoard_half k
    have he : (4*(squareSize (k+1) : Int))-2*squareSize (k+1)=(boardHalf (k+2) : Int) := by omega
    change (boolPieceChannels (k+2) left bottom ((4*(squareSize (k+1) : Int))-2*squareSize (k+1)) ((j:Int)-2*squareSize (k+1))).e=_ ∧
      (stretchedTM F ((4*(squareSize (k+1) : Int))-2*squareSize (k+1)) ((j:Int)-2*squareSize (k+1))).e=.blank
    rw [he]
    exact ⟨boolPieceChannels_east _ _ _ _,stretchedTM_outer_east F _⟩
  south := by
    intro j hj
    have hh := computingBoard_half k
    have he : (0:Int)-2*squareSize (k+1)=-(boardHalf (k+2) : Int) := by omega
    change (boolPieceChannels (k+2) left bottom ((j:Int)-2*squareSize (k+1)) ((0:Int)-2*squareSize (k+1))).s=_ ∧
      (stretchedTM F ((j:Int)-2*squareSize (k+1)) ((0:Int)-2*squareSize (k+1))).s=.blank
    rw [he]
    exact ⟨boolPieceChannels_south _ _ _ _,stretchedTM_outer_south F _⟩
  north := by
    intro j hj
    have hh := computingBoard_half k
    have he : (4*(squareSize (k+1) : Int))-2*squareSize (k+1)=(boardHalf (k+2) : Int) := by omega
    change (boolPieceChannels (k+2) left bottom ((j:Int)-2*squareSize (k+1)) ((4*(squareSize (k+1) : Int))-2*squareSize (k+1))).n=_ ∧
      (stretchedTM F ((j:Int)-2*squareSize (k+1)) ((4*(squareSize (k+1) : Int))-2*squareSize (k+1))).n=.blank
    rw [he]
    exact ⟨boolPieceChannels_north _ _ _ _,stretchedTM_outer_north F _⟩
  covered_blank := by
    intro x y hx hy hc
    exact stretchedTM_covered_blank F hc.2.2
  lower_west := by
    intro b hb j hj
    exact boolPieceChannels_lower_west (k+1) left bottom b hb j hj
  lower_east := by
    intro b hb j hj
    exact boolPieceChannels_lower_east (k+1) left bottom b hb j hj
  lower_south := by
    intro b hb j hj
    exact boolPieceChannels_lower_south (k+1) left bottom b hb j hj
  lower_north := by
    intro b hb j hj
    exact boolPieceChannels_lower_north (k+1) left bottom b hb j hj

#print axioms exposedTile_member
#print axioms computingExposedBoard
end K230Verification
