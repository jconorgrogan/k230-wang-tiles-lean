module
public import ConstructedBoolChannels
public import BoardEntrances
public import GeometricSubboards
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem redSquare_center_mod_four (b : RedSquare) : b.cx%4=0 ∧ b.cy%4=0 := by
  have hd : (4:Int) ∣ 4*(boardHalf b.level:Int) := ⟨_,rfl⟩
  have hh : (boardHalf b.level:Int)=2*(4^(b.level-1):Nat) := by simp [boardHalf]
  have h2 : (2*(boardHalf b.level:Int))%4=0 := by omega
  have hx := Int.emod_emod_of_dvd b.cx hd
  have hy := Int.emod_emod_of_dvd b.cy hd
  rw [b.centered_x,h2] at hx
  rw [b.centered_y,h2] at hy
  exact ⟨hx.symm,hy.symm⟩

theorem lower_square_covered_both {N : Nat} {b : RedSquare} {r s : Int}
    (hb : LowerSquareInside N b) (hp : InRedSquare b (r,s)) :
    BoardCovered N r s ∧ BoardCovered N s r ∧
    (-(boardHalf N:Int)<r ∧ r<boardHalf N) ∧
    (-(boardHalf N:Int)<s ∧ s<boardHalf N) := by
  have hc := lower_square_covered hb hp
  have hr : -(boardHalf N:Int)<r ∧ r<boardHalf N := by
    have := hb.2.1; have := hb.2.2.1; have := hp.1.1; have := hp.1.2; omega
  refine ⟨hc,?_,hr,hc.1,hc.2.1⟩
  obtain ⟨_,_,m,hm,hmN,hmr,hms⟩ := hc
  exact ⟨hr.1,hr.2,m,hm,hmN,hms,hmr⟩

theorem pieceH_covered_incoming (N : Nat) (hN : 2≤N) (left : Int → Channel) (r s : Int)
    (hr : -(boardHalf N:Int)<r ∧ r<boardHalf N)
    (hc : BoardCovered N s r) (hm : s%4=1) :
    pieceH N left (r-1) s=2 ∨ pieceH N left (r-1) s=3 := by
  rw [pieceH_inner N left (r-1) s hm ⟨by omega,by omega⟩]
  simp only [innerChannel,if_neg (show N≠1 by omega)]
  exact code_outer_left (segmentChannel_outer_left (by simpa using hc))

theorem pieceH_covered_outgoing (N : Nat) (hN : 2≤N) (left : Int → Channel) (r s : Int)
    (hr : -(boardHalf N:Int)<r ∧ r<boardHalf N)
    (hc : BoardCovered N s r) (hm : s%4=1) : pieceH N left r s=3 := by
  rw [pieceH_inner N left r s hm ⟨by omega,hr.2⟩]
  simp only [innerChannel,if_neg (show N≠1 by omega),segmentChannel_outer_right hc]
  rfl

theorem pieceV_covered_incoming (N : Nat) (hN : 2≤N) (bottom : Int → Channel) (r s : Int)
    (hs : -(boardHalf N:Int)<s ∧ s<boardHalf N)
    (hc : BoardCovered N r s) (hm : r%4=1) :
    pieceV N bottom r (s-1)=2 ∨ pieceV N bottom r (s-1)=3 :=
  pieceH_covered_incoming N hN bottom s r hs hc hm

theorem pieceV_covered_outgoing (N : Nat) (hN : 2≤N) (bottom : Int → Channel) (r s : Int)
    (hs : -(boardHalf N:Int)<s ∧ s<boardHalf N)
    (hc : BoardCovered N r s) (hm : r%4=1) : pieceV N bottom r s=3 :=
  pieceH_covered_outgoing N hN bottom s r hs hc hm

 theorem boolPieceChannels_lower_west_relative (N : Nat) (hN : 2≤N) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside N b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    let d := (boolPieceChannels N left bottom (b.cx-boardHalf b.level) (b.cy+(j:Int)-boardHalf b.level)).w
    if ((j:Int)-boardHalf b.level)%4=1 then d=2 ∨ d=3 else d=0 := by
  let r : Int := b.cx-boardHalf b.level
  let s : Int := b.cy+(j:Int)-boardHalf b.level
  have hp : InRedSquare b (r,s) := by
    dsimp [InRedSquare,ClosedInterval,r,s]
    have hh := board_half_pos b.level
    omega
  have hc := lower_square_covered_both hb hp
  have hcent := (redSquare_center_mod_four b).2
  have hmod : s%4=((j:Int)-boardHalf b.level)%4 := by
    dsimp [s]
    omega
  by_cases hm : ((j:Int)-boardHalf b.level)%4=1
  · change if ((j:Int)-boardHalf b.level)%4=1 then _ else _
    rw [if_pos hm]
    exact pieceH_covered_incoming N hN (outerChoice left) r s hc.2.2.1 hc.2.1 (by omega)
  · change if ((j:Int)-boardHalf b.level)%4=1 then _ else _
    rw [if_neg hm]
    exact pieceH_absent N (outerChoice left) (r-1) s (by omega)

 theorem boolPieceChannels_lower_east_relative (N : Nat) (hN : 2≤N) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside N b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    (boolPieceChannels N left bottom (b.cx+boardHalf b.level) (b.cy+(j:Int)-boardHalf b.level)).e=
      outgoingOuterDigit ((j:Int)-boardHalf b.level) := by
  let r : Int := b.cx+boardHalf b.level
  let s : Int := b.cy+(j:Int)-boardHalf b.level
  have hp : InRedSquare b (r,s) := by
    dsimp [InRedSquare,ClosedInterval,r,s]
    have hh := board_half_pos b.level
    omega
  have hc := lower_square_covered_both hb hp
  have hcent := (redSquare_center_mod_four b).2
  have hmod : s%4=((j:Int)-boardHalf b.level)%4 := by
    dsimp [s]
    omega
  by_cases hm : ((j:Int)-boardHalf b.level)%4=1
  · rw [outgoingOuterDigit,if_pos hm]
    exact pieceH_covered_outgoing N hN (outerChoice left) r s hc.2.2.1 hc.2.1 (by omega)
  · rw [outgoingOuterDigit,if_neg hm]
    exact pieceH_absent N (outerChoice left) r s (by omega)

 theorem boolPieceChannels_lower_south_relative (N : Nat) (hN : 2≤N) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside N b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    let d := (boolPieceChannels N left bottom (b.cx+(j:Int)-boardHalf b.level) (b.cy-boardHalf b.level)).s
    if ((j:Int)-boardHalf b.level)%4=1 then d=2 ∨ d=3 else d=0 := by
  let r : Int := b.cx+(j:Int)-boardHalf b.level
  let s : Int := b.cy-boardHalf b.level
  have hp : InRedSquare b (r,s) := by
    dsimp [InRedSquare,ClosedInterval,r,s]
    have hh := board_half_pos b.level
    omega
  have hc := lower_square_covered_both hb hp
  have hcent := (redSquare_center_mod_four b).1
  have hmod : r%4=((j:Int)-boardHalf b.level)%4 := by
    dsimp [r]
    omega
  by_cases hm : ((j:Int)-boardHalf b.level)%4=1
  · change if ((j:Int)-boardHalf b.level)%4=1 then _ else _
    rw [if_pos hm]
    exact pieceV_covered_incoming N hN (outerChoice bottom) r s hc.2.2.2 hc.1 (by omega)
  · change if ((j:Int)-boardHalf b.level)%4=1 then _ else _
    rw [if_neg hm]
    exact pieceV_absent N (outerChoice bottom) r (s-1) (by omega)

 theorem boolPieceChannels_lower_north_relative (N : Nat) (hN : 2≤N) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside N b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    (boolPieceChannels N left bottom (b.cx+(j:Int)-boardHalf b.level) (b.cy+boardHalf b.level)).n=
      outgoingOuterDigit ((j:Int)-boardHalf b.level) := by
  let r : Int := b.cx+(j:Int)-boardHalf b.level
  let s : Int := b.cy+boardHalf b.level
  have hp : InRedSquare b (r,s) := by
    dsimp [InRedSquare,ClosedInterval,r,s]
    have hh := board_half_pos b.level
    omega
  have hc := lower_square_covered_both hb hp
  have hcent := (redSquare_center_mod_four b).1
  have hmod : r%4=((j:Int)-boardHalf b.level)%4 := by
    dsimp [r]
    omega
  by_cases hm : ((j:Int)-boardHalf b.level)%4=1
  · rw [outgoingOuterDigit,if_pos hm]
    exact pieceV_covered_outgoing N hN (outerChoice bottom) r s hc.2.2.2 hc.1 (by omega)
  · rw [outgoingOuterDigit,if_neg hm]
    exact pieceV_absent N (outerChoice bottom) r s (by omega)

theorem boolPieceChannels_lower_west (n : Nat) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside (n+1) b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    let d := (boolPieceChannels (n+1) left bottom ((lowerOriginX n b:Int) - 2*squareSize n) ((lowerOriginY n b:Int) + j - 2*squareSize n)).w
    if ((j:Int)-boardHalf b.level)%4=1 then d=2 ∨ d=3 else d=0 := by
  have ho := lower_origins n b hb
  have hh := fullBoard_half n
  have hx : (lowerOriginX n b:Int) - 2*squareSize n=b.cx - boardHalf b.level := by omega
  have hy : (lowerOriginY n b:Int) + j - 2*squareSize n=b.cy + (j:Int) - boardHalf b.level := by omega
  rw [hx,hy]
  exact boolPieceChannels_lower_west_relative (n+1) (by have := b.level_pos; have := hb.1; omega) left bottom b hb j hj

theorem boolPieceChannels_lower_east (n : Nat) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside (n+1) b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    (boolPieceChannels (n+1) left bottom ((lowerOriginX n b:Int) + 2*boardHalf b.level - 2*squareSize n) ((lowerOriginY n b:Int) + j - 2*squareSize n)).e=
      outgoingOuterDigit ((j:Int)-boardHalf b.level) := by
  have ho := lower_origins n b hb
  have hh := fullBoard_half n
  have hx : (lowerOriginX n b:Int) + 2*boardHalf b.level - 2*squareSize n=b.cx + boardHalf b.level := by omega
  have hy : (lowerOriginY n b:Int) + j - 2*squareSize n=b.cy + (j:Int) - boardHalf b.level := by omega
  rw [hx,hy]
  exact boolPieceChannels_lower_east_relative (n+1) (by have := b.level_pos; have := hb.1; omega) left bottom b hb j hj

theorem boolPieceChannels_lower_south (n : Nat) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside (n+1) b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    let d := (boolPieceChannels (n+1) left bottom ((lowerOriginX n b:Int) + j - 2*squareSize n) ((lowerOriginY n b:Int) - 2*squareSize n)).s
    if ((j:Int)-boardHalf b.level)%4=1 then d=2 ∨ d=3 else d=0 := by
  have ho := lower_origins n b hb
  have hh := fullBoard_half n
  have hx : (lowerOriginX n b:Int) + j - 2*squareSize n=b.cx + (j:Int) - boardHalf b.level := by omega
  have hy : (lowerOriginY n b:Int) - 2*squareSize n=b.cy - boardHalf b.level := by omega
  rw [hx,hy]
  exact boolPieceChannels_lower_south_relative (n+1) (by have := b.level_pos; have := hb.1; omega) left bottom b hb j hj

theorem boolPieceChannels_lower_north (n : Nat) (left bottom : Int → Bool)
    (b : RedSquare) (hb : LowerSquareInside (n+1) b) (j : Nat) (hj : j≤2*boardHalf b.level) :
    (boolPieceChannels (n+1) left bottom ((lowerOriginX n b:Int) + j - 2*squareSize n) ((lowerOriginY n b:Int) + 2*boardHalf b.level - 2*squareSize n)).n=
      outgoingOuterDigit ((j:Int)-boardHalf b.level) := by
  have ho := lower_origins n b hb
  have hh := fullBoard_half n
  have hx : (lowerOriginX n b:Int) + j - 2*squareSize n=b.cx + (j:Int) - boardHalf b.level := by omega
  have hy : (lowerOriginY n b:Int) + 2*boardHalf b.level - 2*squareSize n=b.cy + boardHalf b.level := by omega
  rw [hx,hy]
  exact boolPieceChannels_lower_north_relative (n+1) (by have := b.level_pos; have := hb.1; omega) left bottom b hb j hj

#print axioms boolPieceChannels_lower_west
#print axioms boolPieceChannels_lower_north
end K230Verification
