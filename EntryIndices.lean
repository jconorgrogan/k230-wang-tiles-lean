module
public import CropSides
public import BoardEntrances
public import GeometricSubboards
public import BoardLocality
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace K230Concrete
open K230Verification

@[expose] def boardAtRelative (n v : Nat) (r s : Int) : Fin 156 :=
  redBoard n v ((boardHalf (n+1):Int)+r).toNat ((boardHalf (n+1):Int)+s).toNat

theorem lower_side_length (b : RedSquare) : 4*squareSize (b.level-1)=2*boardHalf b.level := by
  have hb := b.level_pos
  have he : (b.level-1)+1=b.level := by omega
  have hh := boardHalf_index (b.level-1)
  rw [he] at hh
  omega

theorem lower_board_crop (n v : Nat) (b : RedSquare) (hv : v<4)
    (hb : LowerSquareInside (n+1) b) :
    ∃ w : Nat, w<4 ∧ BoardCrop n (b.level-1) v w (lowerOriginX n b) (lowerOriginY n b) := by
  obtain ⟨w,hw,hc⟩ := geometric_subboard_crop n v b hv hb
  refine ⟨w,hw,?_⟩
  intro r s hr hs
  rw [lower_side_length] at hr hs
  exact hc r s hr hs

theorem relative_channel_presence (n v : Nat) (hn : 1≤n) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r) (hs : -(boardHalf (n+1):Int)<s) :
    (s%4=1 → HasHChannel (boardAtRelative n v r s).val) ∧
    (r%4=1 → HasVChannel (boardAtRelative n v r s).val) := by
  have hd := lower_period_dvd_half (m:=1) (n:=n+1) (by omega) (by omega)
  have hd' : (8:Int)∣(boardHalf (n+1):Int) := by
    simpa only [show (boardHalf 1:Int)=2 by decide,show (4:Int)*2=8 by decide] using hd
  obtain ⟨q,hq⟩ := hd'
  have hx : (((boardHalf (n+1):Int)+r).toNat:Int)=(boardHalf (n+1):Int)+r := by omega
  have hy : (((boardHalf (n+1):Int)+s).toNat:Int)=(boardHalf (n+1):Int)+s := by omega
  have h := redBoard_modulo_four n hn v ((boardHalf (n+1):Int)+r).toNat
    ((boardHalf (n+1):Int)+s).toNat
  exact ⟨fun hm => h.1.mpr (by omega),fun hm => h.2.mpr (by omega)⟩

theorem redBoard_vertical_entry (n v : Nat) (r s : Int) (hv : v<4)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<(boardHalf (n+1):Int))
    (hmod : r%4=1) (hc : BoardCovered (n+1) r s) (hn : ¬BoardCovered (n+1) r (s-1)) :
    (boardAtRelative n v r s).val=136 ∨ (boardAtRelative n v r s).val=142 ∨
      (boardAtRelative n v r s).val=151 := by
  obtain ⟨b,hb,hp,he⟩ := covered_vertical_entry hr hc hn
  obtain ⟨w,hw,hcrop⟩ := lower_board_crop n v b hv hb
  have hs0 := hc.1
  have hl := lower_origins n b hb
  have hsize := lower_side_length b
  have hn' : 1≤n := by have := hb.1; have := b.level_pos; omega
  have hchan := (relative_channel_presence n v hn' r s hr.1 hc.1).2 hmod
  have hx : (((boardHalf (n+1):Int)+r).toNat:Int)=(boardHalf (n+1):Int)+r := by omega
  have hy : ((boardHalf (n+1):Int)+s).toNat=lowerOriginY n b := by omega
  have hbounds : lowerOriginX n b≤((boardHalf (n+1):Int)+r).toNat ∧
      ((boardHalf (n+1):Int)+r).toNat≤lowerOriginX n b+4*squareSize (b.level-1) := by
    have h1 := hp.1.1; have h2 := hp.1.2
    omega
  dsimp only [boardAtRelative] at hchan ⊢
  rw [hy] at hchan ⊢
  exact crop_bottom_indices hw hcrop hbounds hchan

theorem redBoard_vertical_exit (n v : Nat) (r s : Int) (hv : v<4)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<(boardHalf (n+1):Int))
    (hmod : r%4=1) (hc : BoardCovered (n+1) r s) (hn : ¬BoardCovered (n+1) r (s+1)) :
    (boardAtRelative n v r s).val=134 ∨ (boardAtRelative n v r s).val=140 ∨
      (boardAtRelative n v r s).val=150 := by
  obtain ⟨b,hb,hp,he⟩ := covered_vertical_exit hr hc hn
  obtain ⟨w,hw,hcrop⟩ := lower_board_crop n v b hv hb
  have hs0 := hc.1
  have hl := lower_origins n b hb
  have hsize := lower_side_length b
  have hn' : 1≤n := by have := hb.1; have := b.level_pos; omega
  have hchan := (relative_channel_presence n v hn' r s hr.1 hc.1).2 hmod
  have hx : (((boardHalf (n+1):Int)+r).toNat:Int)=(boardHalf (n+1):Int)+r := by omega
  have hy : ((boardHalf (n+1):Int)+s).toNat=lowerOriginY n b+4*squareSize (b.level-1) := by omega
  have hbounds : lowerOriginX n b≤((boardHalf (n+1):Int)+r).toNat ∧
      ((boardHalf (n+1):Int)+r).toNat≤lowerOriginX n b+4*squareSize (b.level-1) := by
    have h1 := hp.1.1; have h2 := hp.1.2
    omega
  dsimp only [boardAtRelative] at hchan ⊢
  rw [hy] at hchan ⊢
  exact crop_top_indices hw hcrop hbounds hchan

theorem redBoard_horizontal_entry (n v : Nat) (r s : Int) (hv : v<4)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<(boardHalf (n+1):Int))
    (hmod : s%4=1) (hc : BoardCovered (n+1) r s) (hn : ¬BoardCovered (n+1) (r-1) s) :
    (boardAtRelative n v r s).val=100 ∨ (boardAtRelative n v r s).val=116 ∨
      (boardAtRelative n v r s).val=101 := by
  obtain ⟨b,hb,hp,he⟩ := covered_horizontal_entry hr hc hn
  obtain ⟨w,hw,hcrop⟩ := lower_board_crop n v b hv hb
  have hs0 := hc.1
  have hl := lower_origins n b hb
  have hsize := lower_side_length b
  have hn' : 1≤n := by have := hb.1; have := b.level_pos; omega
  have hchan := (relative_channel_presence n v hn' r s hr.1 hc.1).1 hmod
  have hy : (((boardHalf (n+1):Int)+s).toNat:Int)=(boardHalf (n+1):Int)+s := by omega
  have hx : ((boardHalf (n+1):Int)+r).toNat=lowerOriginX n b := by omega
  have hbounds : lowerOriginY n b≤((boardHalf (n+1):Int)+s).toNat ∧
      ((boardHalf (n+1):Int)+s).toNat≤lowerOriginY n b+4*squareSize (b.level-1) := by
    have h1 := hp.2.1; have h2 := hp.2.2
    omega
  dsimp only [boardAtRelative] at hchan ⊢
  rw [hx] at hchan ⊢
  exact crop_left_indices hw hcrop hbounds hchan

theorem redBoard_horizontal_exit (n v : Nat) (r s : Int) (hv : v<4)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<(boardHalf (n+1):Int))
    (hmod : s%4=1) (hc : BoardCovered (n+1) r s) (hn : ¬BoardCovered (n+1) (r+1) s) :
    (boardAtRelative n v r s).val=95 ∨ (boardAtRelative n v r s).val=111 ∨
      (boardAtRelative n v r s).val=96 := by
  obtain ⟨b,hb,hp,he⟩ := covered_horizontal_exit hr hc hn
  obtain ⟨w,hw,hcrop⟩ := lower_board_crop n v b hv hb
  have hs0 := hc.1
  have hl := lower_origins n b hb
  have hsize := lower_side_length b
  have hn' : 1≤n := by have := hb.1; have := b.level_pos; omega
  have hchan := (relative_channel_presence n v hn' r s hr.1 hc.1).1 hmod
  have hy : (((boardHalf (n+1):Int)+s).toNat:Int)=(boardHalf (n+1):Int)+s := by omega
  have hx : ((boardHalf (n+1):Int)+r).toNat=lowerOriginX n b+4*squareSize (b.level-1) := by omega
  have hbounds : lowerOriginY n b≤((boardHalf (n+1):Int)+s).toNat ∧
      ((boardHalf (n+1):Int)+s).toNat≤lowerOriginY n b+4*squareSize (b.level-1) := by
    have h1 := hp.2.1; have h2 := hp.2.2
    omega
  dsimp only [boardAtRelative] at hchan ⊢
  rw [hx] at hchan ⊢
  exact crop_right_indices hw hcrop hbounds hchan

end K230Concrete
#print axioms K230Concrete.redBoard_vertical_entry
#print axioms K230Concrete.redBoard_vertical_exit
#print axioms K230Concrete.redBoard_horizontal_entry
#print axioms K230Concrete.redBoard_horizontal_exit
