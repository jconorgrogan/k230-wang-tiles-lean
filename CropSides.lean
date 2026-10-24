module
public import RingSides
public section
namespace K230Concrete
open K230Verification

@[expose] def BoardCrop (N m v w x0 y0 : Nat) : Prop :=
  ∀ r s : Nat, r≤4*squareSize m → s≤4*squareSize m →
    redBoard N v (x0+r) (y0+s)=redBoard m w r s

theorem crop_bottom_indices {N m v w x0 y0 x : Nat}
    (hw : w<4) (hcrop : BoardCrop N m v w x0 y0)
    (hx : x0≤x ∧ x≤x0+4*squareSize m)
    (hchan : HasVChannel (redBoard N v x y0).val) :
    (redBoard N v x y0).val=136 ∨ (redBoard N v x y0).val=142 ∨ (redBoard N v x y0).val=151 := by
  have he := hcrop (x-x0) 0 (by omega) (by omega)
  have hx' : x0+(x-x0)=x := by omega
  rw [hx',Nat.add_zero] at he
  rw [he] at hchan ⊢
  exact redBoard_bottom_indices m w (x-x0) hw (by omega) hchan

theorem crop_top_indices {N m v w x0 y0 x : Nat}
    (hw : w<4) (hcrop : BoardCrop N m v w x0 y0)
    (hx : x0≤x ∧ x≤x0+4*squareSize m)
    (hchan : HasVChannel (redBoard N v x (y0+4*squareSize m)).val) :
    (redBoard N v x (y0+4*squareSize m)).val=134 ∨
    (redBoard N v x (y0+4*squareSize m)).val=140 ∨
    (redBoard N v x (y0+4*squareSize m)).val=150 := by
  have he := hcrop (x-x0) (4*squareSize m) (by omega) (by omega)
  have hx' : x0+(x-x0)=x := by omega
  rw [hx'] at he
  rw [he] at hchan ⊢
  exact redBoard_top_indices m w (x-x0) hw (by omega) hchan

theorem crop_left_indices {N m v w x0 y0 y : Nat}
    (hw : w<4) (hcrop : BoardCrop N m v w x0 y0)
    (hy : y0≤y ∧ y≤y0+4*squareSize m)
    (hchan : HasHChannel (redBoard N v x0 y).val) :
    (redBoard N v x0 y).val=100 ∨ (redBoard N v x0 y).val=116 ∨ (redBoard N v x0 y).val=101 := by
  have he := hcrop 0 (y-y0) (by omega) (by omega)
  have hy' : y0+(y-y0)=y := by omega
  rw [hy',Nat.add_zero] at he
  rw [he] at hchan ⊢
  exact redBoard_left_indices m w (y-y0) hw (by omega) hchan

theorem crop_right_indices {N m v w x0 y0 y : Nat}
    (hw : w<4) (hcrop : BoardCrop N m v w x0 y0)
    (hy : y0≤y ∧ y≤y0+4*squareSize m)
    (hchan : HasHChannel (redBoard N v (x0+4*squareSize m) y).val) :
    (redBoard N v (x0+4*squareSize m) y).val=95 ∨
    (redBoard N v (x0+4*squareSize m) y).val=111 ∨
    (redBoard N v (x0+4*squareSize m) y).val=96 := by
  have he := hcrop (4*squareSize m) (y-y0) (by omega) (by omega)
  have hy' : y0+(y-y0)=y := by omega
  rw [hy'] at he
  rw [he] at hchan ⊢
  exact redBoard_right_indices m w (y-y0) hw (by omega) hchan

end K230Concrete
