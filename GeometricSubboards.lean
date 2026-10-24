module
public import SubboardCrops
public import RedBoardGeometry
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace K230Concrete

open K230Verification

theorem boardHalf_index (n : Nat) : boardHalf (n+1)=2*squareSize n := by
  simp only [boardHalf,Nat.add_sub_cancel,squareSize_power]

theorem natural_grid_from_center (H h : Nat) (c : Int) (hh:0<h)
    (halign : (4*(h:Int)) ∣ (H:Int))
    (hcenter : CenteredAt h c)
    (hinside : -(H:Int)<c-h ∧ c+h<H) :
    let x0 := ((H:Int)+c-h).toNat
    ∃ q:Nat, H+x0=4*h*q+h ∧ 0<x0 ∧ x0+2*h<2*H := by
  let x0 := ((H:Int)+c-h).toNat
  have hp : (0:Int)<h := by omega
  have hx : (x0:Int)=(H:Int)+c-h := by dsimp [x0]; omega
  have h0 : 0<x0 := by omega
  have hb : x0+2*h<2*H := by omega
  have hH : (H:Int)%(4*(h:Int))=0 := Int.emod_eq_zero_of_dvd halign
  have h2H : (2*(H:Int))%(4*(h:Int))=0 := by rw [Int.mul_emod,hH]; simp
  have hrh : (h:Int)%(4*(h:Int))=h := Int.emod_eq_of_lt (by omega) (by omega)
  have hr2h : (2*(h:Int))%(4*(h:Int))=2*(h:Int) := Int.emod_eq_of_lt (by omega) (by omega)
  have hnum : ((H+x0:Nat):Int)=2*(H:Int)+c-h := by omega
  have hr : ((H+x0:Nat):Int)%(4*(h:Int))=h := by
    rw [hnum]
    rw [Int.sub_emod,Int.add_emod,h2H,hcenter,Int.zero_add,hr2h,hrh]
    have he : 2*(h:Int)-h=h := by omega
    rw [he]
    exact hrh
  have hrNat : (H+x0)%(4*h)=h := by exact_mod_cast hr
  refine ⟨(H+x0)/(4*h),?_,h0,hb⟩
  have he := Nat.div_add_mod (H+x0) (4*h)
  rw [hrNat] at he
  simpa only [Nat.mul_assoc] using he.symm

@[expose] def lowerOriginX (N : Nat) (b : RedSquare) : Nat :=
  ((boardHalf (N+1):Int)+b.cx-boardHalf b.level).toNat
@[expose] def lowerOriginY (N : Nat) (b : RedSquare) : Nat :=
  ((boardHalf (N+1):Int)+b.cy-boardHalf b.level).toNat

theorem lower_origins (N : Nat) (b : RedSquare) (hb:LowerSquareInside (N+1) b) :
    (lowerOriginX N b:Int)=(boardHalf (N+1):Int)+b.cx-boardHalf b.level ∧
    (lowerOriginY N b:Int)=(boardHalf (N+1):Int)+b.cy-boardHalf b.level ∧
    0<lowerOriginX N b ∧ 0<lowerOriginY N b ∧
    lowerOriginX N b+2*boardHalf b.level<2*boardHalf (N+1) ∧
    lowerOriginY N b+2*boardHalf b.level<2*boardHalf (N+1) := by
  dsimp [LowerSquareInside] at hb
  dsimp [lowerOriginX,lowerOriginY]
  omega

theorem geometric_subboard_crop (N v : Nat) (b : RedSquare)
    (hv:v<4) (hb:LowerSquareInside (N+1) b) :
    ∃ w:Nat, w<4 ∧ ∀ r s:Nat, r≤2*boardHalf b.level → s≤2*boardHalf b.level →
      redBoard N v (lowerOriginX N b+r) (lowerOriginY N b+s) =
        redBoard (b.level-1) w r s := by
  have hlevel := b.level_pos
  have hm : b.level=(b.level-1)+1 := by omega
  have hmN : b.level-1≤N := by have hh:=hb.1; omega
  have hbig := boardHalf_index N
  have hsmall : boardHalf b.level=2*squareSize (b.level-1) := by
    rw [hm]
    exact boardHalf_index (b.level-1)
  have hp := board_half_pos b.level
  have hd := lower_period_dvd_half b.level_pos hb.1
  obtain ⟨qx,hqx,hx0,hxb⟩ := natural_grid_from_center (boardHalf (N+1)) (boardHalf b.level)
    b.cx hp hd b.centered_x ⟨hb.2.1,hb.2.2.1⟩
  obtain ⟨qy,hqy,hy0,hyb⟩ := natural_grid_from_center (boardHalf (N+1)) (boardHalf b.level)
    b.cy hp hd b.centered_y ⟨hb.2.2.2.1,hb.2.2.2.2⟩
  change boardHalf (N+1)+lowerOriginX N b=4*boardHalf b.level*qx+boardHalf b.level at hqx
  change boardHalf (N+1)+lowerOriginY N b=4*boardHalf b.level*qy+boardHalf b.level at hqy
  change lowerOriginX N b+2*boardHalf b.level<2*boardHalf (N+1) at hxb
  change lowerOriginY N b+2*boardHalf b.level<2*boardHalf (N+1) at hyb
  rw [hbig,hsmall] at hqx hqy hxb hyb
  have hgx : 2*squareSize N+lowerOriginX N b=
      8*squareSize (b.level-1)*qx+2*squareSize (b.level-1) := by
    simp only [Nat.mul_assoc] at hqx ⊢
    omega
  have hgy : 2*squareSize N+lowerOriginY N b=
      8*squareSize (b.level-1)*qy+2*squareSize (b.level-1) := by
    simp only [Nat.mul_assoc] at hqy ⊢
    omega
  obtain ⟨w,hw,hcrop⟩ := subboard_crop N (b.level-1) v
    (lowerOriginX N b) (lowerOriginY N b) qx qy hmN hv hgx hgy (by omega) (by omega)
  refine ⟨w,hw,?_⟩
  intro r s hr hs
  rw [hsmall] at hr hs
  exact hcrop r s (by omega) (by omega)

end K230Concrete

#print axioms K230Concrete.geometric_subboard_crop
