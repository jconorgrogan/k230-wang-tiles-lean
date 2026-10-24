module
public import SideGeometry
public import CenteredFullBoard
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem root_side_options (n side v j : Nat) (hn : 1≤n) (hs : side<4) (hv : v<4)
    (hj : 0<j ∧ j<4*squareSize n) (hmod : j%4=1) :
    (sideCell n v side j).val=channelExpected side 1 ∨
    (sideCell n v side j).val=channelExpected side 3 := by
  have hfour := four_dvd_squareSize n hn
  obtain ⟨d,hd⟩ := hfour
  have hne : j≠2*squareSize n := by omega
  by_cases hl : j<2*squareSize n
  · exact Or.inl (side_lower_channel n side v j hn hs hv ⟨hj.1,hl⟩ hmod)
  · exact Or.inr (side_upper_channel n side v j hn hs hv ⟨by omega,hj.2⟩ hmod)

@[expose] def rootSidePoint (b : Cell) (N side : Nat) (r : Int) : Cell :=
  if side=0 then centerCell b N (-(boardHalf N:Int)) r
  else if side=1 then centerCell b N (boardHalf N) r
  else if side=2 then centerCell b N r (-(boardHalf N:Int))
  else centerCell b N r (boardHalf N)

theorem fullBoard_root_side_group (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hb : FullBoardAt T n v b) (side : Nat) (hside : side<4) (r : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1)) :
    (indexedGroup (T (rootSidePoint b (n+1) side r))).1 =
      (sideCell n v side ((boardHalf (n+1):Int)+r).toNat).val := by
  have hz : ((boardHalf (n+1):Int)+(-(boardHalf (n+1):Int))).toNat=0 := by omega
  have ht : ((boardHalf (n+1):Int)+(boardHalf (n+1):Int)).toNat=4*squareSize n := by
    have hh := fullBoard_side n
    omega
  have hs : side=0 ∨ side=1 ∨ side=2 ∨ side=3 := by omega
  rcases hs with rfl|rfl|rfl|rfl
  · have h := fullBoard_centered_group T n v b hb (-(boardHalf (n+1):Int)) r (by omega) hr
    simpa only [rootSidePoint,sideCell,hz,ite_true,ite_false,show ¬(0:Nat)=1 by decide,
      show ¬(0:Nat)=2 by decide,show ¬(0:Nat)=3 by decide] using h
  · have h := fullBoard_centered_group T n v b hb (boardHalf (n+1)) r (by omega) hr
    simpa only [rootSidePoint,sideCell,ht,ite_true,ite_false,show ¬(1:Nat)=0 by decide,
      show ¬(1:Nat)=2 by decide,show ¬(1:Nat)=3 by decide] using h
  · have h := fullBoard_centered_group T n v b hb r (-(boardHalf (n+1):Int)) hr (by omega)
    simpa only [rootSidePoint,sideCell,hz,ite_true,ite_false,show ¬(2:Nat)=0 by decide,
      show ¬(2:Nat)=1 by decide,show ¬(2:Nat)=3 by decide] using h
  · have h := fullBoard_centered_group T n v b hb r (boardHalf (n+1)) hr (by omega)
    simpa only [rootSidePoint,sideCell,ht,ite_true,ite_false,show ¬(3:Nat)=0 by decide,
      show ¬(3:Nat)=1 by decide,show ¬(3:Nat)=2 by decide] using h

theorem fullBoard_root_side_options (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hn : 1≤n) (hv : v<4) (hb : FullBoardAt T n v b) (side : Nat) (hside : side<4) (r : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1)) (hmod : r%4=1) :
    (indexedGroup (T (rootSidePoint b (n+1) side r))).1=channelExpected side 1 ∨
    (indexedGroup (T (rootSidePoint b (n+1) side r))).1=channelExpected side 3 := by
  have hH := fullBoard_half n
  obtain ⟨d,hd⟩ := four_dvd_squareSize n hn
  have hj : 0<((boardHalf (n+1):Int)+r).toNat ∧
      ((boardHalf (n+1):Int)+r).toNat<4*squareSize n := by omega
  have hjmod : ((boardHalf (n+1):Int)+r).toNat%4=1 := by omega
  rw [fullBoard_root_side_group T n v b hb side hside r ⟨by omega,by omega⟩]
  exact root_side_options n side v _ hn hside hv hj hjmod

#print axioms fullBoard_root_side_options
end K230Verification
