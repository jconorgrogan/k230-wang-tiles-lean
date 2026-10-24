module
public import RedStatus
public import RingAlgebra
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace K230Concrete
open K230Verification

/-- The outer ring or a canonical ring of a strictly smaller red board. -/
@[expose] def GeometricRed (n s : Nat) (x y : Int) : Prop :=
  s=rectStatus 0 (4*(squareSize n:Int)) 0 (4*(squareSize n:Int)) x y ∨
  ∃ m : Nat, 1≤m ∧ m≤n ∧ ∃ cx cy : Int,
    CenteredAt (boardHalf m) cx ∧ CenteredAt (boardHalf m) cy ∧
    s=rectStatus (cx-boardHalf m) (cx+boardHalf m)
      (cy-boardHalf m) (cy+boardHalf m) x y

theorem expanded_successor_parity (n : Nat) (k : Fin 156) (x y : Nat) :
    (Wang156.tile (expanded (n+1) k x y).val).px=x%2 ∧
    (Wang156.tile (expanded (n+1) k x y).val).py=y%2 := by
  have hq : x%2+2*(y%2)<4 := by omega
  have h := Wang156.sigma_parity (expanded n k (x/2) (y/2)) ⟨x%2+2*(y%2),hq⟩
  have hxq : (x%2+2*(y%2))%2=x%2 := by omega
  have hyq : (x%2+2*(y%2))/2=y%2 := by omega
  simpa [expanded,child,hxq,hyq] using h

theorem redBoard_parity (n v x y : Nat) (hv : v<4)
    (hx : x≤4*squareSize n) (hy : y≤4*squareSize n) :
    (Wang156.tile (redBoard n v x y).val).px=x%2 ∧
    (Wang156.tile (redBoard n v x y).val).py=y%2 := by
  cases n with
  | zero =>
    have he : redBoard 0 v x y=boardCore v x y := by
      simp only [redBoard,squareSize,width,Nat.mul_zero,Nat.div_one,Nat.mod_one,expanded]
    rw [he]
    exact (core_red_status v x y hv hx hy).2
  | succ n =>
    rw [redBoard_step n v x y hv hx hy]
    have h := expanded_successor_parity 1 (redBoard n v (x/4) (y/4)) (x%4) (y%4)
    have hx' : x%4%2=x%2 := by omega
    have hy' : y%4%2=y%2 := by omega
    simpa only [hx',hy'] using h

@[expose] def lowestCenter (x : Nat) : Int := (x:Int)-(x:Int)%8+4

theorem lowest_centered (x : Nat) : CenteredAt 2 (lowestCenter x) := by
  unfold CenteredAt lowestCenter
  omega

theorem lowest_red_geometric (x y : Nat) :
    lowestRed ((x/4)%2) ((y/4)%2) (x%4) (y%4) =
    rectStatus (lowestCenter x-2) (lowestCenter x+2)
      (lowestCenter y-2) (lowestCenter y+2) x y := by
  have hx : 4*(((x/4)%2:Nat):Int)+((x%4:Nat):Int)=(x:Int)%8 := by omega
  have hy : 4*(((y/4)%2:Nat):Int)+((y%4:Nat):Int)=(y:Int)%8 := by omega
  unfold lowestRed
  rw [hx,hy]
  have h := rect_status_translate 2 6 2 6 ((x:Int)%8) ((y:Int)%8)
    ((x:Int)-(x:Int)%8) ((y:Int)-(y:Int)%8)
  have hLx : (2:Int)+(x-(x:Int)%8)=lowestCenter x-2 := by unfold lowestCenter; omega
  have hRx : (6:Int)+(x-(x:Int)%8)=lowestCenter x+2 := by unfold lowestCenter; omega
  have hLy : (2:Int)+(y-(y:Int)%8)=lowestCenter y-2 := by unfold lowestCenter; omega
  have hRy : (6:Int)+(y-(y:Int)%8)=lowestCenter y+2 := by unfold lowestCenter; omega
  have heX : (x:Int)%8+(x-(x:Int)%8)=x := by omega
  have heY : (y:Int)%8+(y-(y:Int)%8)=y := by omega
  rw [hLx,hRx,hLy,hRy,heX,heY] at h
  exact h.symm

end K230Concrete
