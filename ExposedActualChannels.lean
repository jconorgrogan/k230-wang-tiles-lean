module
public import RingExposure
public import ActualSegmentTrace
public import CenteredChannels
public section
set_option maxHeartbeats 0
namespace K230Verification
open K230Concrete

theorem boardCovered_swap (N : Nat) (r s : Int)
    (hr : -(boardHalf N:Int)<r ∧ r<boardHalf N)
    (hs : -(boardHalf N:Int)<s ∧ s<boardHalf N) :
    BoardCovered N r s ↔ BoardCovered N s r := by
  constructor
  · rintro ⟨_,_,m,hm,hmN,hx,hy⟩
    exact ⟨hr.1,hr.2,m,hm,hmN,hy,hx⟩
  · rintro ⟨_,_,m,hm,hmN,hy,hx⟩
    exact ⟨hs.1,hs.2,m,hm,hmN,hx,hy⟩

/-- The concrete no-extra-rings theorem discharges both local copying exceptions. -/
theorem fullBoard_exposed_not_boundary (T : Cell → Fin 11487) (n v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) :
    ¬hBoundary (indexedGroup (T (centerCell b (n+1) r s))).1 ∧
    ¬vBoundary (indexedGroup (T (centerCell b (n+1) r s))).1 := by
  have hh := fullBoard_half n
  let x := ((boardHalf (n+1):Int)+r).toNat
  let y := ((boardHalf (n+1):Int)+s).toNat
  have hx : 0<x ∧ x<4*squareSize n := by dsimp [x]; omega
  have hy : 0<y ∧ y<4*squareSize n := by dsimp [y]; omega
  have hxr : (x:Int)-2*squareSize n=r := by dsimp [x]; omega
  have hyr : (y:Int)-2*squareSize n=s := by dsimp [y]; omega
  have he' : ¬BoardCovered (n+1) ((x:Int)-2*squareSize n) ((y:Int)-2*squareSize n) := by
    simpa only [hxr,hyr] using he
  have h := exposed_not_boundary n v x y hv hx hy he'
  rw [fullBoard_centered_group T n v b hb r s ⟨by omega,by omega⟩ ⟨by omega,by omega⟩]
  exact h

theorem fullBoard_exposed_vertical_copy (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) :
    verticalTrace T b (n+1) r s=verticalTrace T b (n+1) r (s-1) := by
  have hn := (fullBoard_exposed_not_boundary T n v b hv hb r s hr hs he).2
  have h := actual_vcopy T hT (centerCell b (n+1) r s) hn
  have hp : ((centerCell b (n+1) r s).1,(centerCell b (n+1) r s).2-1)=
      centerCell b (n+1) r (s-1) := by apply Prod.ext <;> dsimp [centerCell] <;> omega
  rw [hp] at h
  exact h

theorem fullBoard_exposed_horizontal_copy (T : Cell → Fin 11487) (hT : FullValid T)
    (n v : Nat) (b : Cell) (hv : v<4) (hb : FullBoardAt T n v b) (r s : Int)
    (hr : -(boardHalf (n+1):Int)<r ∧ r<boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)<s ∧ s<boardHalf (n+1))
    (he : ¬BoardCovered (n+1) s r) :
    horizontalTrace T b (n+1) s r=horizontalTrace T b (n+1) s (r-1) := by
  have he' : ¬BoardCovered (n+1) r s := fun h => he ((boardCovered_swap (n+1) r s hr hs).mp h)
  have hn := (fullBoard_exposed_not_boundary T n v b hv hb r s hr hs he').1
  have h := actual_hcopy T hT (centerCell b (n+1) r s) hn
  have hp : ((centerCell b (n+1) r s).1-1,(centerCell b (n+1) r s).2)=
      centerCell b (n+1) (r-1) s := by apply Prod.ext <;> dsimp [centerCell] <;> omega
  rw [hp] at h
  exact h

#print axioms fullBoard_exposed_not_boundary
#print axioms fullBoard_exposed_vertical_copy
end K230Verification
