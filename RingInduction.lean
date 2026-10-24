module
public import RingClassification
public section
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

theorem geometric_red_scale {n s : Nat} {x y : Int}
    (h : GeometricRed n s x y) (dx dy : Nat) (hdx : dx<4) (hdy : dy<4) :
    GeometricRed (n+1) (refineRed s dx dy) (4*x+dx) (4*y+dy) := by
  rcases h with h | ⟨m,hm,hmn,cx,cy,hcx,hcy,h⟩
  · apply Or.inl
    rw [h]
    have hp : (0:Int)<4*(squareSize n:Int) := by have := squareSize_pos n; omega
    have he := rect_status_scale 0 (4*(squareSize n:Int)) 0 (4*(squareSize n:Int))
      x y hp hp dx dy hdx hdy
    simpa only [squareSize_step,Int.natCast_mul,Int.mul_zero,show ((4:Nat):Int)=4 by decide] using he.symm
  · apply Or.inr
    refine ⟨m+1,by omega,by omega,4*cx,4*cy,?_,?_,?_⟩
    · have hh : (boardHalf (m+1):Int)=4*(boardHalf m:Int) := by
        exact_mod_cast board_half_step hm
      rw [hh]
      exact centered_scale hcx
    · have hh : (boardHalf (m+1):Int)=4*(boardHalf m:Int) := by
        exact_mod_cast board_half_step hm
      rw [hh]
      exact centered_scale hcy
    · have hp : (0:Int)<boardHalf m := by have := board_half_pos m; omega
      have hh : (boardHalf (m+1):Int)=4*(boardHalf m:Int) := by
        exact_mod_cast board_half_step hm
      rw [hh,h]
      have he := rect_status_scale (cx-boardHalf m) (cx+boardHalf m)
        (cy-boardHalf m) (cy+boardHalf m) x y (by omega) (by omega) dx dy hdx hdy
      simpa only [Int.mul_sub,Int.mul_add] using he.symm

/-- There are no red sides or corners outside the root ring and the canonical
    smaller red-square rings. This is an exact all-scale consequence of σ²,
    not a sampled geometric observation. -/
theorem red_status_geometric (n v x y : Nat) (hv : v<4)
    (hx : x≤4*squareSize n) (hy : y≤4*squareSize n)
    (hs : redStatus (redBoard n v x y).val≠0) :
    GeometricRed n (redStatus (redBoard n v x y).val) x y := by
  induction n generalizing x y with
  | zero =>
    apply Or.inl
    have he : redBoard 0 v x y=boardCore v x y := by
      simp only [redBoard,squareSize,width,Nat.mul_zero,Nat.div_one,Nat.mod_one,expanded]
    rw [he]
    exact (core_red_status v x y hv hx hy).1
  | succ n ih =>
    have hsz := squareSize_step n
    have hxd : x/4≤4*squareSize n := by omega
    have hyd : y/4≤4*squareSize n := by omega
    have hp := redBoard_parity n v (x/4) (y/4) hv hxd hyd
    have he := (red_status_step (redBoard n v (x/4) (y/4)) (x%4) (y%4)
      (by omega) (by omega)).2
    rw [hp.1,hp.2] at he
    have heb : redStatus (redBoard (n+1) v x y).val =
        if lowestRed ((x/4)%2) ((y/4)%2) (x%4) (y%4)=0 then
          refineRed (redStatus (redBoard n v (x/4) (y/4)).val) (x%4) (y%4)
        else lowestRed ((x/4)%2) ((y/4)%2) (x%4) (y%4) := by
      rw [redBoard_step n v x y hv hx hy]
      exact he
    rw [heb] at hs ⊢
    by_cases ha : lowestRed ((x/4)%2) ((y/4)%2) (x%4) (y%4)=0
    · simp only [ha,if_true] at hs ⊢
      have hparent := ih (x/4) (y/4) hxd hyd (refine_nonzero hs)
      have hh := geometric_red_scale hparent (x%4) (y%4) (by omega) (by omega)
      have hxe : 4*((x/4:Nat):Int)+(x%4:Nat)=x := by omega
      have hye : 4*((y/4:Nat):Int)+(y%4:Nat)=y := by omega
      rw [hxe,hye] at hh
      exact hh
    · simp only [ha,if_false] at hs ⊢
      apply Or.inr
      refine ⟨1,by omega,by omega,lowestCenter x,lowestCenter y,?_,?_,?_⟩
      · exact lowest_centered x
      · exact lowest_centered y
      · exact lowest_red_geometric x y

end K230Concrete
#print axioms K230Concrete.red_status_geometric
