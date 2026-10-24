module
public import RingInduction
public import ChannelClasses
public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace K230Concrete
open K230Verification

theorem lowest_red_boundary {px py dx dy : Nat}
    (h : (px=0 ∧ dx=0) ∨ (py=0 ∧ dy=0)) : lowestRed px py dx dy=0 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [lowestRed,rectStatus]

/-- The entire outer ring of every exact canonical board has its expected
    orientation, including level 2 and all four base variants. -/
theorem redBoard_ring_status (n v x y : Nat) (hv : v<4)
    (hx : x≤4*squareSize n) (hy : y≤4*squareSize n)
    (hb : x=0 ∨ x=4*squareSize n ∨ y=0 ∨ y=4*squareSize n) :
    redStatus (redBoard n v x y).val =
      rectStatus 0 (4*(squareSize n:Int)) 0 (4*(squareSize n:Int)) x y := by
  induction n generalizing x y with
  | zero =>
    have he : redBoard 0 v x y=boardCore v x y := by
      simp only [redBoard,squareSize,width,Nat.div_one,expanded]
    rw [he]
    exact (core_red_status v x y hv hx hy).1
  | succ n ih =>
    have hsz := squareSize_step n
    have hxd : x/4≤4*squareSize n := by omega
    have hyd : y/4≤4*squareSize n := by omega
    have hp := redBoard_parity n v (x/4) (y/4) hv hxd hyd
    have hpb : x/4=0 ∨ x/4=4*squareSize n ∨ y/4=0 ∨ y/4=4*squareSize n := by
      rcases hb with hb|hb|hb|hb <;> omega
    have ha : lowestRed ((x/4)%2) ((y/4)%2) (x%4) (y%4)=0 := by
      apply lowest_red_boundary
      rcases hb with hb|hb|hb|hb <;> omega
    have he := (red_status_step (redBoard n v (x/4) (y/4)) (x%4) (y%4)
      (by omega) (by omega)).2
    rw [hp.1,hp.2,if_pos ha,ih (x/4) (y/4) hxd hyd hpb] at he
    rw [redBoard_step n v x y hv hx hy,he]
    have hpos : (0:Int)<4*(squareSize n:Int) := by have := squareSize_pos n; omega
    have hh := rect_status_scale 0 (4*(squareSize n:Int)) 0 (4*(squareSize n:Int))
      (x/4:Nat) (y/4:Nat) hpos hpos (x%4) (y%4) (by omega) (by omega)
    have hxe : 4*((x/4:Nat):Int)+(x%4:Nat)=x := by omega
    have hye : 4*((y/4:Nat):Int)+(y%4:Nat)=y := by omega
    simpa only [squareSize_step,Int.natCast_mul,show ((4:Nat):Int)=4 by decide,
      Int.mul_zero,hxe,hye] using hh.symm

/-- Ring orientation plus actual channel presence identifies precisely the
    compiler's side index sets, uniformly for inert and computing boards. -/
theorem red_status_channel_index (k : Fin 156) :
    (HasHChannel k.val →
      (redStatus k.val=1 → k.val=100 ∨ k.val=116 ∨ k.val=101) ∧
      (redStatus k.val=2 → k.val=95 ∨ k.val=111 ∨ k.val=96)) ∧
    (HasVChannel k.val →
      (redStatus k.val=3 → k.val=136 ∨ k.val=142 ∨ k.val=151) ∧
      (redStatus k.val=4 → k.val=134 ∨ k.val=140 ∨ k.val=150)) := by
  have h : ∀ k : Fin 156,
    (HasHChannel k.val →
      (redStatus k.val=1 → k.val=100 ∨ k.val=116 ∨ k.val=101) ∧
      (redStatus k.val=2 → k.val=95 ∨ k.val=111 ∨ k.val=96)) ∧
    (HasVChannel k.val →
      (redStatus k.val=3 → k.val=136 ∨ k.val=142 ∨ k.val=151) ∧
      (redStatus k.val=4 → k.val=134 ∨ k.val=140 ∨ k.val=150)) := by decide +kernel
  exact h k

end K230Concrete
#print axioms K230Concrete.redBoard_ring_status
#print axioms K230Concrete.red_status_channel_index
