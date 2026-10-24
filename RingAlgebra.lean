module
public import RedStatusData
public import RedBoardGeometry
public section
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

theorem rect_status_translate (L R B T x y a b : Int) :
    rectStatus (L+a) (R+a) (B+b) (T+b) (x+a) (y+b) =
      rectStatus L R B T x y := by
  simp [rectStatus]

theorem rect_status_scale (L R B T x y : Int) (hLR : L<R) (hBT : B<T)
    (dx dy : Nat) (hdx : dx<4) (hdy : dy<4) :
    rectStatus (4*L) (4*R) (4*B) (4*T) (4*x+dx) (4*y+dy) =
      refineRed (rectStatus L R B T x y) dx dy := by
  have hneLR : L≠R := by omega
  have hdx0 : (0:Int)≤dx := by omega
  have hdy0 : (0:Int)≤dy := by omega
  have hdx4 : (dx:Int)<4 := by omega
  have hdy4 : (dy:Int)<4 := by omega
  have hxL : 4*L≤4*x+dx ↔ L≤x := by omega
  have hxR : 4*x+dx≤4*R ↔ x<R ∨ (x=R ∧ dx=0) := by omega
  have hyB : 4*B≤4*y+dy ↔ B≤y := by omega
  have hyT : 4*y+dy≤4*T ↔ y<T ∨ (y=T ∧ dy=0) := by omega
  have hxEqL : 4*x+(dx:Int)=4*L ↔ x=L ∧ dx=0 := by omega
  have hxEqR : 4*x+(dx:Int)=4*R ↔ x=R ∧ dx=0 := by omega
  have hyEqB : 4*y+(dy:Int)=4*B ↔ y=B ∧ dy=0 := by omega
  have hyEqT : 4*y+(dy:Int)=4*T ↔ y=T ∧ dy=0 := by omega
  simp only [rectStatus,hxL,hxR,hyB,hyT,hxEqL,hxEqR,hyEqB,hyEqT]
  by_cases hx1 : x<L
  · have : ¬L≤x := by omega
    simp [this,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
  by_cases hx2 : x=L
  · subst x
    by_cases hy1 : y<B
    · have : ¬B≤y := by omega
      simp [this,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy2 : y=B
    · subst y
      have hRL : L≤R := by omega
      have hTB : B≤T := by omega
      have hne : B≠T := by omega
      simp [hLR,hBT,hRL,hTB,hne,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy3 : y<T
    · have hBy : B≤y := by omega
      have hRL : L≤R := by omega
      have hyT' : y≤T := by omega
      have hynT : y≠T := by omega
      simp [hLR,hRL,hBy,hyT',hy3,hy2,hynT,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy4 : y=T
    · subst y
      have hRL : L≤R := by omega
      have hTB : B≤T := by omega
      have hne : T≠B := by omega
      simp [hLR,hRL,hTB,hne,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    · have hTy : ¬y≤T := by omega
      have hyT' : ¬y<T := by omega
      simp [hTy,hyT',hy4,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
  by_cases hx3 : x<R
  · have hLx : L≤x := by omega
    have hxR' : x≤R := by omega
    have hxnR : x≠R := by omega
    by_cases hy1 : y<B
    · have : ¬B≤y := by omega
      simp [this,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy2 : y=B
    · subst y
      have hTB : B≤T := by omega
      have hne : B≠T := by omega
      simp [hLx,hxR',hx2,hx3,hxnR,hTB,hBT,hne,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy3 : y<T
    · have hBy : B≤y := by omega
      have hyT' : y≤T := by omega
      have hynT : y≠T := by omega
      simp [hLx,hxR',hx2,hx3,hxnR,hBy,hyT',hy3,hy2,hynT,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy4 : y=T
    · subst y
      have hTB : B≤T := by omega
      have hne : T≠B := by omega
      simp [hLx,hxR',hx2,hx3,hxnR,hTB,hne,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    · have hTy : ¬y≤T := by omega
      have hyT' : ¬y<T := by omega
      simp [hTy,hyT',hy4,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
  by_cases hx4 : x=R
  · subst x
    have hLx : L≤R := by omega
    by_cases hy1 : y<B
    · have : ¬B≤y := by omega
      simp [this,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy2 : y=B
    · subst y
      have hTB : B≤T := by omega
      have hne : B≠T := by omega
      simp [hLx,hx2,hTB,hBT,hne,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy3 : y<T
    · have hBy : B≤y := by omega
      have hyT' : y≤T := by omega
      have hynT : y≠T := by omega
      simp [hLx,hx2,hBy,hyT',hy3,hy2,hynT,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    by_cases hy4 : y=T
    · subst y
      have hTB : B≤T := by omega
      have hne : T≠B := by omega
      simp [hLx,hx2,hTB,hne,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
    · have hTy : ¬y≤T := by omega
      have hyT' : ¬y<T := by omega
      simp [hTy,hyT',hy4,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)
  · have hRx : ¬x≤R := by omega
    simp [hRx,hx3,hx4,refineRed] <;> (by_cases hdxz : dx=0 <;> by_cases hdyz : dy=0 <;> simp_all)


theorem rect_status_bounds {L R B T x y : Int}
    (h : rectStatus L R B T x y≠0) : L≤x ∧ x≤R ∧ B≤y ∧ y≤T := by
  unfold rectStatus at h
  split at h
  · assumption
  · contradiction

theorem rect_status_interior {L R B T x y : Int}
    (h : L<x ∧ x<R ∧ B<y ∧ y<T) : rectStatus L R B T x y=0 := by
  have hL : x≠L := by omega
  have hR : x≠R := by omega
  have hB : y≠B := by omega
  have hT : y≠T := by omega
  simp [rectStatus,hL,hR,hB,hT]

theorem refine_nonzero {s dx dy : Nat} (h : refineRed s dx dy≠0) : s≠0 := by
  intro hs
  subst s
  exact h rfl

theorem centered_scale {h c : Int} (hc : CenteredAt h c) : CenteredAt (4*h) (4*c) := by
  unfold CenteredAt at *
  rw [Int.mul_emod_mul_of_pos c (4*h) (by decide : (0:Int)<4),hc]
  omega

theorem board_half_step {m : Nat} (hm : 1≤m) : boardHalf (m+1)=4*boardHalf m := by
  have he : m=(m-1)+1 := by omega
  unfold boardHalf
  simp only [Nat.add_sub_cancel]
  have hp := Nat.pow_succ 4 (m-1)
  change 4^((m-1)+1)=4^(m-1)*4 at hp
  rw [←he] at hp
  rw [hp]
  omega

end K230Concrete
