module
public import Recognizability
public import BaseFacts
public import PhaseHierarchy
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Wang156
open K230PhaseHierarchy

@[expose] def quadrant (r : Offset) : Fin 4 :=
  ⟨r.1.val + 2*r.2.val, by have hx := r.1.isLt; have hy := r.2.isLt; omega⟩

@[expose] def sigmaTile (k : Fin 156) (r : Offset) : Fin 156 :=
  ⟨sigma k.val (quadrant r).val, sigma_closed k (quadrant r)⟩

@[expose] def presentation : WangPresentation where
  Tile := Fin 156
  Color := Nat
  north k := (tile k.val).n
  east k := (tile k.val).e
  south k := (tile k.val).s
  west k := (tile k.val).w
  sigma := sigmaTile

theorem int_induction (P : Int → Prop) (h0 : P 0)
    (hp : ∀ z, P z → P (z+1)) (hm : ∀ z, P z → P (z-1)) : ∀ z, P z := by
  intro z
  cases z with
  | ofNat n =>
    induction n with
    | zero => exact h0
    | succ n ih => exact hp n ih
  | negSucc n =>
    induction n with
    | zero => exact hm 0 h0
    | succ n ih => exact hm (Int.negSucc n) ih

theorem constant_line (f : Int → Nat) (h : ∀ z, f z = f (z+1)) :
    ∀ z, f z = f 0 := by
  apply int_induction
  · rfl
  · intro z hz; exact (h z).symm.trans hz
  · intro z hz
    have hh := h (z-1)
    have he : z-1+1 = z := by omega
    rw [he] at hh
    exact hh.trans hz

theorem parity_line (f : Int → Nat) (h : ∀ z, f z + f (z+1) = 1) :
    ∀ z, (f z : Int) = (z + (f 0 : Int)) % 2 := by
  apply int_induction
  · have hh := h 0; omega
  · intro z hz
    have hh := h z
    omega
  · intro z hz
    have hh := h (z-1)
    have he : z-1+1 = z := by omega
    rw [he] at hh
    omega

@[expose] def globalPhase (T : Tiling (Fin 156)) : Offset :=
  (⟨(tile (T (0,0)).val).px, (parity_bounds (T (0,0))).1⟩,
   ⟨(tile (T (0,0)).val).py, (parity_bounds (T (0,0))).2⟩)

theorem parity_coordinates (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (x y : Int) :
    ((tile (T (x,y)).val).px : Int) = (x + (tile (T (0,0)).val).px) % 2 ∧
    ((tile (T (x,y)).val).py : Int) = (y + (tile (T (0,0)).val).py) % 2 := by
  have hx := parity_line (fun z => (tile (T (z,y)).val).px)
    (fun z => (horizontal_parity _ _ (h (z,y)).1).1) x
  have hy := parity_line (fun z => (tile (T (x,z)).val).py)
    (fun z => (vertical_parity _ _ (h (x,z)).2).2) y
  have cx := constant_line (fun z => (tile (T (0,z)).val).px)
    (fun z => (vertical_parity _ _ (h (0,z)).2).1) y
  have cy := constant_line (fun z => (tile (T (z,0)).val).py)
    (fun z => (horizontal_parity _ _ (h (z,0)).1).2) x
  rw [cx] at hx
  rw [cy] at hy
  exact ⟨hx,hy⟩

theorem aligned_origin (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (q : Point) :
    (tile (T (place (globalPhase T) q zeroOffset)).val).px = 0 ∧
    (tile (T (place (globalPhase T) q zeroOffset)).val).py = 0 := by
  have hh := parity_coordinates T h
    (place (globalPhase T) q zeroOffset).1 (place (globalPhase T) q zeroOffset).2
  simp only [place, globalPhase, zeroOffset] at hh ⊢
  omega

@[expose] def window (T : Tiling (Fin 156)) (b : Point) : Patch :=
  fun i j => T (b.1 + (i : Int) - 2, b.2 + (j : Int) - 2)

theorem window_valid (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (b : Point) (n : Nat) : Valid n (window T b) := by
  constructor
  · intro i j _ _
    have hh := (h (b.1 + (i : Int) - 2, b.2 + (j : Int) - 2)).1
    have he : (b.1 + ((i+1 : Nat) : Int) - 2, b.2 + (j : Int) - 2) =
        (b.1 + (i : Int) - 2 + 1, b.2 + (j : Int) - 2) := by
      apply Prod.ext <;> dsimp <;> omega
    change (tile (T (b.1 + (i : Int) - 2, b.2 + (j : Int) - 2)).val).e =
      (tile (T (b.1 + ((i+1 : Nat) : Int) - 2, b.2 + (j : Int) - 2)).val).w
    rw [he]
    exact hh
  · intro i j _ _
    have hh := (h (b.1 + (i : Int) - 2, b.2 + (j : Int) - 2)).2
    have he : (b.1 + (i : Int) - 2, b.2 + ((j+1 : Nat) : Int) - 2) =
        (b.1 + (i : Int) - 2, b.2 + (j : Int) - 2 + 1) := by
      apply Prod.ext <;> dsimp <;> omega
    change (tile (T (b.1 + (i : Int) - 2, b.2 + (j : Int) - 2)).val).n =
      (tile (T (b.1 + (i : Int) - 2, b.2 + ((j+1 : Nat) : Int) - 2)).val).s
    rw [he]
    exact hh

theorem window_center (T : Tiling (Fin 156)) (b : Point) : window T b 2 2 = T b := by
  simp [window]

theorem window_micro (T : Tiling (Fin 156)) (eps : Offset) (q : Point) (r : Offset) :
    window T (place eps q zeroOffset) (blockX 0 0 (quadrant r).val)
      (blockY 0 0 (quadrant r).val) = T (place eps q r) := by
  have hx := r.1.isLt
  have hy := r.2.isLt
  have hmod : (r.1.val + 2*r.2.val)%2 = r.1.val := by omega
  have hdiv : (r.1.val + 2*r.2.val)/2 = r.2.val := by omega
  simp only [window, blockX, blockY, macroX, macroY, quadrant, place, zeroOffset]
  congr 1
  apply Prod.ext <;> dsimp <;> omega

theorem global_D1 (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (q : Point) : ∃ k, isBlock presentation T (globalPhase T) q k := by
  have ha := aligned_origin T h q
  have hx : (tile (window T (place (globalPhase T) q zeroOffset) 2 2).val).px = 0 := by
    simpa only [window_center] using ha.1
  have hy : (tile (window T (place (globalPhase T) q zeroOffset) 2 2).val).py = 0 := by
    simpa only [window_center] using ha.2
  obtain ⟨k,hk⟩ := D1_six (window T (place (globalPhase T) q zeroOffset))
    (window_valid T h _ 6) hx hy
  refine ⟨k, fun r => ?_⟩
  apply Fin.ext
  have hh := hk (quadrant r).val (quadrant r).isLt
  rw [window_micro] at hh
  exact hh

theorem block_boundary_h (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (eps : Offset) (q : Point) (a b : Fin 156)
    (ha : isBlock presentation T eps q a)
    (hb : isBlock presentation T eps (q.1+1,q.2) b) (y : Fin 2) :
    (tile (sigma a.val (1 + 2*y.val))).e = (tile (sigma b.val (2*y.val))).w := by
  have hh := (h (place eps q (1,y))).1
  have he : ((place eps q (1,y)).1+1, (place eps q (1,y)).2) =
      place eps (q.1+1,q.2) (0,y) := by
    apply Prod.ext <;> dsimp [place] <;> omega
  change (tile (T (place eps q (1,y))).val).e =
    (tile (T ((place eps q (1,y)).1+1, (place eps q (1,y)).2)).val).w at hh
  rw [he,ha (1,y),hb (0,y)] at hh
  simpa [presentation,sigmaTile,quadrant] using hh

theorem block_boundary_v (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (eps : Offset) (q : Point) (a b : Fin 156)
    (ha : isBlock presentation T eps q a)
    (hb : isBlock presentation T eps (q.1,q.2+1) b) (x : Fin 2) :
    (tile (sigma a.val (x.val + 2))).n = (tile (sigma b.val x.val)).s := by
  have hh := (h (place eps q (x,1))).2
  have he : ((place eps q (x,1)).1, (place eps q (x,1)).2+1) =
      place eps (q.1,q.2+1) (x,0) := by
    apply Prod.ext <;> dsimp [place] <;> omega
  change (tile (T (place eps q (x,1))).val).n =
    (tile (T ((place eps q (x,1)).1, (place eps q (x,1)).2+1)).val).s at hh
  rw [he,ha (x,1),hb (x,0)] at hh
  exact hh

theorem global_D2h (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (q : Point) (a b : Fin 156)
    (ha : isBlock presentation T (globalPhase T) q a)
    (hb : isBlock presentation T (globalPhase T) (q.1+1,q.2) b) :
    (tile a.val).e = (tile b.val).w := by
  apply reflect_horizontal a b
  · exact block_boundary_h T h _ q a b ha hb 0
  · exact block_boundary_h T h _ q a b ha hb 1

theorem global_D2v (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (q : Point) (a b : Fin 156)
    (ha : isBlock presentation T (globalPhase T) q a)
    (hb : isBlock presentation T (globalPhase T) (q.1,q.2+1) b) :
    (tile a.val).n = (tile b.val).s := by
  apply reflect_vertical a b
  · exact block_boundary_v T h _ q a b ha hb 0
  · exact block_boundary_v T h _ q a b ha hb 1

@[expose] def recognition : Recognition presentation where
  phase := globalPhase
  D1 := global_D1
  D2h := global_D2h
  D2v := global_D2v

@[expose] noncomputable def exactSystem : System := recognizedSystem presentation recognition

theorem exact_desubstitution (T : Tiling (Fin 156)) (h : wangValid presentation T) :
    ∃ eps U, wangValid presentation U ∧
      ∀ q r, T (place eps q r) = sigmaTile (U q) r :=
  exactSystem.desubstitute T h

theorem exact_arbitrary_supertile (T : Tiling (Fin 156)) (h : wangValid presentation T)
    (n : Nat) : ∃ k b, HasSupertile exactSystem T n k b :=
  contains_rectangular_supertile exactSystem ⟨T,h⟩ n

#print axioms parity_coordinates
#print axioms global_D1
#print axioms global_D2h
#print axioms global_D2v
#print axioms exact_desubstitution
#print axioms exact_arbitrary_supertile
end Wang156
