module
public import ConcreteWitness
public import ConcreteCoreTable
public import GlobalRecognition
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace K230Concrete

open K230PhaseHierarchy

theorem boardVariant_bound (k : Fin 156) : boardVariant k < 4 := by
  have h := Wang156.parity_bounds k
  dsimp [boardVariant]
  omega

@[expose] def redBoard (n v x y : Nat) : Fin 156 :=
  expanded (2*n)
    (boardCore v (x/squareSize n) (y/squareSize n))
    (x%squareSize n) (y%squareSize n)

theorem expanded_core (n : Nat) (k : Fin 156) (p q r s : Nat)
    (hp : p<5) (hq : q<5) (hr : r<squareSize n) (hs : s<squareSize n) :
    expanded (2*n+3) k (squareSize n*(p+2)+r) (squareSize n*(q+2)+s) =
      expanded (2*n) (boardCore (boardVariant k) p q) r s := by
  have h := expanded_add (2*n) 3 k (p+2) (q+2) r s hr hs
  rw [core_identity k p q hp hq] at h
  exact h

theorem redBoard_core_identity (n : Nat) (k : Fin 156) (x y : Nat)
    (hx : x ≤ 4*squareSize n) (hy : y ≤ 4*squareSize n) :
    expanded (2*n+3) k (2*squareSize n+x) (2*squareSize n+y) =
      redBoard n (boardVariant k) x y := by
  have hw := squareSize_pos n
  have hxd : x/squareSize n < 5 := (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
  have hyd : y/squareSize n < 5 := (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
  have hxe := Nat.div_add_mod x (squareSize n)
  have hye := Nat.div_add_mod y (squareSize n)
  have hcX : squareSize n*(x/squareSize n+2)+x%squareSize n = 2*squareSize n+x := by
    simp only [Nat.mul_add]
    omega
  have hcY : squareSize n*(y/squareSize n+2)+y%squareSize n = 2*squareSize n+y := by
    simp only [Nat.mul_add]
    omega
  have h := expanded_core n k (x/squareSize n) (y/squareSize n)
    (x%squareSize n) (y%squareSize n) hxd hyd (Nat.mod_lt x hw) (Nat.mod_lt y hw)
  simpa only [hcX,hcY,redBoard] using h

theorem phaseScale_width (n : Nat) : K230PhaseHierarchy.scale n = (width n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [K230PhaseHierarchy.scale,width,ih]; omega

theorem supertile_expanded (n : Nat) (k : Fin 156) (bits : Nat → Offset) :
    supertile Wang156.exactSystem n k bits = expanded n k
      (binaryOffset n bits).1.toNat (binaryOffset n bits).2.toNat := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    have hb := binaryOffset_bounds n (shifted bits)
    have hx := (bits 0).1.isLt
    have hy := (bits 0).2.isLt
    have hxn : (2*(binaryOffset n (shifted bits)).1 + ((bits 0).1.val : Int)).toNat =
        2*(binaryOffset n (shifted bits)).1.toNat + (bits 0).1.val := by omega
    have hyn : (2*(binaryOffset n (shifted bits)).2 + ((bits 0).2.val : Int)).toNat =
        2*(binaryOffset n (shifted bits)).2.toNat + (bits 0).2.val := by omega
    have hxd : (2*(binaryOffset n (shifted bits)).1.toNat + (bits 0).1.val)/2 =
        (binaryOffset n (shifted bits)).1.toNat := by omega
    have hyd : (2*(binaryOffset n (shifted bits)).2.toNat + (bits 0).2.val)/2 =
        (binaryOffset n (shifted bits)).2.toNat := by omega
    have hxr : (2*(binaryOffset n (shifted bits)).1.toNat + (bits 0).1.val)%2 = (bits 0).1.val := by omega
    have hyr : (2*(binaryOffset n (shifted bits)).2.toNat + (bits 0).2.val)%2 = (bits 0).2.val := by omega
    change Wang156.sigmaTile (supertile Wang156.exactSystem n k (shifted bits)) (bits 0) = _
    rw [ih]
    simp only [binaryOffset, hxn, hyn, expanded, hxd, hyd, hxr, hyr]
    rfl

theorem exact_expanded_occurs (T : K230PhaseHierarchy.Point → Fin 156)
    (hT : wangValid Wang156.presentation T) (n : Nat) :
    ∃ (k : Fin 156) (b : K230PhaseHierarchy.Point), ∀ x y : Nat, x<width n → y<width n →
      T (b.1+(x:Int),b.2+(y:Int)) = expanded n k x y := by
  obtain ⟨k,b,hb⟩ := Wang156.exact_arbitrary_supertile T hT n
  change Fin 156 at k
  refine ⟨k,b,?_⟩
  intro x y hx hy
  have hs := phaseScale_width n
  obtain ⟨bits,hbits⟩ := binaryOffset_surjective n (x:Int) (y:Int) (by omega) (by omega)
  have h := hb bits
  have he := supertile_expanded n k bits
  have hh := h.trans he
  rw [hbits] at hh
  simpa [Wang156.exactSystem,recognizedSystem,Wang156.presentation] using hh

theorem arbitrary_redBoard_occurs (T : K230PhaseHierarchy.Point → Fin 156)
    (hT : wangValid Wang156.presentation T) (n : Nat) :
    ∃ (v : Nat) (b : K230PhaseHierarchy.Point), v<4 ∧ ∀ x y : Nat, x≤4*squareSize n → y≤4*squareSize n →
      T (b.1+(x:Int),b.2+(y:Int)) = redBoard n v x y := by
  obtain ⟨k,b,hb⟩ := exact_expanded_occurs T hT (2*n+3)
  refine ⟨boardVariant k, (b.1+2*squareSize n,b.2+2*squareSize n), boardVariant_bound k, ?_⟩
  intro x y hx hy
  have hw := squareSize_pos n
  have hsize : width (2*n+3) = 8*squareSize n := by
    rw [width_add]
    change width (2*n)*8 = 8*width (2*n)
    omega
  have hxb : 2*squareSize n+x < width (2*n+3) := by omega
  have hyb : 2*squareSize n+y < width (2*n+3) := by omega
  have h := hb (2*squareSize n+x) (2*squareSize n+y) hxb hyb
  rw [redBoard_core_identity n k x y hx hy] at h
  simpa [Int.add_assoc] using h

theorem squareSize_power (n : Nat) : squareSize n = 4^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [squareSize_step,ih,Nat.pow_succ]; omega

theorem representative_variant (v : Nat) (hv : v<4) :
    boardVariant (coreRepresentative v) = v := by
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

theorem redBoard_as_expanded (n v x y : Nat) (hv : v<4)
    (hx : x≤4*squareSize n) (hy : y≤4*squareSize n) :
    redBoard n v x y = expanded (2*n+3) (coreRepresentative v)
      (2*squareSize n+x) (2*squareSize n+y) := by
  have h := redBoard_core_identity n (coreRepresentative v) x y hx hy
  rw [representative_variant v hv] at h
  exact h.symm

theorem expanded_low_two (n : Nat) (k : Fin 156) (x y : Nat) :
    expanded (n+2) k x y = expanded 2 (expanded n k (x/4) (y/4)) (x%4) (y%4) := by
  have h := expanded_add 2 n k (x/4) (y/4) (x%4) (y%4)
    (by change x%4<4; omega) (by change y%4<4; omega)
  have hx := Nat.div_add_mod x 4
  have hy := Nat.div_add_mod y 4
  have hn : 2+n=n+2 := by omega
  change expanded (2+n) k (4*(x/4)+x%4) (4*(y/4)+y%4) = _ at h
  simpa only [hx,hy,hn] using h

theorem redBoard_step (n v x y : Nat) (hv : v<4)
    (hx : x≤4*squareSize (n+1)) (hy : y≤4*squareSize (n+1)) :
    redBoard (n+1) v x y = expanded 2 (redBoard n v (x/4) (y/4)) (x%4) (y%4) := by
  have hs := squareSize_step n
  have hxd : x/4≤4*squareSize n := by omega
  have hyd : y/4≤4*squareSize n := by omega
  have hxq : (2*squareSize (n+1)+x)/4 = 2*squareSize n+x/4 := by omega
  have hyq : (2*squareSize (n+1)+y)/4 = 2*squareSize n+y/4 := by omega
  have hxr : (2*squareSize (n+1)+x)%4=x%4 := by omega
  have hyr : (2*squareSize (n+1)+y)%4=y%4 := by omega
  have hn : 2*(n+1)+3 = (2*n+3)+2 := by omega
  rw [redBoard_as_expanded (n+1) v x y hv hx hy,hn,expanded_low_two,hxq,hyq,hxr,hyr]
  rw [←redBoard_as_expanded n v (x/4) (y/4) hv hxd hyd]

end K230Concrete

#print axioms K230Concrete.core_identity
#print axioms K230Concrete.redBoard_core_identity
#print axioms K230Concrete.arbitrary_redBoard_occurs
