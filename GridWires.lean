module
public import FiniteBoard
public import TapeGrid
public import ConcreteRoleExtensions
public section
namespace K230Verification

@[expose] def physicalColumn (k : Nat) (i : Int) (hi : InTape (2^k) i) : Int :=
  (tapeColumns k)[(i+(2^k : Nat)).toNat]'(by
    rw [tapeColumns_length]
    unfold InTape at hi
    have he := Int.toNat_of_nonneg (show 0≤i+(2^k : Nat) by omega)
    omega)
@[expose] def physicalRow (k t : Nat) (ht : t<2^k) : Int :=
  (tapeRows k)[t]'(by rw [tapeRows_length]; exact ht)

theorem physicalColumn_mem {k : Nat} {i : Int} (hi : InTape (2^k) i) :
    TapeOffset (k+2) (physicalColumn k i hi) :=
  tapeColumns_mem.mp (List.getElem_mem _)
theorem physicalRow_mem {k t : Nat} (ht : t<2^k) :
    TapeOffset (k+2) (physicalRow k t ht) ∧ 0<physicalRow k t ht :=
  tapeRows_mem.mp (List.getElem_mem _)

theorem logical_zero_in_tape (k : Nat) : InTape (2^k) 0 := by
  unfold InTape
  have h : 0<2^k := Nat.pow_pos (by decide)
  omega

theorem physicalColumn_zero (k : Nat) : physicalColumn k 0 (logical_zero_in_tape k)=1 := by
  simpa only [physicalColumn,Int.zero_add,Int.toNat_natCast] using tapeColumns_start k

theorem physicalColumn_strict {k : Nat} {i j : Int}
    (hi : InTape (2^k) i) (hj : InTape (2^k) j) (hij : i<j) :
    physicalColumn k i hi < physicalColumn k j hj := by
  apply List.pairwise_iff_getElem.mp (tapeColumns_strict k)
  unfold InTape at hi hj
  have he1 := Int.toNat_of_nonneg (show 0≤i+(2^k : Nat) by omega)
  have he2 := Int.toNat_of_nonneg (show 0≤j+(2^k : Nat) by omega)
  omega

theorem physicalRow_strict {k t u : Nat} (ht : t<2^k) (hu : u<2^k) (htu : t<u) :
    physicalRow k t ht < physicalRow k u hu :=
  List.pairwise_iff_getElem.mp (tapeRows_strict k) t u _ _ htu

/-- Finite, possibly very long, routing is a theorem about integer intervals,
    not a bounded scan. The guard supports nonblank column propagation. -/
theorem guarded_wire_constant {α : Type} {edge : Int → α} {P : α → Prop}
    {a b : Int} (hab : a≤b) (hstart : P (edge a))
    (hcopy : ∀ x, a<x → x≤b → P (edge (x-1)) → edge x=edge (x-1)) :
    edge b=edge a := by
  let len := (b-a).toNat
  have hlen : (len : Int)=b-a := Int.toNat_of_nonneg (by omega)
  have all : ∀ k : Nat, k≤len → edge (a+(k : Int))=edge a := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have he : a+(k+1 : Nat)-1=a+(k : Int) := by omega
      have hguard : P (edge (a+(k+1 : Nat)-1)) := by rw [he,hprev]; exact hstart
      have hstep := hcopy (a+(k+1 : Nat)) (by omega) (by omega) hguard
      rw [he,hprev] at hstep
      exact hstep
  have hlast := all len (Nat.le_refl len)
  have he : a+(len : Int)=b := by omega
  simpa only [he] using hlast

/-- A horizontal physical wire transmits a move across an arbitrary gap. -/
theorem horizontal_wire {tile : Int → Quad TMColor} {a b : Int} (hab : a<b)
    (hm : ∀ x, a≤x → x<b → (tile x).e=(tile (x+1)).w)
    (hc : ∀ x, a<x → x<b → (tile x).e=(tile x).w) :
    (tile b).w=(tile a).e := by
  have he : (tile (b-1)).e=(tile a).e := by
    apply guarded_wire_constant (edge:=fun x => (tile x).e) (a:=a) (b:=b-1) (P:=fun _ => True) (by omega) True.intro
    intro x hxa hxb _
    have hw := hm (x-1) (by omega) (by omega)
    have hx : x-1+1=x := by omega
    rw [hx] at hw
    exact (hc x hxa (by omega)).trans hw.symm
  have hw := hm (b-1) (by omega) (by omega)
  have hb : b-1+1=b := by omega
  rw [hb] at hw
  exact hw.symm.trans he

/-- A vertical physical wire carries the exact incoming nonblank symbol or
    head label through every intervening column-transmitter cell. -/
theorem vertical_wire {tile : Int → Quad TMColor} {a b : Int} (hab : a<b)
    (hm : ∀ y, a≤y → y<b → (tile y).n=(tile (y+1)).s)
    (hc : ∀ y, a<y → y<b → (tile y).s≠.blank → (tile y).n=(tile y).s)
    (hdata : (tile a).n≠.blank) : (tile b).s=(tile a).n := by
  have he : (tile (b-1)).n=(tile a).n := by
    apply guarded_wire_constant (edge:=fun y => (tile y).n) (a:=a) (b:=b-1) (P:=fun v => v≠TMColor.blank) (by omega) hdata
    intro y hya hyb hprev
    have hw := hm (y-1) (by omega) (by omega)
    have hy : y-1+1=y := by omega
    rw [hy] at hw
    have hs : (tile y).s≠.blank := by rw [←hw]; exact hprev
    exact (hc y hya (by omega) hs).trans hw.symm
  have hw := hm (b-1) (by omega) (by omega)
  have hb : b-1+1=b := by omega
  rw [hb] at hw
  exact hw.symm.trans he

#print axioms physicalColumn_zero
#print axioms guarded_wire_constant
#print axioms horizontal_wire
#print axioms vertical_wire
end K230Verification
