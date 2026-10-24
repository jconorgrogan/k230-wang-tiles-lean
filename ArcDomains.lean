module
public import PatchSemantics
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Wang156
structure Square where
  bl : Nat
  br : Nat
  tl : Nat
  tr : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

@[expose] def squareEq (a b : Square) : Bool := a.bl == b.bl && a.br == b.br && a.tl == b.tl && a.tr == b.tr

theorem squareEq_iff (a b : Square) : squareEq a b = true ↔ a = b := by
  cases a; cases b
  simp [squareEq, Square.mk.injEq, and_assoc]

@[expose] def squareOf (p : Patch) : Square := ⟨(p 2 2).val,(p 3 2).val,(p 2 3).val,(p 3 3).val⟩
@[expose] def imageSquare (k : Nat) : Square := ⟨sigma k 0,sigma k 1,sigma k 2,sigma k 3⟩
@[expose] abbrev Domains := Nat → Nat → List Nat

@[expose] def initialDomains (b : Square) : Domains := fun i j =>
  if i = 2 ∧ j = 2 then [b.bl]
  else if i = 3 ∧ j = 2 then [b.br]
  else if i = 2 ∧ j = 3 then [b.tl]
  else if i = 3 ∧ j = 3 then [b.tr]
  else List.range 156

@[expose] def Contains (p : Patch) (d : Domains) : Prop :=
  ∀ i j, i < 6 → j < 6 → (p i j).val ∈ d i j

structure ArcStep where
  i : Nat
  j : Nat
  s : Nat
  deriving Repr, Inhabited

@[expose] def nx (r : ArcStep) : Nat := if r.s = 1 then r.i+1 else if r.s = 3 then r.i-1 else r.i
@[expose] def ny (r : ArcStep) : Nat := if r.s = 0 then r.j+1 else if r.s = 2 then r.j-1 else r.j

@[expose] def ArcValid (r : ArcStep) : Prop := r.i < 6 ∧ r.j < 6 ∧ r.s < 4 ∧
  (if r.s = 0 then r.j+1 < 6 else if r.s = 1 then r.i+1 < 6 else if r.s = 2 then 0 < r.j else 0 < r.i)
@[expose] instance (r : ArcStep) : Decidable (ArcValid r) := by unfold ArcValid; infer_instance

@[expose] def prune (d : Domains) (r : ArcStep) : Domains := fun i j =>
  if i = r.i ∧ j = r.j then
    (d i j).filter fun k => (d (nx r) (ny r)).any fun u => side (tile k) r.s == side (tile u) ((r.s+2)%4)
  else d i j

@[expose] def runDomains (d : Domains) (rs : List ArcStep) : Domains := rs.foldl prune d

theorem contains_initial (p : Patch) : Contains p (initialDomains (squareOf p)) := by
  intro i j hi hj
  simp only [initialDomains, squareOf]
  split
  next h => obtain ⟨rfl,rfl⟩ := h; simp
  next h =>
    split
    next h => obtain ⟨rfl,rfl⟩ := h; simp
    next h =>
      split
      next h => obtain ⟨rfl,rfl⟩ := h; simp
      next h =>
        split
        next h => obtain ⟨rfl,rfl⟩ := h; simp
        next => exact List.mem_range.mpr (p i j).isLt

theorem arc_neighbor (p : Patch) (hv : Valid 6 p) (r : ArcStep) (hr : ArcValid r) :
    nx r < 6 ∧ ny r < 6 ∧
    side (tile (p r.i r.j).val) r.s = side (tile (p (nx r) (ny r)).val) ((r.s+2)%4) := by
  obtain ⟨hi,hj,hs,hb⟩ := hr
  by_cases h0 : r.s = 0
  · have hn : r.j+1 < 6 := by simpa [h0] using hb
    simpa [nx,ny,h0,side] using And.intro hi (And.intro hn (hv.2 r.i r.j hi hn))
  by_cases h1 : r.s = 1
  · have hn : r.i+1 < 6 := by simpa [h0,h1] using hb
    simpa [nx,ny,h0,h1,side] using And.intro hn (And.intro hj (hv.1 r.i r.j hn hj))
  by_cases h2 : r.s = 2
  · have hpos : 0 < r.j := by simpa [h0,h1,h2] using hb
    have he := hv.2 r.i (r.j-1) hi (by omega)
    have he' : (tile (p r.i r.j).val).s = (tile (p r.i (r.j-1)).val).n := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r.j)] using he.symm
    refine ⟨by simpa [nx,h2], by simp [ny,h2]; omega, ?_⟩
    simpa [nx,ny,h2,side] using he'
  · have h3 : r.s = 3 := by omega
    have hpos : 0 < r.i := by simpa [h0,h1,h2] using hb
    have he := hv.1 (r.i-1) r.j (by omega) hj
    have he' : (tile (p r.i r.j).val).w = (tile (p (r.i-1) r.j).val).e := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r.i)] using he.symm
    refine ⟨by simp [nx,h3]; omega, by simpa [ny,h3], ?_⟩
    simpa [nx,ny,h3,side] using he'

theorem prune_sound (p : Patch) (hv : Valid 6 p) (d : Domains) (r : ArcStep)
    (hc : Contains p d) (hr : ArcValid r) : Contains p (prune d r) := by
  intro i j hi hj
  simp only [prune]
  split
  next he =>
    obtain ⟨rfl,rfl⟩ := he
    obtain ⟨hnx,hny,hm⟩ := arc_neighbor p hv r hr
    refine List.mem_filter.mpr ⟨hc _ _ hi hj, ?_⟩
    exact List.any_eq_true.mpr ⟨(p (nx r) (ny r)).val, hc _ _ hnx hny, by simpa using hm⟩
  next => exact hc i j hi hj

theorem run_sound (p : Patch) (hv : Valid 6 p) (d : Domains) (rs : List ArcStep)
    (hc : Contains p d) (hr : ∀ r ∈ rs, ArcValid r) : Contains p (runDomains d rs) := by
  induction rs generalizing d with
  | nil => exact hc
  | cons r rs ih =>
    exact ih (prune d r) (prune_sound p hv d r hc (hr r (by simp))) (fun s hs => hr s (by simp [hs]))

structure ArcCertificate where
  block : Square
  steps : List ArcStep
  i : Nat
  j : Nat
  deriving Repr, Inhabited

@[expose] def checkArc (c : ArcCertificate) : Bool :=
  c.steps.all (fun r => decide (ArcValid r)) &&
  decide (c.i < 6 ∧ c.j < 6) &&
  ((runDomains (initialDomains c.block) c.steps) c.i c.j).isEmpty

theorem arc_no_square (c : ArcCertificate) (h : checkArc c = true)
    (p : Patch) (hv : Valid 6 p) : squareOf p ≠ c.block := by
  intro heq
  have hh : c.steps.all (fun r => decide (ArcValid r)) = true ∧
      decide (c.i < 6 ∧ c.j < 6) = true ∧
      ((runDomains (initialDomains c.block) c.steps) c.i c.j).isEmpty = true := by
    simpa only [checkArc, Bool.and_eq_true, and_assoc] using h
  have hrs : ∀ r ∈ c.steps, ArcValid r := fun r hr => of_decide_eq_true (List.all_eq_true.mp hh.1 r hr)
  obtain ⟨hi,hj⟩ := of_decide_eq_true hh.2.1
  have hc : Contains p (initialDomains c.block) := heq ▸ contains_initial p
  have hout := run_sound p hv (initialDomains c.block) c.steps hc hrs c.i c.j hi hj
  have hempty : (runDomains (initialDomains c.block) c.steps) c.i c.j = [] := by simpa using hh.2.2
  simpa [hempty] using hout
end Wang156
