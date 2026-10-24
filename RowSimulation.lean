module
public import Std

/- New, independently written formalization of the row transition relation.
   This file does not import the unlicensed Rocq development. -/
public section
namespace K230Verification
inductive Dir where
  | left | right
  deriving DecidableEq, BEq
abbrev Machine := Nat → Bool → Option (Nat × Bool × Dir)
inductive VLabel where
  | symbol (a : Bool)
  | head (q : Nat) (a : Bool)
  deriving DecidableEq, BEq
abbrev HLabel := Option (Dir × Nat)

inductive Allowed (M : Machine) : VLabel → HLabel → VLabel → HLabel → Prop where
  | symbol (a) : Allowed M (.symbol a) none (.symbol a) none
  | right (q a q' b) (step : M q a = some (q', b, .right)) :
      Allowed M (.symbol b) (some (.right, q')) (.head q a) none
  | left (q a q' b) (step : M q a = some (q', b, .left)) :
      Allowed M (.symbol b) none (.head q a) (some (.left, q'))
  | mergeRight (q a) (entered : ∃ p c b, M p c = some (q,b,.right)) :
      Allowed M (.head q a) none (.symbol a) (some (.right, q))
  | mergeLeft (q a) (entered : ∃ p c b, M p c = some (q,b,.left)) :
      Allowed M (.head q a) (some (.left, q)) (.symbol a) none

/-- A tile with a head on its lower edge exists only if the machine can step. -/
theorem head_requires_transition {M : Machine} {q a n e w}
    (h : Allowed M n e (.head q a) w) : ∃ z, M q a = some z := by
  cases h with
  | right q a q' b step => exact ⟨_, step⟩
  | left q a q' b step => exact ⟨_, step⟩

/-- No tile has both an incoming and an outgoing right-move signal. -/
theorem right_emitter {M : Machine} {q n s w}
    (h : Allowed M n (some (.right,q)) s w) :
    ∃ p a b, s = .head p a ∧ n = .symbol b ∧
      M p a = some (q,b,.right) ∧ w = none := by
  cases h with
  | right p a q b step => exact ⟨p,a,b,rfl,rfl,step,rfl⟩

/-- A left-move signal can be emitted only by a genuine transition tile. -/
theorem left_emitter {M : Machine} {q n e s}
    (h : Allowed M n e s (some (.left,q))) :
    ∃ p a b, s = .head p a ∧ n = .symbol b ∧
      M p a = some (q,b,.left) ∧ e = none := by
  cases h with
  | left p a q b step => exact ⟨p,a,b,rfl,rfl,step,rfl⟩

/-- A head in the upper row is always the target of a move signal. -/
theorem head_requires_incoming {M : Machine} {q a e s w}
    (h : Allowed M (.head q a) e s w) :
    s = .symbol a ∧ ((w = some (.right,q) ∧ e = none) ∨
                       (e = some (.left,q) ∧ w = none)) := by
  cases h with
  | mergeRight q a entered => exact ⟨rfl, Or.inl ⟨rfl,rfl⟩⟩
  | mergeLeft q a entered => exact ⟨rfl, Or.inr ⟨rfl,rfl⟩⟩

/-- The horizontal edge indexed i lies between cells i and i+1. -/
@[expose] def RowAllowed (M : Machine) (north south : Int → VLabel) (edge : Int → HLabel) : Prop :=
  ∀ i, Allowed M (north i) (edge i) (south i) (edge (i-1))

theorem right_head_tile {M : Machine} {q a q' b n e w}
    (hs : M q a = some (q', b, .right))
    (ht : Allowed M n e (.head q a) w) :
    n = .symbol b ∧ e = some (.right,q') ∧ w = none := by
  cases ht with
  | right q a r c h =>
    have eq : (r,c,Dir.right) = (q',b,Dir.right) := Option.some.inj (h.symm.trans hs)
    cases eq
    exact ⟨rfl,rfl,rfl⟩
  | left q a r c h =>
    have eq : (r,c,Dir.left) = (q',b,Dir.right) := Option.some.inj (h.symm.trans hs)
    have : Dir.left = Dir.right := congrArg (fun z => z.2.2) eq
    contradiction

/-- No extra head can arise in a valid row: every upper head is adjacent to
    the unique lower head. This is a universal row fact, not a finite test. -/
theorem no_spurious_heads {M : Machine} {north south : Int → VLabel} {edge}
    {p : Int} (hr : RowAllowed M north south edge)
    (unique : ∀ i q a, south i = .head q a → i = p)
    {i q a} (hn : north i = .head q a) : i = p+1 ∨ i = p-1 := by
  have ht := hr i
  rw [hn] at ht
  rcases (head_requires_incoming ht).2 with h | h
  · rcases right_emitter (h.1 ▸ hr (i-1)) with ⟨r,c,b,hs,_,_,_⟩
    have hp := unique (i-1) r c hs
    left
    omega
  · have ht' := hr (i+1)
    have he : edge (i+1-1) = some (.left,q) := by simpa using h.1
    rw [he] at ht'
    rcases left_emitter ht' with ⟨r,c,b,hs,_,_,_⟩
    have hp := unique (i+1) r c hs
    right
    omega

theorem right_receiver {M : Machine} {q a n e}
    (ht : Allowed M n e (.symbol a) (some (.right,q))) :
    n = .head q a ∧ e = none := by
  cases ht with
  | mergeRight q a entered => exact ⟨rfl,rfl⟩

theorem upper_head_right {M : Machine} {north south : Int → VLabel} {edge}
    {p : Int} {q a q' b} (hr : RowAllowed M north south edge)
    (hp : south p = .head q a)
    (unique : ∀ i q a, south i = .head q a → i = p)
    (step : M q a = some (q',b,.right))
    {i r c} (hn : north i = .head r c) : i = p+1 ∧ r = q' := by
  have ht := hr p
  rw [hp] at ht
  have act := right_head_tile step ht
  have top := hr i
  rw [hn] at top
  rcases (head_requires_incoming top).2 with h | h
  · rcases right_emitter (h.1 ▸ hr (i-1)) with ⟨s,d,b',hs,_,_,_⟩
    have eq := unique (i-1) s d hs
    have hi : i = p+1 := by omega
    have ee : edge p = some (.right,r) := by simpa [eq] using h.1
    have rr : r = q' := by simpa using ee.symm.trans act.2.1
    exact ⟨hi,rr⟩
  · have ht' := hr (i+1)
    have he : edge (i+1-1) = some (.left,r) := by simpa using h.1
    rw [he] at ht'
    rcases left_emitter ht' with ⟨s,d,b',hs,_,_,ew⟩
    have eq := unique (i+1) s d hs
    have ep : edge (p-1) = some (.left,r) := by
      have i_eq : i = p-1 := by omega
      simpa [i_eq] using h.1
    rw [act.2.2] at ep
    contradiction

theorem symbol_lower {M : Machine} {n e a w}
    (h : Allowed M n e (.symbol a) w) :
    n = .symbol a ∨ ∃ q, n = .head q a := by
  cases h with
  | symbol a => exact Or.inl rfl
  | mergeRight q a entered => exact Or.inr ⟨q,rfl⟩
  | mergeLeft q a entered => exact Or.inr ⟨q,rfl⟩

/-- Every legal row above a single-head configuration is its genuine next
    configuration, for a rightward transition. -/
theorem row_right {M : Machine} {north south : Int → VLabel} {edge}
    (tape : Int → Bool) (p : Int) (q q' : Nat) (b : Bool)
    (hr : RowAllowed M north south edge)
    (hs : ∀ i, south i = if i = p then .head q (tape i) else .symbol (tape i))
    (step : M q (tape p) = some (q',b,.right)) :
    ∀ i, north i = if i = p then .symbol b else
      if i = p+1 then .head q' (tape i) else .symbol (tape i) := by
  have hp : south p = .head q (tape p) := by simpa using hs p
  have unique : ∀ i q a, south i = .head q a → i = p := by
    intro i r a h
    by_cases hi : i = p
    · exact hi
    · rw [hs i, ite_eq_right hi] at h
      contradiction
  have atp := hr p
  rw [hp] at atp
  have act := right_head_tile step atp
  intro i
  by_cases hi : i = p
  · subst i
    simpa using act.1
  · rw [ite_eq_right hi]
    have southi : south i = .symbol (tape i) := by simpa [hi] using hs i
    have hti := hr i
    rw [southi] at hti
    by_cases hin : i = p+1
    · rw [ite_eq_left hin]
      have back : i-1 = p := by omega
      rw [back, act.2.1] at hti
      exact (right_receiver hti).1
    · rw [ite_eq_right hin]
      rcases symbol_lower hti with same | ⟨r,hh⟩
      · exact same
      · have h := upper_head_right hr hp unique step hh
        exact False.elim (hin h.1)

def Dir.flip : Dir → Dir
  | .left => .right
  | .right => .left

def mirrorMachine (M : Machine) : Machine :=
  fun q a => (M q a).map (fun (r,b,d) => (r,b,d.flip))

def mirrorH : HLabel → HLabel :=
  Option.map (fun (d,q) => (d.flip,q))

theorem reflect_allowed {M : Machine} {n e s w}
    (h : Allowed M n e s w) :
    Allowed (mirrorMachine M) n (mirrorH w) s (mirrorH e) := by
  cases h with
  | symbol a => exact .symbol a
  | right q a r b hs =>
    exact .left q a r b (by simp [mirrorMachine,hs,Dir.flip])
  | left q a r b hs =>
    exact .right q a r b (by simp [mirrorMachine,hs,Dir.flip])
  | mergeRight q a entered =>
    obtain ⟨p,c,b,h⟩ := entered
    exact .mergeLeft q a ⟨p,c,b,by simp [mirrorMachine,h,Dir.flip]⟩
  | mergeLeft q a entered =>
    obtain ⟨p,c,b,h⟩ := entered
    exact .mergeRight q a ⟨p,c,b,by simp [mirrorMachine,h,Dir.flip]⟩

theorem reflect_row {M : Machine} {north south : Int → VLabel} {edge}
    (hr : RowAllowed M north south edge) :
    RowAllowed (mirrorMachine M) (fun i => north (-i)) (fun i => south (-i))
      (fun i => mirrorH (edge (-i-1))) := by
  intro i
  have h := reflect_allowed (hr (-i))
  have eq : -(i-1)-1 = -i := by omega
  simpa [eq] using h

/-- The reflected row theorem handles every leftward transition as well. -/
theorem row_left {M : Machine} {north south : Int → VLabel} {edge}
    (tape : Int → Bool) (p : Int) (q q' : Nat) (b : Bool)
    (hr : RowAllowed M north south edge)
    (hs : ∀ i, south i = if i = p then .head q (tape i) else .symbol (tape i))
    (step : M q (tape p) = some (q',b,.left)) :
    ∀ i, north i = if i = p then .symbol b else
      if i = p-1 then .head q' (tape i) else .symbol (tape i) := by
  have hsr : ∀ i, south (-i) = if i = -p then .head q (tape (-i)) else .symbol (tape (-i)) := by
    intro i
    have eq : (-i = p) ↔ (i = -p) := by omega
    simpa [eq] using hs (-i)
  have stepr : mirrorMachine M q ((fun i => tape (-i)) (-p)) = some (q',b,.right) := by
    simp [mirrorMachine,step,Dir.flip]
  have h := row_right (fun i => tape (-i)) (-p) q q' b (reflect_row hr) hsr stepr
  intro i
  have eq : (-i = -p) ↔ (i = p) := by omega
  have eq' : (-i = -p+1) ↔ (i = p-1) := by omega
  simpa [eq,eq'] using h (-i)

@[expose] def configRow (tape : Int → Bool) (p : Int) (q : Nat) (i : Int) : VLabel :=
  if i = p then .head q (tape i) else .symbol (tape i)

theorem row_exists_right {M : Machine} (tape : Int → Bool) (p : Int) (q q' : Nat) (b : Bool)
    (step : M q (tape p) = some (q',b,.right)) :
    ∃ north edge, RowAllowed M north (configRow tape p q) edge := by
  refine ⟨(fun i => if i = p then .symbol b else
    if i = p+1 then .head q' (tape i) else .symbol (tape i)),
    (fun i => if i = p then some (.right,q') else none), ?_⟩
  intro i
  by_cases hi : i = p
  · subst i
    have hp : p-1 ≠ p := by omega
    simp only [configRow, ite_eq_left, hp]
    exact .right q (tape p) q' b step
  · have back : (i-1 = p) ↔ (i = p+1) := by omega
    by_cases hn : i = p+1
    · have hb : i-1 = p := by omega
      simp only [configRow, ite_eq_right hi, ite_eq_left hn, ite_eq_left hb]
      exact .mergeRight q' (tape i) ⟨q,tape p,b,step⟩
    · simp only [configRow, hi, hn, back]
      exact .symbol (tape i)

theorem row_exists_left {M : Machine} (tape : Int → Bool) (p : Int) (q q' : Nat) (b : Bool)
    (step : M q (tape p) = some (q',b,.left)) :
    ∃ north edge, RowAllowed M north (configRow tape p q) edge := by
  refine ⟨(fun i => if i = p then .symbol b else
    if i = p-1 then .head q' (tape i) else .symbol (tape i)),
    (fun i => if i = p-1 then some (.left,q') else none), ?_⟩
  intro i
  have back : (i-1 = p-1) ↔ (i = p) := by omega
  by_cases hi : i = p
  · subst i
    have hp : p ≠ p-1 := by omega
    simp only [configRow, hp, ite_eq_left]
    exact .left q (tape p) q' b step
  · by_cases hn : i = p-1
    · have hb : i-1 ≠ p-1 := by omega
      simp only [configRow, ite_eq_right hi, ite_eq_left hn, ite_eq_right hb]
      exact .mergeLeft q' (tape i) ⟨q,tape p,b,step⟩
    · simp only [configRow, hi, hn, back]
      exact .symbol (tape i)

/-- Exact one-step existential equivalence for the row relation. -/
theorem row_exists_iff_step {M : Machine} (tape : Int → Bool) (p : Int) (q : Nat) :
    (∃ north edge, RowAllowed M north (configRow tape p q) edge) ↔
      ∃ z, M q (tape p) = some z := by
  constructor
  · rintro ⟨north,edge,h⟩
    have hp := h p
    simp only [configRow, ite_true] at hp
    exact head_requires_transition hp
  · rintro ⟨⟨r,b,d⟩,h⟩
    cases d with
    | right => exact row_exists_right tape p q r b h
    | left => exact row_exists_left tape p q r b h

#print axioms row_exists_iff_step
#print axioms row_right
#print axioms row_left
end K230Verification
