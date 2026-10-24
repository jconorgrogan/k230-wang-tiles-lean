module
public import BoardAdjacency
public section
set_option maxHeartbeats 0
namespace K230Verification

/-- Maximal proper lower boards are the pieces pasted in one induction step. -/
@[expose] def ChildOwns (n : Nat) (b : RedSquare) (p : Int × Int) : Prop :=
  LowerSquareInside n b ∧ InRedSquare b p ∧
    ∀ a : RedSquare, LowerSquareInside n a → InRedSquare a p → a.level≤b.level

theorem nat_maximal_bounded (P : Nat → Prop) (N : Nat) (h : ∃ n, n<N ∧ P n) :
    ∃ n, n<N ∧ P n ∧ ∀ m, m<N → P m → m≤n := by
  classical
  induction N with
  | zero => obtain ⟨n,hn,_⟩ := h; omega
  | succ N ih =>
    by_cases hn : P N
    · exact ⟨N,by omega,hn,fun m hm _ => by omega⟩
    · have hp : ∃ n, n<N ∧ P n := by
        obtain ⟨n,hb,hp⟩ := h
        refine ⟨n,?_,hp⟩
        by_cases he : n=N
        · subst n; exact False.elim (hn hp)
        · omega
      obtain ⟨n,hb,hp,hm⟩ := ih hp
      refine ⟨n,by omega,hp,?_⟩
      intro m hm' hpm
      have hmn : m<N := by
        by_cases he : m=N
        · subst m; exact False.elim (hn hpm)
        · omega
      exact hm m hmn hpm

theorem covered_has_maximal_child {n : Nat} {r s : Int}
    (hr : -(boardHalf n:Int)<r ∧ r<(boardHalf n:Int))
    (hc : BoardCovered n r s) : ∃ b : RedSquare, ChildOwns n b (r,s) := by
  obtain ⟨b,hb,hp⟩ := (boardCovered_iff_lower_square hr).mp hc
  let P : Nat → Prop := fun m => ∃ a : RedSquare,
    a.level=m ∧ LowerSquareInside n a ∧ InRedSquare a (r,s)
  have hex : ∃ m, m<n ∧ P m := ⟨b.level,hb.1,b,rfl,hb,hp⟩
  obtain ⟨m,hm,⟨a,he,ha,hap⟩,hmax⟩ := nat_maximal_bounded P n hex
  refine ⟨a,ha,hap,?_⟩
  intro c hcn hcp
  have h := hmax c.level hcn.1 ⟨c,rfl,hcn,hcp⟩
  omega

theorem strictly_inside_contains {a b : RedSquare} {p : Int × Int}
    (h : StrictlyInside a b) (hp : InRedSquare a p) : InRedSquare b p := by
  unfold StrictlyInside at h
  unfold InRedSquare ClosedInterval at hp ⊢
  omega

theorem maximal_child_unique {n : Nat} {a b : RedSquare} {p : Int × Int}
    (ha : ChildOwns n a p) (hb : ChildOwns n b p) :
    a.level=b.level ∧ a.cx=b.cx ∧ a.cy=b.cy := by
  have hl : a.level=b.level := Nat.le_antisymm (hb.2.2 a ha.1 ha.2.1) (ha.2.2 b hb.1 hb.2.1)
  exact ⟨hl,same_level_square_centers hl ha.2.1 hb.2.1⟩

/-- The maximal-child owner is constant on the whole closed child square,
    so its recursively constructed patch is a genuine piece, not a cellwise selection. -/
theorem maximal_child_stable {n : Nat} {b : RedSquare} {p q : Int × Int}
    (hb : ChildOwns n b p) (hq : InRedSquare b q) : ChildOwns n b q := by
  refine ⟨hb.1,hq,?_⟩
  intro a ha haq
  by_cases hle : a.level≤b.level
  · exact hle
  · have hlt : b.level<a.level := by omega
    have hi := red_squares_strictly_nested hlt hq haq
    have hap := strictly_inside_contains hi hb.2.1
    have h := hb.2.2 a ha hap
    omega

/-- Two adjacent covered cells are in the very same maximal child. All
    cross-piece seams therefore meet the parent's exposed region. -/
theorem neighboring_maximal_children {n : Nat} {a b : RedSquare} {p q : Int × Int}
    (ha : ChildOwns n a p) (hb : ChildOwns n b q)
    (hdx : -1≤p.1-q.1 ∧ p.1-q.1≤1) (hdy : -1≤p.2-q.2 ∧ p.2-q.2≤1) :
    a.level=b.level ∧ a.cx=b.cx ∧ a.cy=b.cy := by
  have hnotlt : ¬a.level<b.level := by
    intro hlt
    have hi := red_squares_neighbor_nested hlt ha.2.1 hb.2.1 hdx hdy
    have hp := strictly_inside_contains hi ha.2.1
    have hle := ha.2.2 b hb.1 hp
    omega
  have hnotgt : ¬b.level<a.level := by
    intro hlt
    have hi := red_squares_neighbor_nested hlt hb.2.1 ha.2.1 (by omega) (by omega)
    have hp := strictly_inside_contains hi hb.2.1
    have hle := hb.2.2 a ha.1 hp
    omega
  have hl : a.level=b.level := by omega
  exact ⟨hl,same_level_neighbor_square hl ha.2.1 hb.2.1 hdx hdy⟩

@[expose] def RootCovered (n : Nat) (p : Int × Int) : Prop :=
  -(boardHalf n:Int)<p.1 ∧ p.1<(boardHalf n:Int) ∧ BoardCovered n p.1 p.2

@[expose] noncomputable def childOwner (n : Nat) (p : Int × Int) : Option RedSquare := by
  classical
  exact if h : RootCovered n p then
    some (Classical.choose (covered_has_maximal_child ⟨h.1,h.2.1⟩ h.2.2)) else none

theorem childOwner_spec {n : Nat} {p : Int × Int} {b : RedSquare}
    (h : childOwner n p=some b) : ChildOwns n b p := by
  classical
  unfold childOwner at h
  split at h
  next hc =>
    have he := Option.some.inj h
    rw [←he]
    exact Classical.choose_spec (covered_has_maximal_child ⟨hc.1,hc.2.1⟩ hc.2.2)
  next hc => cases h

theorem childOwner_none_iff (n : Nat) (p : Int × Int) :
    childOwner n p=none ↔ ¬RootCovered n p := by
  classical
  unfold childOwner
  split <;> simp_all

theorem redSquare_ext {a b : RedSquare} (hl : a.level=b.level) (hx : a.cx=b.cx) (hy : a.cy=b.cy) : a=b := by
  cases a
  cases b
  simp_all

theorem childOwner_neighbors {n : Nat} {p q : Int × Int} {a b : RedSquare}
    (ha : childOwner n p=some a) (hb : childOwner n q=some b)
    (hdx : -1≤p.1-q.1 ∧ p.1-q.1≤1) (hdy : -1≤p.2-q.2 ∧ p.2-q.2≤1) : a=b := by
  have h := neighboring_maximal_children (childOwner_spec ha) (childOwner_spec hb) hdx hdy
  exact redSquare_ext h.1 h.2.1 h.2.2


theorem in_lower_rootCovered {n : Nat} {b : RedSquare} {p : Int × Int}
    (hb : LowerSquareInside n b) (hp : InRedSquare b p) : RootCovered n p := by
  have hx1 := hp.1.1
  have hx2 := hp.1.2
  have hL := hb.2.1
  have hR := hb.2.2.1
  exact ⟨by omega,by omega,lower_square_covered hb hp⟩

theorem childOwner_constant {n : Nat} {p q : Int × Int} {b : RedSquare}
    (hb : childOwner n p=some b) (hq : InRedSquare b q) : childOwner n q=some b := by
  have hb' := childOwner_spec hb
  have hroot := in_lower_rootCovered hb'.1 hq
  have hn : childOwner n q≠none := by
    intro he
    exact (childOwner_none_iff n q).mp he hroot
  cases he : childOwner n q with
  | none => exact False.elim (hn he)
  | some a =>
    have ha := childOwner_spec he
    have hbq := maximal_child_stable hb' hq
    have hh := maximal_child_unique ha hbq
    exact congrArg some (redSquare_ext hh.1 hh.2.1 hh.2.2)

theorem no_child_outside {n : Nat} {p q : Int × Int} {b : RedSquare}
    (hp : childOwner n p=none) (hq : childOwner n q=some b) : ¬InRedSquare b p := by
  intro h
  have hc := in_lower_rootCovered (childOwner_spec hq).1 h
  exact (childOwner_none_iff n p).mp hp hc

theorem childOwner_horizontal_entry {n : Nat} {r s : Int} {b : RedSquare}
    (hp : childOwner n (r,s)=none) (hq : childOwner n (r+1,s)=some b) :
    r+1=b.cx-boardHalf b.level := by
  have hn := no_child_outside hp hq
  have hb := (childOwner_spec hq).2.1
  have hx := hb.1
  have hy := hb.2
  unfold ClosedInterval at hx
  by_cases he : r+1=b.cx-boardHalf b.level
  · exact he
  · exact False.elim (hn ⟨by unfold ClosedInterval; omega,hy⟩)

theorem childOwner_horizontal_exit {n : Nat} {r s : Int} {b : RedSquare}
    (hp : childOwner n (r,s)=some b) (hq : childOwner n (r+1,s)=none) :
    r=b.cx+boardHalf b.level := by
  have hn := no_child_outside hq hp
  have hb := (childOwner_spec hp).2.1
  have hx := hb.1
  have hy := hb.2
  unfold ClosedInterval at hx
  by_cases he : r=b.cx+boardHalf b.level
  · exact he
  · exact False.elim (hn ⟨by unfold ClosedInterval; omega,hy⟩)

theorem childOwner_vertical_entry {n : Nat} {r s : Int} {b : RedSquare}
    (hp : childOwner n (r,s)=none) (hq : childOwner n (r,s+1)=some b) :
    s+1=b.cy-boardHalf b.level := by
  have hn := no_child_outside hp hq
  have hb := (childOwner_spec hq).2.1
  have hx := hb.1
  have hy := hb.2
  unfold ClosedInterval at hy
  by_cases he : s+1=b.cy-boardHalf b.level
  · exact he
  · exact False.elim (hn ⟨hx,by unfold ClosedInterval; omega⟩)

theorem childOwner_vertical_exit {n : Nat} {r s : Int} {b : RedSquare}
    (hp : childOwner n (r,s)=some b) (hq : childOwner n (r,s+1)=none) :
    s=b.cy+boardHalf b.level := by
  have hn := no_child_outside hq hp
  have hb := (childOwner_spec hp).2.1
  have hx := hb.1
  have hy := hb.2
  unfold ClosedInterval at hy
  by_cases he : s=b.cy+boardHalf b.level
  · exact he
  · exact False.elim (hn ⟨hx,by unfold ClosedInterval; omega⟩)

end K230Verification
#print axioms K230Verification.covered_has_maximal_child
#print axioms K230Verification.childOwner_neighbors
