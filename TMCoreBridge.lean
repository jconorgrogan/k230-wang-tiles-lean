module
public import FullPlaneData
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

@[expose] def vColor : VLabel → TMColor
  | .symbol a => .symbol a
  | .head q a => .head q a
@[expose] def hColor : HLabel → TMColor
  | none => .blank
  | some (d,q) => .move d q
@[expose] def rowTile (n : VLabel) (e : HLabel) (s : VLabel) (w : HLabel) : Quad TMColor :=
  ⟨vColor n,hColor e,vColor s,hColor w⟩

theorem index_read (i : Nat) : 2*(i/2)+(if i%2==1 then 1 else 0)=i := by
  by_cases h : i%2=1
  · simp [h]; omega
  · have h0 : i%2=0 := by omega
    simp [h0]; omega

theorem k230_step_index {i : Nat} (hi : i<460) :
    k230Machine (i/2) (i%2==1) = some (decodeTransition k230Codes[i]!) := by
  have hq : i/2<230 := by omega
  simp only [k230Machine, if_pos hq, index_read]

@[expose] def codeMove (code : Nat) : TMColor :=
  .move (if code%2=1 then .right else .left) (code/4)

theorem move_code_normalize (code : Nat) :
    TMColor.move (if (2*(code/4)+code%2)%2=1 then .right else .left)
      ((2*(code/4)+code%2)/2) = codeMove code := by
  have hm : (2*(code/4)+code%2)%2=code%2 := by omega
  have hd : (2*(code/4)+code%2)/2=code/4 := by omega
  simp [hm,hd,codeMove]

theorem tmMoves_mem_codes {m : TMColor} :
    m ∈ tmMoves ↔ ∃ code ∈ k230Codes.toList, codeMove code=m := by
  unfold tmMoves
  constructor
  · intro hm
    obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
    rw [List.mem_eraseDups] at hv
    obtain ⟨code,hcode,hv⟩ := List.mem_map.mp hv
    subst v
    exact ⟨code,hcode,(move_code_normalize code).symm.trans he⟩
  · rintro ⟨code,hcode,he⟩
    apply List.mem_map.mpr
    refine ⟨2*(code/4)+code%2,?_,?_⟩
    · rw [List.mem_eraseDups]
      exact List.mem_map.mpr ⟨code,hcode,rfl⟩
    · exact (move_code_normalize code).trans he

theorem code_mem_index {code : Nat} : code ∈ k230Codes.toList ↔
    ∃ i : Nat, i<460 ∧ k230Codes[i]! = code := by
  constructor
  · intro h
    obtain ⟨i,hi,hcode⟩ := List.mem_iff_getElem.mp h
    have hi' : i<k230Codes.size := by simpa only [Array.length_toList] using hi
    have hi460 : i<460 := by simpa only [k230_transition_count] using hi'
    refine ⟨i,hi460,?_⟩
    rw [getElem!_pos k230Codes i hi']
    simpa only [Array.getElem_toList] using hcode
  · rintro ⟨i,hi,hcode⟩
    have hi' : i<k230Codes.size := by simpa only [k230_transition_count] using hi
    apply List.mem_iff_getElem.mpr
    refine ⟨i,by simpa only [Array.length_toList] using hi',?_⟩
    rw [getElem!_pos k230Codes i hi'] at hcode
    simpa only [Array.getElem_toList] using hcode

theorem code_enters_machine {code : Nat} (hc : code ∈ k230Codes.toList) :
    ∃ p a, k230Machine p a = some (decodeTransition code) := by
  obtain ⟨i,hi,hcode⟩ := code_mem_index.mp hc
  refine ⟨i/2,i%2==1,?_⟩
  simpa only [hcode] using k230_step_index hi

theorem machine_step_has_code {q q' : Nat} {a b : Bool} {d : Dir}
    (hs : k230Machine q a=some (q',b,d)) :
    ∃ code ∈ k230Codes.toList, decodeTransition code=(q',b,d) := by
  have hq : q<230 := by
    by_cases h : q<230
    · exact h
    · simp [k230Machine,h] at hs
  let i := 2*q+(if a then 1 else 0)
  have hi : i<460 := by cases a <;> simp [i] <;> omega
  refine ⟨k230Codes[i]!,code_mem_index.mpr ⟨i,hi,rfl⟩,?_⟩
  exact Option.some.inj (by simpa only [k230Machine,if_pos hq] using hs)

/-- The deduplicated concrete move list is exactly the entered-state/side
    relation used by the generic row compiler, including its witness. -/
theorem tmMoves_mem_entered {q : Nat} {d : Dir} :
    TMColor.move d q ∈ tmMoves ↔ ∃ p a b, k230Machine p a=some (q,b,d) := by
  constructor
  · intro hm
    obtain ⟨code,hcode,he⟩ := tmMoves_mem_codes.mp hm
    obtain ⟨p,a,hs⟩ := code_enters_machine hcode
    change TMColor.move (decodeTransition code).2.2 (decodeTransition code).1 = .move d q at he
    obtain ⟨hd,hq⟩ := TMColor.move.inj he
    refine ⟨p,a,(decodeTransition code).2.1,?_⟩
    rw [←hd,←hq]
    exact hs
  · rintro ⟨p,a,b,hs⟩
    obtain ⟨code,hcode,he⟩ := machine_step_has_code hs
    apply tmMoves_mem_codes.mpr
    refine ⟨code,hcode,?_⟩
    change TMColor.move (decodeTransition code).2.2 (decodeTransition code).1 = .move d q
    rw [he]

@[expose] def parseV : TMColor → VLabel
  | .symbol a => .symbol a
  | .head q a => .head q a
  | _ => .symbol false
@[expose] def parseH : TMColor → HLabel
  | .move d q => some (d,q)
  | _ => none

theorem parseV_vColor (v : VLabel) : parseV (vColor v)=v := by cases v <;> rfl
theorem parseH_hColor (h : HLabel) : parseH (hColor h)=h := by
  cases h with
  | none => rfl
  | some z => cases z; rfl

@[expose] def actionTile (i : Nat) : Quad TMColor :=
  let z := decodeTransition k230Codes[i]!
  let head := TMColor.head (i/2) (i%2==1)
  if k230Codes[i]! % 2=1 then ⟨.symbol z.2.1,.move .right z.1,head,.blank⟩
  else ⟨.symbol z.2.1,.blank,head,.move .left z.1⟩

theorem actionTile_sound {i : Nat} (hi : i<460) :
    Allowed k230Machine (parseV (actionTile i).n) (parseH (actionTile i).e)
      (parseV (actionTile i).s) (parseH (actionTile i).w) := by
  have hs := k230_step_index hi
  by_cases hd : k230Codes[i]!%2=1
  · simp only [actionTile,if_pos hd,parseV,parseH]
    exact Allowed.right _ _ _ _ (by simpa [decodeTransition,hd] using hs)
  · simp only [actionTile,if_neg hd,parseV,parseH]
    exact Allowed.left _ _ _ _ (by simpa [decodeTransition,hd] using hs)

theorem tmActions_sound {t : Quad TMColor} (ht : t ∈ tmActions) :
    Allowed k230Machine (parseV t.n) (parseH t.e) (parseV t.s) (parseH t.w) := by
  obtain ⟨i,hi,ht⟩ := List.mem_map.mp ht
  have hi460 : i<460 := List.mem_range.mp hi
  change actionTile i=t at ht
  subst t
  exact actionTile_sound hi460

theorem machine_step_indexed {q q' : Nat} {a b : Bool} {d : Dir}
    (hs : k230Machine q a=some (q',b,d)) :
    q<230 ∧ decodeTransition k230Codes[2*q+(if a then 1 else 0)]! = (q',b,d) := by
  by_cases hq : q<230
  · exact ⟨hq,Option.some.inj (by simpa only [k230Machine,if_pos hq] using hs)⟩
  · simp [k230Machine,hq] at hs

theorem action_right_mem {q q' : Nat} {a b : Bool}
    (hs : k230Machine q a=some (q',b,.right)) :
    rowTile (.symbol b) (some (.right,q')) (.head q a) none ∈ tmActions := by
  obtain ⟨hq,hdecode⟩ := machine_step_indexed hs
  let i := 2*q+(if a then 1 else 0)
  have hi : i<460 := by cases a <;> simp [i] <;> omega
  have hq' : i/2=q := by cases a <;> simp [i] <;> omega
  have ha' : (i%2==1)=a := by cases a <;> simp [i] <;> omega
  have hd : k230Codes[i]!%2=1 := by
    have h := congrArg (fun z : Nat × Bool × Dir => z.2.2) hdecode
    change (if k230Codes[i]!%2=1 then Dir.right else Dir.left)=Dir.right at h
    by_cases he : k230Codes[i]!%2=1
    · exact he
    · simp [he] at h
  apply List.mem_map.mpr
  refine ⟨i,List.mem_range.mpr hi,?_⟩
  change actionTile i=_
  have hz : decodeTransition k230Codes[i]! = (q',b,.right) := hdecode
  simp [actionTile,hd,hz,hq',ha',rowTile,vColor,hColor]

theorem action_left_mem {q q' : Nat} {a b : Bool}
    (hs : k230Machine q a=some (q',b,.left)) :
    rowTile (.symbol b) none (.head q a) (some (.left,q')) ∈ tmActions := by
  obtain ⟨hq,hdecode⟩ := machine_step_indexed hs
  let i := 2*q+(if a then 1 else 0)
  have hi : i<460 := by cases a <;> simp [i] <;> omega
  have hq' : i/2=q := by cases a <;> simp [i] <;> omega
  have ha' : (i%2==1)=a := by cases a <;> simp [i] <;> omega
  have hd : ¬ k230Codes[i]!%2=1 := by
    have h := congrArg (fun z : Nat × Bool × Dir => z.2.2) hdecode
    change (if k230Codes[i]!%2=1 then Dir.right else Dir.left)=Dir.left at h
    intro he
    simp [he] at h
  apply List.mem_map.mpr
  refine ⟨i,List.mem_range.mpr hi,?_⟩
  change actionTile i=_
  have hz : decodeTransition k230Codes[i]! = (q',b,.left) := hdecode
  simp [actionTile,hd,hz,hq',ha',rowTile,vColor,hColor]

theorem tmMerges_sound {t : Quad TMColor} (ht : t ∈ tmMerges) :
    Allowed k230Machine (parseV t.n) (parseH t.e) (parseV t.s) (parseH t.w) := by
  obtain ⟨m,hm,ht⟩ := List.mem_flatMap.mp ht
  cases m with
  | move d q =>
    have entered := tmMoves_mem_entered.mp hm
    cases d with
    | right =>
      have he : t=⟨.head q false,.blank,.symbol false,.move .right q⟩ ∨
          t=⟨.head q true,.blank,.symbol true,.move .right q⟩ := by simpa using ht
      rcases he with rfl|rfl
      · exact Allowed.mergeRight q false entered
      · exact Allowed.mergeRight q true entered
    | left =>
      have he : t=⟨.head q false,.move .left q,.symbol false,.blank⟩ ∨
          t=⟨.head q true,.move .left q,.symbol true,.blank⟩ := by simpa using ht
      rcases he with rfl|rfl
      · exact Allowed.mergeLeft q false entered
      · exact Allowed.mergeLeft q true entered
  | _ => simp at ht

/-- Every one of the exact 972 comp tiles implements the exact generic
    transition relation, with no extra entered states or fake merges. -/
theorem tmComp_sound {t : Quad TMColor} (ht : t ∈ tmComp) :
    Allowed k230Machine (parseV t.n) (parseH t.e) (parseV t.s) (parseH t.w) := by
  simp only [tmComp,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with ((h|h)|h)|h
  · subst t; exact Allowed.symbol false
  · subst t; exact Allowed.symbol true
  · exact tmActions_sound h
  · exact tmMerges_sound h

/-- Conversely every legal generic row tile occurs in the exact list. -/
theorem tmComp_complete {n : VLabel} {e : HLabel} {s : VLabel} {w : HLabel}
    (ha : Allowed k230Machine n e s w) : rowTile n e s w ∈ tmComp := by
  simp only [tmComp,List.mem_append]
  cases ha with
  | symbol a =>
    apply Or.inl; apply Or.inl
    cases a <;> simp [rowTile,vColor,hColor]
  | right q a q' b hs => exact Or.inl (Or.inr (action_right_mem hs))
  | left q a q' b hs => exact Or.inl (Or.inr (action_left_mem hs))
  | mergeRight q a entered =>
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨TMColor.move .right q,tmMoves_mem_entered.mpr entered,?_⟩
    cases a <;> simp [rowTile,vColor,hColor]
  | mergeLeft q a entered =>
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨TMColor.move .left q,tmMoves_mem_entered.mpr entered,?_⟩
    cases a <;> simp [rowTile,vColor,hColor]

/-- Exact finite compiler binding to the already verified generic row
    semantics. This theorem concerns the actual tmComp list imported from
    FullPlaneData, not a redefined compiler. -/
theorem tmComp_iff_allowed {n : VLabel} {e : HLabel} {s : VLabel} {w : HLabel} :
    rowTile n e s w ∈ tmComp ↔ Allowed k230Machine n e s w := by
  constructor
  · intro ht
    simpa only [rowTile,parseV_vColor,parseH_hColor] using tmComp_sound ht
  · exact tmComp_complete

#print axioms tmMoves_mem_entered
#print axioms tmComp_sound
#print axioms tmComp_complete
#print axioms tmComp_iff_allowed
end K230Verification
