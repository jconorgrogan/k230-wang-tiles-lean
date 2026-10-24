module
public import BoardChannels
public section
set_option maxHeartbeats 0
namespace K230Verification

@[expose] noncomputable def NatSegmentCompatible (covered : Nat → Prop) (i : Nat) (c : Channel) : Prop := by
  classical
  exact EndAllows (if ∃ t, t≤i ∧ covered t then .outerRight else .innerLeft) c ∧
    EndAllows (if ∃ t, i<t ∧ covered t then .outerLeft else .innerRight) c

/-- Propagate actual edge values across every exposed segment of a finite trace. -/
theorem nat_segmentCompatible_of_trace (covered : Nat → Prop) (L : Nat) (edge : Nat → Channel)
    (hbound : ∀ t, covered t → 0<t ∧ t<L)
    (hcopy : ∀ i, 0<i → i<L → ¬covered i → edge i=edge (i-1))
    (hentry : ∀ i, 0<i → i<L → covered i → ¬covered (i-1) →
      EndAllows .outerLeft (edge (i-1)))
    (hexit : ∀ i, i<L → covered i → ¬covered (i+1) →
      EndAllows .outerRight (edge i))
    (hleft : EndAllows .innerLeft (edge 0))
    (hright : EndAllows .innerRight (edge (L-1)))
    (i : Nat) (hi : i<L) (hfree : ¬covered i) : NatSegmentCompatible covered i (edge i) := by
  classical
  have left : ∀ i, i<L → ¬covered i →
      EndAllows (if ∃t,t≤i ∧ covered t then .outerRight else .innerLeft) (edge i) := by
    intro j
    induction j with
    | zero =>
      intro _ _
      have hn : ¬∃t,t≤0 ∧ covered t := by
        rintro ⟨t,ht,hc⟩
        have := (hbound t hc).1
        omega
      simpa only [if_neg hn] using hleft
    | succ j ih =>
      intro hj hfj
      have he := hcopy (j+1) (by omega) hj hfj
      by_cases hc : covered j
      · have hn : ∃t,t≤j+1 ∧ covered t := ⟨j,by omega,hc⟩
        rw [if_pos hn,he]
        simpa only [Nat.add_sub_cancel] using hexit j (by omega) hc hfj
      · have hh := ih (by omega) hc
        have iffBefore : (∃t,t≤j+1 ∧ covered t) ↔ ∃t,t≤j ∧ covered t := by
          constructor
          · rintro ⟨t,ht,hct⟩
            have hn : t≠j+1 := by intro he; subst t; exact hfj hct
            exact ⟨t,by omega,hct⟩
          · rintro ⟨t,ht,hct⟩; exact ⟨t,by omega,hct⟩
        simpa only [iffBefore,he,Nat.add_sub_cancel] using hh
  have right : ∀ d j, j+d+1=L → ¬covered j →
      EndAllows (if ∃t,j<t ∧ covered t then .outerLeft else .innerRight) (edge j) := by
    intro d
    induction d with
    | zero =>
      intro j hj _
      have hn : ¬∃t,j<t ∧ covered t := by
        rintro ⟨t,ht,hc⟩
        have := (hbound t hc).2
        omega
      have he : j=L-1 := by omega
      rw [if_neg hn,he]
      exact hright
    | succ d ih =>
      intro j hj hfj
      by_cases hc : covered (j+1)
      · have hn : ∃t,j<t ∧ covered t := ⟨j+1,by omega,hc⟩
        rw [if_pos hn]
        simpa only [Nat.add_sub_cancel] using hentry (j+1) (by omega) (by omega) hc (by simpa using hfj)
      · have hh := ih (j+1) (by omega) hc
        have he := hcopy (j+1) (by omega) (by omega) hc
        have iffAfter : (∃t,j<t ∧ covered t) ↔ ∃t,j+1<t ∧ covered t := by
          constructor
          · rintro ⟨t,ht,hct⟩
            have hn : t≠j+1 := by intro he; subst t; exact hc hct
            exact ⟨t,by omega,hct⟩
          · rintro ⟨t,ht,hct⟩; exact ⟨t,by omega,hct⟩
        simpa only [iffAfter,he,Nat.add_sub_cancel] using hh
  exact ⟨left i hi hfree,right (L-1-i) i (by omega) hfree⟩

/-- Integer-coordinate form used on actual complete board channel traces. -/
theorem int_segmentCompatible_of_trace (covered : Int → Prop) (H : Nat) (edge : Int → Channel)
    (hH : 0<H)
    (hbound : ∀ t, covered t → -(H:Int)<t ∧ t<(H:Int))
    (hcopy : ∀ s, -(H:Int)<s → s<(H:Int) → ¬covered s → edge s=edge (s-1))
    (hentry : ∀ s, -(H:Int)<s → s<(H:Int) → covered s → ¬covered (s-1) →
      EndAllows .outerLeft (edge (s-1)))
    (hexit : ∀ s, -(H:Int)<s → s<(H:Int) → covered s → ¬covered (s+1) →
      EndAllows .outerRight (edge s))
    (hleft : EndAllows .innerLeft (edge (-(H:Int))))
    (hright : EndAllows .innerRight (edge ((H:Int)-1)))
    (s : Int) (hsl : -(H:Int)<s) (hsr : s<(H:Int)) (hfree : ¬covered s) :
    SegmentCompatible covered s (edge s) := by
  classical
  let cv : Nat → Prop := fun j => covered ((j:Int)-H)
  let ev : Nat → Channel := fun j => edge ((j:Int)-H)
  let i : Nat := (s+H).toNat
  have hie : (i:Int)-H=s := by dsimp [i]; omega
  have hi : i<2*H := by omega
  have hcv : ∀ t, cv t → 0<t ∧ t<2*H := by
    intro t ht
    have hh := hbound ((t:Int)-H) ht
    omega
  have hcp : ∀ j, 0<j → j<2*H → ¬cv j → ev j=ev (j-1) := by
    intro j hj hjL hf
    have hh := hcopy ((j:Int)-H) (by omega) (by omega) hf
    have he : ((j-1:Nat):Int)-H=((j:Int)-H)-1 := by omega
    simpa only [ev,he] using hh
  have hen : ∀ j, 0<j → j<2*H → cv j → ¬cv (j-1) → EndAllows .outerLeft (ev (j-1)) := by
    intro j hj hjL hc hf
    have he : ((j-1:Nat):Int)-H=((j:Int)-H)-1 := by omega
    have hf' : ¬covered (((j:Int)-H)-1) := by simpa only [cv,he] using hf
    have hh := hentry ((j:Int)-H) (by omega) (by omega) hc hf'
    simpa only [ev,he] using hh
  have hex : ∀ j, j<2*H → cv j → ¬cv (j+1) → EndAllows .outerRight (ev j) := by
    intro j hjL hc hf
    have hh := hcv j hc
    have he : ((j+1:Nat):Int)-H=((j:Int)-H)+1 := by omega
    have hf' : ¬covered (((j:Int)-H)+1) := by simpa only [cv,he] using hf
    exact hexit ((j:Int)-H) (by omega) (by omega) hc hf'
  have hl : EndAllows .innerLeft (ev 0) := by simpa only [ev,Int.natCast_zero,Int.zero_sub] using hleft
  have hr : EndAllows .innerRight (ev (2*H-1)) := by
    have he : ((2*H-1:Nat):Int)-H=(H:Int)-1 := by omega
    simpa only [ev,he] using hright
  have hf : ¬cv i := by simpa only [cv,hie] using hfree
  have result := nat_segmentCompatible_of_trace cv (2*H) ev hcv hcp hen hex hl hr i hi hf
  have before : (∃t:Nat,t≤i ∧ cv t) ↔ ∃t:Int,t≤s ∧ covered t := by
    constructor
    · rintro ⟨t,ht,hct⟩
      exact ⟨(t:Int)-H,by omega,hct⟩
    · rintro ⟨t,ht,hct⟩
      have htbound := hbound t hct
      have he : (((t+H).toNat : Nat):Int)-H=t := by omega
      refine ⟨(t+H).toNat,by omega,?_⟩
      simpa only [cv,he] using hct
  have after : (∃t:Nat,i<t ∧ cv t) ↔ ∃t:Int,s<t ∧ covered t := by
    constructor
    · rintro ⟨t,ht,hct⟩
      exact ⟨(t:Int)-H,by omega,hct⟩
    · rintro ⟨t,ht,hct⟩
      have htbound := hbound t hct
      have he : (((t+H).toNat : Nat):Int)-H=t := by omega
      refine ⟨(t+H).toNat,by omega,?_⟩
      simpa only [cv,he] using hct
  unfold NatSegmentCompatible at result
  simpa only [before,after,ev,hie,SegmentCompatible] using result

#print axioms nat_segmentCompatible_of_trace
#print axioms int_segmentCompatible_of_trace
end K230Verification
