module
public import BoardChannels
public section
namespace K230Verification

theorem board_half_succ {n : Nat} (hn : 1 ≤ n) :
    boardHalf (n+1) = 4 * boardHalf n := by
  have he : n-1+1=n := by omega
  have hp : 4^n = 4^(n-1)*4 := by
    calc
      4^n = 4^(n-1+1) := congrArg (fun z : Nat => 4^z) he.symm
      _ = 4^(n-1)*4 := Nat.pow_succ _ _
  simp only [boardHalf, Nat.add_sub_cancel]
  rw [hp]
  omega

theorem lower_period_dvd {m n : Nat} (hmn : m ≤ n) :
    (4*(boardHalf m : Int)) ∣ (4*(boardHalf n : Int)) := by
  have hp : 4^(m-1) ∣ 4^(n-1) := Nat.pow_dvd_pow 4 (by omega)
  have hd := Nat.mul_dvd_mul_left 8 hp
  have hi := Int.natCast_dvd_natCast.mpr hd
  simpa [boardHalf, Int.natCast_mul, ← Int.mul_assoc] using hi

theorem band_reflect_period {h P t : Int} (hh : 0 < h) (hd : (4*h) ∣ P) :
    RedBand h (P-t) ↔ RedBand h t := by
  have he : (P-t) % (4*h) = (-t) % (4*h) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    have hz : (P-t)-(-t)=P := by omega
    rw [hz]
    exact Int.emod_eq_zero_of_dvd hd
  have hb : RedBand h (P-t) ↔ RedBand h (-t) := by
    unfold RedBand
    rw [he]
  rw [hb]
  constructor
  · intro h
    have := red_band_symmetric hh h
    simpa using this
  · exact red_band_symmetric hh

theorem blocked_reflect {n : Nat} {t : Int} :
    BlockedOffset n (4*(boardHalf n : Int)-t) ↔ BlockedOffset n t := by
  constructor <;> rintro ⟨m,hm,hmn,hb⟩
  · refine ⟨m,hm,hmn,?_⟩
    have hp : (0 : Int) < boardHalf m := by have := board_half_pos m; omega
    exact (band_reflect_period hp (lower_period_dvd (by omega))).mp hb
  · refine ⟨m,hm,hmn,?_⟩
    have hp : (0 : Int) < boardHalf m := by have := board_half_pos m; omega
    exact (band_reflect_period hp (lower_period_dvd (by omega))).mpr hb

theorem blocked_succ {n : Nat} (hn : 1 ≤ n) {t : Int} :
    BlockedOffset (n+1) t ↔ BlockedOffset n t ∨ RedBand (boardHalf n) t := by
  constructor
  · rintro ⟨m,hm,hmn,hb⟩
    by_cases he : m=n
    · right; simpa [he] using hb
    · left; exact ⟨m,hm,by omega,hb⟩
  · rintro (h|h)
    · obtain ⟨m,hm,hmn,hb⟩ := h
      exact ⟨m,hm,by omega,hb⟩
    · exact ⟨n,hn,by omega,h⟩

@[expose] def PositiveFree (n : Nat) (t : Int) : Prop :=
  0 < t ∧ t < (boardHalf n : Int) ∧ ¬ BlockedOffset n t

theorem positive_free_one {t : Int} : PositiveFree 1 t ↔ t=1 := by
  unfold PositiveFree boardHalf BlockedOffset
  simp only [Nat.sub_self, Nat.pow_zero]
  constructor
  · rintro ⟨hl,hr,_⟩; omega
  · intro ht; subst t
    refine ⟨by decide,by decide,?_⟩
    rintro ⟨m,hm,hmn,_⟩
    omega

/-- Exact all-size positive free-offset recurrence derived from the band
    definition, rather than introduced as a separate combinatorial model. -/
theorem positive_free_succ {n : Nat} (hn : 1 ≤ n) {t : Int} :
    PositiveFree (n+1) t ↔ PositiveFree n t ∨
      ∃ s, PositiveFree n s ∧ t=4*(boardHalf n : Int)-s := by
  have hp : (0 : Int) < boardHalf n := by have := board_half_pos n; omega
  have hs : (boardHalf (n+1) : Int)=4*(boardHalf n : Int) := by
    rw [board_half_succ hn]
    simp
  constructor
  · rintro ⟨ht0,htH,hnot⟩
    rw [hs] at htH
    have hnold : ¬ BlockedOffset n t := by
      intro hb; exact hnot ((blocked_succ hn).mpr (Or.inl hb))
    have hnband : ¬ RedBand (boardHalf n) t := by
      intro hb; exact hnot ((blocked_succ hn).mpr (Or.inr hb))
    have he : t % (4*(boardHalf n : Int))=t := Int.emod_eq_of_lt (by omega) htH
    unfold RedBand at hnband
    rw [he] at hnband
    by_cases ht : t < (boardHalf n : Int)
    · exact Or.inl ⟨ht0,ht,hnold⟩
    · right
      have ht3 : 3*(boardHalf n : Int)<t := by omega
      refine ⟨4*(boardHalf n : Int)-t, ⟨by omega,by omega,?_⟩,by omega⟩
      exact fun hb => hnold (blocked_reflect.mp hb)
  · rintro (h | ⟨s,h,ht⟩)
    · rcases h with ⟨ht0,htH,hnot⟩
      refine ⟨ht0,by omega,?_⟩
      rw [blocked_succ hn]
      rintro (hb|hb)
      · exact hnot hb
      · have he : t % (4*(boardHalf n : Int))=t := Int.emod_eq_of_lt (by omega) (by omega)
        unfold RedBand at hb
        rw [he] at hb
        omega
    · rcases h with ⟨hs0,hsH,hnot⟩
      subst t
      refine ⟨by omega,by omega,?_⟩
      rw [blocked_succ hn]
      rintro (hb|hb)
      · exact hnot (blocked_reflect.mp hb)
      · have he : (4*(boardHalf n : Int)-s) % (4*(boardHalf n : Int))=4*(boardHalf n : Int)-s :=
          Int.emod_eq_of_lt (by omega) (by omega)
        unfold RedBand at hb
        rw [he] at hb
        omega

/-- Enumerates exactly the positive free offsets of board level 2*(k+1).
    It is not assumed sorted; membership and absence of duplicates are proved. -/
@[expose] def positiveOffsets : Nat → List Int
  | 0 => [1]
  | k+1 => positiveOffsets k ++
      (positiveOffsets k).map (fun s => 4*(boardHalf (k+1) : Int)-s)

theorem positiveOffsets_mem {k : Nat} {t : Int} :
    t ∈ positiveOffsets k ↔ PositiveFree (k+1) t := by
  induction k generalizing t with
  | zero => simp [positiveOffsets, positive_free_one]
  | succ k ih =>
    rw [positive_free_succ (by omega)]
    simp only [positiveOffsets, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (h | ⟨s,hs,ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s,hs,ht.symm⟩
    · rintro (h | ⟨s,hs,ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨s,hs,ht.symm⟩

theorem positiveOffsets_length (k : Nat) : (positiveOffsets k).length = 2^k := by
  induction k with
  | zero => simp [positiveOffsets]
  | succ k ih => simp only [positiveOffsets, List.length_append, List.length_map, ih, Nat.pow_succ]; omega

theorem positiveOffsets_nodup (k : Nat) : (positiveOffsets k).Nodup := by
  induction k with
  | zero => simp [positiveOffsets]
  | succ k ih =>
    unfold positiveOffsets
    apply List.nodup_append.mpr
    refine ⟨ih, ?_, ?_⟩
    · exact List.Pairwise.map _ (by intro a b hab he; apply hab; omega) ih
    · intro a ha b hb
      obtain ⟨s,hs,hb⟩ := List.mem_map.mp hb
      have ha' := positiveOffsets_mem.mp ha
      have hs' := positiveOffsets_mem.mp hs
      rcases ha' with ⟨ha0,haH,_⟩
      rcases hs' with ⟨hs0,hsH,_⟩
      omega

theorem reflect_mod4_one (H t : Int) : (4*H-t)%4=1 ↔ t%4=3 := by omega
theorem reflect_mod4_three (H t : Int) : (4*H-t)%4=3 ↔ t%4=1 := by omega

theorem positiveOffsets_residue {k : Nat} {t : Int} (ht : t ∈ positiveOffsets k) :
    t%4=1 ∨ t%4=3 := by
  induction k generalizing t with
  | zero => simp [positiveOffsets] at ht; subst t; decide
  | succ k ih =>
    rcases List.mem_append.mp ht with ht | ht
    · exact ih ht
    · obtain ⟨s,hs,ht⟩ := List.mem_map.mp ht
      subst t
      rcases ih hs with h|h
      · exact Or.inr ((reflect_mod4_three _ _).mpr h)
      · exact Or.inl ((reflect_mod4_one _ _).mpr h)

theorem residue_counts_partition (xs : List Int)
    (hall : ∀ t, t ∈ xs → t%4=1 ∨ t%4=3) :
    xs.countP (fun t => decide (t%4=1)) + xs.countP (fun t => decide (t%4=3)) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hall x (by simp)
    have hi := ih (fun t ht => hall t (by simp [ht]))
    rcases hx with hx | hx
    · have hn : ¬ x%4=3 := by omega
      simp [List.countP_cons, hx]
      omega
    · have hn : ¬ x%4=1 := by omega
      simp [List.countP_cons, hx]
      omega

theorem positiveOffsets_count_one (k : Nat) :
    (positiveOffsets (k+1)).countP (fun t => decide (t%4=1)) = 2^k := by
  rw [positiveOffsets, List.countP_append, List.countP_map]
  have he : List.countP ((fun t => decide (t%4=1)) ∘
      (fun s => 4*(boardHalf (k+1) : Int)-s)) (positiveOffsets k) =
      List.countP (fun t => decide (t%4=3)) (positiveOffsets k) := by
    apply List.countP_congr
    intro t _
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact reflect_mod4_one _ _
  rw [he, residue_counts_partition _ (fun _ ht => positiveOffsets_residue ht), positiveOffsets_length]

theorem positiveOffsets_count_three (k : Nat) :
    (positiveOffsets (k+1)).countP (fun t => decide (t%4=3)) = 2^k := by
  rw [positiveOffsets, List.countP_append, List.countP_map]
  have he : List.countP ((fun t => decide (t%4=3)) ∘
      (fun s => 4*(boardHalf (k+1) : Int)-s)) (positiveOffsets k) =
      List.countP (fun t => decide (t%4=1)) (positiveOffsets k) := by
    apply List.countP_congr
    intro t _
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact reflect_mod4_three _ _
  rw [he, Nat.add_comm, residue_counts_partition _ (fun _ ht => positiveOffsets_residue ht), positiveOffsets_length]

theorem blocked_neg {n : Nat} {t : Int} :
    BlockedOffset n (-t) ↔ BlockedOffset n t := by
  constructor <;> rintro ⟨m,hm,hmn,hb⟩
  · refine ⟨m,hm,hmn,?_⟩
    have hp : (0 : Int) < boardHalf m := by have := board_half_pos m; omega
    have := red_band_symmetric hp hb
    simpa using this
  · refine ⟨m,hm,hmn,?_⟩
    have hp : (0 : Int) < boardHalf m := by have := board_half_pos m; omega
    exact red_band_symmetric hp hb

/-- The exact geometric tape-column predicate. Positive instances are also
    exactly the computation rows, since the row and column geometries agree. -/
@[expose] def TapeOffset (n : Nat) (t : Int) : Prop :=
  -(boardHalf n : Int)<t ∧ t<(boardHalf n : Int) ∧
  t%4=1 ∧ ¬ BlockedOffset n t

@[expose] def positiveTapeOffsets (k : Nat) : List Int :=
  (positiveOffsets (k+1)).filter (fun t => decide (t%4=1))
@[expose] def negativeTapeOffsets (k : Nat) : List Int :=
  ((positiveOffsets (k+1)).filter (fun t => decide (t%4=3))).map (fun t => -t)

theorem positiveTape_mem {k : Nat} {t : Int} :
    t ∈ positiveTapeOffsets k ↔ TapeOffset (k+2) t ∧ 0<t := by
  simp only [positiveTapeOffsets, List.mem_filter, decide_eq_true_eq, positiveOffsets_mem]
  constructor
  · rintro ⟨⟨ht0,htH,hnot⟩,hmod⟩
    exact ⟨⟨by omega,htH,hmod,hnot⟩,ht0⟩
  · rintro ⟨⟨_,htH,hmod,hnot⟩,ht0⟩
    exact ⟨⟨ht0,htH,hnot⟩,hmod⟩

theorem negativeTape_mem {k : Nat} {t : Int} :
    t ∈ negativeTapeOffsets k ↔ TapeOffset (k+2) t ∧ t<0 := by
  simp only [negativeTapeOffsets, List.mem_map, List.mem_filter, decide_eq_true_eq, positiveOffsets_mem]
  have he : k+1+1=k+2 := by omega
  simp only [he]
  constructor
  · rintro ⟨s,⟨⟨hs0,hsH,hnot⟩,hmod⟩,ht⟩
    subst t
    refine ⟨⟨by omega,by omega,by omega,?_⟩,by omega⟩
    exact fun hb => hnot (blocked_neg.mp hb)
  · rintro ⟨⟨htH,_,hmod,hnot⟩,ht0⟩
    refine ⟨-t, ⟨⟨by omega,by omega,?_⟩,by omega⟩,by omega⟩
    exact fun hb => hnot (blocked_neg.mp hb)

theorem positiveTape_nodup (k : Nat) : (positiveTapeOffsets k).Nodup := by
  exact List.Pairwise.filter _ (positiveOffsets_nodup (k+1))
theorem negativeTape_nodup (k : Nat) : (negativeTapeOffsets k).Nodup := by
  exact List.Pairwise.map _ (by intro a b hab he; apply hab; omega)
    (List.Pairwise.filter _ (positiveOffsets_nodup (k+1)))

/-- Exact number of selected positive columns AND positive computation rows
    in every level-2*(k+2) board, not a finite sample. -/
theorem positiveTape_length (k : Nat) : (positiveTapeOffsets k).length=2^k := by
  unfold positiveTapeOffsets
  rw [←List.countP_eq_length_filter]
  exact positiveOffsets_count_one k

theorem negativeTape_length (k : Nat) : (negativeTapeOffsets k).length=2^k := by
  unfold negativeTapeOffsets
  rw [List.length_map, ←List.countP_eq_length_filter]
  exact positiveOffsets_count_three k

theorem tape_offsets_complete {k : Nat} {t : Int} :
    TapeOffset (k+2) t ↔ t ∈ negativeTapeOffsets k ++ positiveTapeOffsets k := by
  rw [List.mem_append, negativeTape_mem, positiveTape_mem]
  constructor
  · intro ht
    have hm := ht.2.2.1
    by_cases hs : t<0
    · exact Or.inl ⟨ht,hs⟩
    · exact Or.inr ⟨ht,by omega⟩
  · rintro (⟨h,_⟩|⟨h,_⟩) <;> exact h

theorem tape_offsets_nodup (k : Nat) :
    (negativeTapeOffsets k ++ positiveTapeOffsets k).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨negativeTape_nodup k,positiveTape_nodup k,?_⟩
  intro a ha b hb
  have hneg := (negativeTape_mem.mp ha).2
  have hpos := (positiveTape_mem.mp hb).2
  omega

theorem positiveOffsets_one_mem (k : Nat) : (1 : Int) ∈ positiveOffsets k := by
  induction k with
  | zero => simp [positiveOffsets]
  | succ k ih => exact List.mem_append_left _ ih

theorem start_is_positive_tape (k : Nat) : (1 : Int) ∈ positiveTapeOffsets k := by
  apply List.mem_filter.mpr
  exact ⟨positiveOffsets_one_mem (k+1),by decide⟩

#print axioms positive_free_succ
#print axioms positiveOffsets_mem
#print axioms positiveOffsets_nodup
#print axioms tape_offsets_complete
#print axioms tape_offsets_nodup
#print axioms positiveTape_length
#print axioms negativeTape_length
end K230Verification
