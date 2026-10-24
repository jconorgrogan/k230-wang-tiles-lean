module
public import FreeOffsets
public section
namespace K230Verification

@[expose] def sortOffsets (xs : List Int) : List Int :=
  xs.mergeSort (fun a b => decide (a≤b))

theorem sortOffsets_mem {xs : List Int} {t : Int} :
    t ∈ sortOffsets xs ↔ t ∈ xs := List.mem_mergeSort
theorem sortOffsets_length (xs : List Int) : (sortOffsets xs).length=xs.length := List.length_mergeSort xs

theorem sortOffsets_strict {xs : List Int} (hn : xs.Nodup) :
    (sortOffsets xs).Pairwise (fun a b => a<b) := by
  have hle : (sortOffsets xs).Pairwise (fun a b => a≤b) := by
    have h := List.pairwise_mergeSort (le:=fun a b : Int => decide (a≤b))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp; omega) xs
    exact h.imp (fun hh => of_decide_eq_true hh)
  have hne : (sortOffsets xs).Nodup :=
    (List.Perm.nodup_iff (List.mergeSort_perm xs _)).mpr hn
  exact (hle.and hne).imp (by intro a b hab; rcases hab with ⟨hle,hne⟩; omega)

/-- Ordered physical coordinates: k corresponds to board level 2*(k+2). -/
@[expose] def tapeRows (k : Nat) : List Int := sortOffsets (positiveTapeOffsets k)
@[expose] def leftTapeColumns (k : Nat) : List Int := sortOffsets (negativeTapeOffsets k)
@[expose] def tapeColumns (k : Nat) : List Int := leftTapeColumns k ++ tapeRows k

theorem tapeRows_mem {k : Nat} {t : Int} :
    t ∈ tapeRows k ↔ TapeOffset (k+2) t ∧ 0<t := by
  rw [tapeRows,sortOffsets_mem,positiveTape_mem]
theorem leftTapeColumns_mem {k : Nat} {t : Int} :
    t ∈ leftTapeColumns k ↔ TapeOffset (k+2) t ∧ t<0 := by
  rw [leftTapeColumns,sortOffsets_mem,negativeTape_mem]
theorem tapeColumns_mem {k : Nat} {t : Int} :
    t ∈ tapeColumns k ↔ TapeOffset (k+2) t := by
  rw [tapeColumns,List.mem_append]
  rw [leftTapeColumns,sortOffsets_mem,tapeRows,sortOffsets_mem]
  rw [←List.mem_append,←tape_offsets_complete]

theorem tapeRows_length (k : Nat) : (tapeRows k).length=2^k := by
  rw [tapeRows,sortOffsets_length,positiveTape_length]
theorem leftTapeColumns_length (k : Nat) : (leftTapeColumns k).length=2^k := by
  rw [leftTapeColumns,sortOffsets_length,negativeTape_length]
theorem tapeColumns_length (k : Nat) : (tapeColumns k).length=2*2^k := by
  rw [tapeColumns,List.length_append,leftTapeColumns_length,tapeRows_length]
  omega

theorem tapeRows_strict (k : Nat) : (tapeRows k).Pairwise (fun a b => a<b) :=
  sortOffsets_strict (positiveTape_nodup k)
theorem leftTapeColumns_strict (k : Nat) : (leftTapeColumns k).Pairwise (fun a b => a<b) :=
  sortOffsets_strict (negativeTape_nodup k)
theorem tapeColumns_strict (k : Nat) : (tapeColumns k).Pairwise (fun a b => a<b) := by
  apply List.pairwise_append.mpr
  refine ⟨leftTapeColumns_strict k,tapeRows_strict k,?_⟩
  intro a ha b hb
  have hneg := (leftTapeColumns_mem.mp ha).2
  have hpos := (tapeRows_mem.mp hb).2
  omega

theorem tapeRows_positive_length (k : Nat) : 0<(tapeRows k).length := by
  rw [tapeRows_length]
  exact Nat.pow_pos (by decide)

theorem tapeRows_first (k : Nat) : (tapeRows k)[0]'(tapeRows_positive_length k)=1 := by
  have hmem : (1 : Int) ∈ tapeRows k := sortOffsets_mem.mpr (start_is_positive_tape k)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hmem
  by_cases hz : i=0
  · subst i; exact he
  · have hlt := List.pairwise_iff_getElem.mp (tapeRows_strict k) 0 i (tapeRows_positive_length k) hi (by omega)
    have hp := (tapeRows_mem.mp (List.getElem_mem (tapeRows_positive_length k))).2
    omega

theorem tapeColumns_start_bound (k : Nat) : 2^k<(tapeColumns k).length := by
  rw [tapeColumns_length]
  have hp : 0<2^k := Nat.pow_pos (by decide)
  omega

/-- Logical tape column zero is exactly physical offset +1, at index H. -/
theorem tapeColumns_start (k : Nat) :
    (tapeColumns k)[2^k]'(tapeColumns_start_bound k)=1 := by
  have hlen : (leftTapeColumns k).length ≤ 2^k := by rw [leftTapeColumns_length]; exact Nat.le_refl _
  have he := List.getElem_append_right (as:=leftTapeColumns k) (bs:=tapeRows k)
    (i:=2^k) (h₂:=tapeColumns_start_bound k) hlen
  have hb : 2^k<(tapeColumns k).length := tapeColumns_start_bound k
  have hc : 2^k-(leftTapeColumns k).length<(tapeRows k).length := by
    rw [leftTapeColumns_length,Nat.sub_self]
    exact tapeRows_positive_length k
  calc
    (tapeColumns k)[2^k]'hb = (tapeRows k)[2^k-(leftTapeColumns k).length]'hc := he
    _ = 1 := by simpa only [leftTapeColumns_length,Nat.sub_self] using tapeRows_first k

/-- There is no unlisted selected column between consecutive ordered ones.
    Thus the full physical gap is a single row-transmitter corridor. -/
theorem no_tape_between_columns {k i : Nat} (hi : i+1<(tapeColumns k).length)
    {r : Int} (hl : (tapeColumns k)[i]'(by omega)<r)
    (hr : r<(tapeColumns k)[i+1]'hi) : ¬ TapeOffset (k+2) r := by
  intro ht
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp (tapeColumns_mem.mpr ht)
  have hsort := List.pairwise_iff_getElem.mp (tapeColumns_strict k)
  by_cases hjl : j≤i
  · by_cases heq : j=i
    · subst j; omega
    · have hh := hsort j i hj (by omega) (by omega)
      omega
  · by_cases heq : j=i+1
    · subst j; omega
    · have hh := hsort (i+1) j hi hj (by omega)
      omega

/-- On a channel column inside a physical tape gap, the geometry predicate
    is necessarily blocked. This is the direct input to upper V=b forcing. -/
theorem tape_gap_blocked {k i : Nat} (hi : i+1<(tapeColumns k).length)
    {r : Int} (hl : (tapeColumns k)[i]'(by omega)<r)
    (hr : r<(tapeColumns k)[i+1]'hi) (hmod : r%4=1) : BlockedOffset (k+2) r := by
  have hleft := tapeColumns_mem.mp (List.getElem_mem (show i<(tapeColumns k).length by omega))
  have hright := tapeColumns_mem.mp (List.getElem_mem hi)
  have hnot := no_tape_between_columns hi hl hr
  classical
  by_cases hb : BlockedOffset (k+2) r
  · exact hb
  · exact False.elim (hnot ⟨by have := hleft.1; omega,by have := hright.2.1; omega,hmod,hb⟩)

#print axioms tapeColumns_start
#print axioms tape_gap_blocked
end K230Verification
