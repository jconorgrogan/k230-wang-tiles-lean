module
public import RoutedBoard
public section
namespace K230Verification

theorem physicalColumn_surjective {k : Nat} {r : Int} (hr : TapeOffset (k+2) r) :
    ∃ (i : Int) (hi : InTape (2^k) i), physicalColumn k i hi=r := by
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp (tapeColumns_mem.mpr hr)
  have hlen := tapeColumns_length k
  have hi : InTape (2^k) ((j : Int)-(2^k : Nat)) := by unfold InTape; omega
  refine ⟨(j : Int)-(2^k : Nat),hi,?_⟩
  have hx : (((j : Int)-(2^k : Nat))+(2^k : Nat)).toNat=j := by omega
  simpa only [physicalColumn,hx] using he

theorem physicalRow_surjective {k : Nat} {r : Int}
    (hr : TapeOffset (k+2) r) (hp : 0<r) :
    ∃ (t : Nat) (ht : t<2^k), physicalRow k t ht=r := by
  obtain ⟨t,ht,he⟩ := List.mem_iff_getElem.mp (tapeRows_mem.mpr ⟨hr,hp⟩)
  have ht' : t<2^k := by rw [←tapeRows_length]; exact ht
  exact ⟨t,ht',he⟩

theorem physicalColumn_le_iff {k : Nat} {i j : Int}
    (hi : InTape (2^k) i) (hj : InTape (2^k) j) :
    physicalColumn k i hi≤physicalColumn k j hj ↔ i≤j := by
  constructor
  · intro h
    by_cases hij : i≤j
    · exact hij
    · have hh := physicalColumn_strict hj hi (by omega); omega
  · intro h
    by_cases hij : i=j
    · subst j; exact Int.le_refl _
    · have hh := physicalColumn_strict hi hj (by omega); omega

theorem physicalRow_le_iff {k t u : Nat} (ht : t<2^k) (hu : u<2^k) :
    physicalRow k t ht≤physicalRow k u hu ↔ t≤u := by
  constructor
  · intro h
    by_cases htu : t≤u
    · exact htu
    · have hh := physicalRow_strict hu ht (by omega); omega
  · intro h
    by_cases htu : t=u
    · subst u; exact Int.le_refl _
    · have hh := physicalRow_strict ht hu (by omega); omega

theorem physical_column_gap_not_free {k : Nat} {i r : Int}
    (hi : InTape (2^k) i) (hj : InTape (2^k) (i+1))
    (hl : physicalColumn k i hi<r) (hr : r<physicalColumn k (i+1) hj) :
    ¬TapeOffset (k+2) r := by
  intro hf
  obtain ⟨j,hj',he⟩ := physicalColumn_surjective hf
  have hlt : i<j := by
    by_cases hh : i<j
    · exact hh
    · have hle := (physicalColumn_le_iff hj' hi).mpr (by omega); omega
  have hgt : j<i+1 := by
    by_cases hh : j<i+1
    · exact hh
    · have hle := (physicalColumn_le_iff hj hj').mpr (by omega); omega
  omega

theorem physical_column_left_not_free {k : Nat} {r : Int}
    (hi : InTape (2^k) (-(2^k : Nat)))
    (hr : r<physicalColumn k (-(2^k : Nat)) hi) : ¬TapeOffset (k+2) r := by
  intro hf
  obtain ⟨j,hj,he⟩ := physicalColumn_surjective hf
  have hle := (physicalColumn_le_iff hi hj).mpr hj.1
  omega

theorem physical_column_right_not_free {k : Nat} {r : Int}
    (hi : InTape (2^k) ((2^k : Nat)-1))
    (hr : physicalColumn k ((2^k : Nat)-1) hi<r) : ¬TapeOffset (k+2) r := by
  intro hf
  obtain ⟨j,hj,he⟩ := physicalColumn_surjective hf
  have hle := (physicalColumn_le_iff hj hi).mpr (by have := hj.2; omega)
  omega

theorem timeY_nonneg {k t : Nat} (ht : t≤2^k) : 0≤timeY k t ht := by
  by_cases hz : t=0
  · subst t; rw [timeY_zero]; omega
  · have hpos := (physicalRow_mem (show t-1<2^k by omega)).2
    simpa only [timeY,dif_neg hz] using (show 0≤physicalRow k (t-1) (by omega) by omega)

theorem physical_row_gap_not_free {k t : Nat} {r : Int} (ht : t<2^k)
    (hl : timeY k t (by omega)<r) (hr : r<physicalRow k t ht) :
    ¬TapeOffset (k+2) r := by
  intro hf
  have hpos : 0<r := by have := timeY_nonneg (show t≤2^k by omega); omega
  obtain ⟨u,hu,he⟩ := physicalRow_surjective hf hpos
  have hut : u<t := by
    by_cases hh : u<t
    · exact hh
    · have hle := (physicalRow_le_iff ht hu).mpr (by omega); omega
  have hz : t≠0 := by omega
  have hup : u≤t-1 := by omega
  have hle := (physicalRow_le_iff hu (show t-1<2^k by omega)).mpr hup
  have hy : timeY k t (by omega)=physicalRow k (t-1) (by omega) := by simp only [timeY,dif_neg hz]
  rw [hy] at hl
  omega

theorem interior_channel_not_free_blocked {n : Nat} {r : Int}
    (hl : -(boardHalf n : Int)<r) (hr : r<(boardHalf n : Int))
    (hm : r%4=1) (hn : ¬TapeOffset n r) : BlockedOffset n r := by
  classical
  by_cases hb : BlockedOffset n r
  · exact hb
  · exact False.elim (hn ⟨hl,hr,hm,hb⟩)

#print axioms physicalColumn_surjective
#print axioms physical_column_gap_not_free
#print axioms physical_row_gap_not_free
end K230Verification
