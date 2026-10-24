module
public import GridGaps
public section
namespace K230Verification

@[expose] def cutIndex (xs : List Int) (x : Int) : Nat := xs.countP (fun y => decide (y≤x))

theorem cutIndex_le (xs : List Int) (x : Int) : cutIndex xs x≤xs.length := List.countP_le_length

theorem cutIndex_zero {xs : List Int} {x : Int} (h : ∀ y∈xs, x<y) : cutIndex xs x=0 := by
  apply List.countP_eq_zero.mpr
  intro y hy
  simpa using (show ¬y≤x by have := h y hy; omega)

theorem cutIndex_full {xs : List Int} {x : Int} (h : ∀ y∈xs, y≤x) : cutIndex xs x=xs.length := by
  apply List.countP_eq_length.mpr
  intro y hy
  simpa using h y hy

theorem cutIndex_pos {xs : List Int} {x : Int} (hx : x∈xs) : 0<cutIndex xs x := by
  apply List.countP_pos_iff.mpr
  exact ⟨x,hx,by simp⟩

theorem cutIndex_at {xs : List Int} (hs : xs.Pairwise (fun a b => a<b))
    (i : Nat) (hi : i<xs.length) : cutIndex xs xs[i]=i+1 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp hs
    cases i with
    | zero =>
      have hz : cutIndex xs a=0 := cutIndex_zero ha
      simpa [cutIndex,List.countP_cons] using hz
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      have hb : a≤xs[i] := by have := ha _ (List.getElem_mem hi'); omega
      have hh := ih ht i hi'
      simpa [cutIndex,List.countP_cons,hb] using hh

theorem cutIndex_before {xs : List Int} (hs : xs.Pairwise (fun a b => a<b))
    (i : Nat) (hi : i<xs.length) : cutIndex xs (xs[i]-1)=i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp hs
    cases i with
    | zero =>
      change cutIndex (a::xs) (a-1)=0
      apply cutIndex_zero
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · omega
      · have := ha _ hy; omega
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      have hb : a≤xs[i]-1 := by have := ha _ (List.getElem_mem hi'); omega
      have hh := ih ht i hi'
      simpa [cutIndex,List.countP_cons,hb] using hh

theorem cutIndex_step {xs : List Int} {x : Int} (hx : x∉xs) : cutIndex xs x=cutIndex xs (x-1) := by
  unfold cutIndex
  rw [List.countP_eq_length_filter,List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro y hy
  have hne : y≠x := by intro he; subst y; exact hx hy
  by_cases h1 : y≤x
  · have h2 : y≤x-1 := by omega
    simp [h1,h2]
  · have h2 : ¬y≤x-1 := by omega
    simp [h1,h2]

@[expose] def columnRank (k : Nat) (r : Int) : Int :=
  (cutIndex (tapeColumns k) r : Int)-(2^k : Nat)-1
@[expose] def timeRank (k : Nat) (s : Int) : Nat := cutIndex (tapeRows k) s

theorem columnRank_physical {k : Nat} {i : Int} (hi : InTape (2^k) i) :
    columnRank k (physicalColumn k i hi)=i := by
  have h := cutIndex_at (tapeColumns_strict k) (i+(2^k : Nat)).toNat
    (show (i+(2^k : Nat)).toNat<(tapeColumns k).length by
      rw [tapeColumns_length]
      have hnon := Int.toNat_of_nonneg (show 0≤i+(2^k : Nat) by have := hi.1; omega)
      have := hi.2; omega)
  change cutIndex (tapeColumns k) (physicalColumn k i hi)=(i+(2^k : Nat)).toNat+1 at h
  unfold columnRank
  rw [h]
  have hnon := Int.toNat_of_nonneg (show 0≤i+(2^k : Nat) by have := hi.1; omega)
  omega

theorem columnRank_before_physical {k : Nat} {i : Int} (hi : InTape (2^k) i) :
    columnRank k (physicalColumn k i hi-1)=i-1 := by
  have h := cutIndex_before (tapeColumns_strict k) (i+(2^k : Nat)).toNat
    (show (i+(2^k : Nat)).toNat<(tapeColumns k).length by
      rw [tapeColumns_length]
      have hnon := Int.toNat_of_nonneg (show 0≤i+(2^k : Nat) by have := hi.1; omega)
      have := hi.2; omega)
  change cutIndex (tapeColumns k) (physicalColumn k i hi-1)=(i+(2^k : Nat)).toNat at h
  unfold columnRank
  rw [h]
  have hnon := Int.toNat_of_nonneg (show 0≤i+(2^k : Nat) by have := hi.1; omega)
  omega

theorem timeRank_physical {k t : Nat} (ht : t<2^k) : timeRank k (physicalRow k t ht)=t+1 :=
  cutIndex_at (tapeRows_strict k) t (by rw [tapeRows_length]; exact ht)

theorem timeRank_before_physical {k t : Nat} (ht : t<2^k) : timeRank k (physicalRow k t ht-1)=t :=
  cutIndex_before (tapeRows_strict k) t (by rw [tapeRows_length]; exact ht)

theorem columnRank_step {k : Nat} {r : Int} (hr : ¬TapeOffset (k+2) r) :
    columnRank k r=columnRank k (r-1) := by
  unfold columnRank
  rw [cutIndex_step (fun hm => hr (tapeColumns_mem.mp hm))]

theorem timeRank_step {k : Nat} {s : Int} (hs : ¬(TapeOffset (k+2) s ∧ 0<s)) :
    timeRank k s=timeRank k (s-1) :=
  cutIndex_step (fun hm => hs (tapeRows_mem.mp hm))

#print axioms cutIndex_at
#print axioms columnRank_physical
#print axioms timeRank_physical
end K230Verification
