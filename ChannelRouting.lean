module
public import ActualBoardData
public import ExposedActualChannels
public import GridGaps
public import ConcreteRoutingMasks
public section
namespace K230Verification

/-- Actual traces of the chosen original tiling. The two clauses are
    discharged by the exact red-ring geometry, not postulated channels. -/
structure BoardTraces (T : Cell → Fin 11487) (b : Cell) (k : Nat) : Prop where
  vertical : ∀ r s : Int,
    (-(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2)) →
    (-(boardHalf (k+2) : Int)<s ∧ s<boardHalf (k+2)) → r%4=1 →
    ¬BoardCovered (k+2) r s →
    SegmentCompatible (BoardCovered (k+2) r) s (verticalTrace T b (k+2) r s)
  horizontal : ∀ r s : Int,
    (-(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2)) →
    (-(boardHalf (k+2) : Int)<s ∧ s<boardHalf (k+2)) → s%4=1 →
    ¬BoardCovered (k+2) s r →
    SegmentCompatible (BoardCovered (k+2) s) r (horizontalTrace T b (k+2) s r)

theorem free_column_not_covered {n : Nat} {r s : Int} (hr : ¬BlockedOffset n r) :
    ¬BoardCovered n r s := by
  rintro ⟨_,_,m,hm,hmn,hbr,_⟩
  exact hr ⟨m,hm,hmn,hbr⟩

theorem free_row_not_covered {n : Nat} {r s : Int} (hs : ¬BlockedOffset n s) :
    ¬BoardCovered n r s := by
  rintro ⟨_,_,m,hm,hmn,_,hbs⟩
  exact hs ⟨m,hm,hmn,hbs⟩

theorem centerGroup_n_code (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) :
    (groupChannel (centerGroup T b N r s)).n=vCode T (centerCell b N r s) := by
  rw [centerGroup_channels]; rfl

theorem centerGroup_e_code (T : Cell → Fin 11487) (b : Cell) (N : Nat) (r s : Int) :
    (groupChannel (centerGroup T b N r s)).e=hCode T (centerCell b N r s) := by
  rw [centerGroup_channels]; rfl

theorem centerGroup_exposed_copy (T : Cell → Fin 11487) (k v : Nat) (b : Cell)
    (hv : v<4) (hb : FullBoardAt T (k+1) v b) (r s : Int)
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2))
    (hs : -(boardHalf (k+2) : Int)<s ∧ s<boardHalf (k+2))
    (he : ¬BoardCovered (k+2) r s) :
    (groupChannel (centerGroup T b (k+2) r s)).e=(groupChannel (centerGroup T b (k+2) r s)).w ∧
    (groupChannel (centerGroup T b (k+2) r s)).n=(groupChannel (centerGroup T b (k+2) r s)).s := by
  have hn := fullBoard_exposed_not_boundary T (k+1) v b hv hb r s hr hs he
  have hc := concrete_channel_copy _ (centerGroup_mem T b (k+2) r s)
  exact ⟨hc.1 hn.1,hc.2 hn.2⟩

namespace BoardTraces
variable {T : Cell → Fin 11487} {b : Cell} {k : Nat}

theorem v_zero (R : BoardTraces T b k) {r s : Int} (hr : TapeOffset (k+2) r)
    (hs : -(boardHalf (k+2) : Int)<s ∧ s<boardHalf (k+2)) :
    (groupChannel (centerGroup T b (k+2) r s)).n=1 := by
  have hc := R.vertical r s ⟨hr.1,hr.2.1⟩ hs hr.2.2.1 (free_column_not_covered hr.2.2.2)
  have hz := (board_zero_iff_free hc).mpr hr.2.2.2
  change decodeChannel (vCode T (centerCell b (k+2) r s))=.zero at hz
  rw [centerGroup_n_code]
  exact (decode_zero_iff _).mp hz

theorem h_zero (R : BoardTraces T b k) {r s : Int} (hs : TapeOffset (k+2) s)
    (hr : -(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2)) :
    (groupChannel (centerGroup T b (k+2) r s)).e=1 := by
  have hc := R.horizontal r s hr ⟨hs.1,hs.2.1⟩ hs.2.2.1 (free_column_not_covered hs.2.2.2)
  have hz := (board_zero_iff_free hc).mpr hs.2.2.2
  change decodeChannel (hCode T (centerCell b (k+2) r s))=.zero at hz
  rw [centerGroup_e_code]
  exact (decode_zero_iff _).mp hz

theorem v_upper (R : BoardTraces T b k) {v : Nat} (hb : FullBoardAt T (k+1) v b)
    {r s : Int} (hr : -(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2))
    (hs : -(boardHalf (k+2) : Int)<s ∧ s<boardHalf (k+2)) (hm : r%4=1)
    (hblock : BlockedOffset (k+2) r) (hpos : 0≤s) (hexp : ¬BoardCovered (k+2) r s) :
    (groupChannel (centerGroup T b (k+2) r s)).n=3 := by
  have hc := R.vertical r s hr hs hm hexp
  have hz := board_upper_blocked_is_b hblock hpos hc
  change decodeChannel (vCode T (centerCell b (k+2) r s))=.b at hz
  have hp := centerGroup_presence T k v b hb r s ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  have hnz := hp.2.2.1.mpr hm
  have hcode := centerGroup_n_code T b (k+2) r s
  have hbound : (groupChannel (centerGroup T b (k+2) r s)).n<4 := Nat.mod_lt _ (by decide)
  rw [←hcode] at hz
  exact (decode_b_iff _ ⟨by omega,hbound⟩).mp hz

theorem initial_channel (R : BoardTraces T b k) {v : Nat} (hb : FullBoardAt T (k+1) v b)
    {r : Int} (hr : -(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2)) :
    (groupChannel (centerGroup T b (k+2) r 0)).n=0 ∨
    (groupChannel (centerGroup T b (k+2) r 0)).n=1 ∨
    (groupChannel (centerGroup T b (k+2) r 0)).n=3 := by
  have hp := board_half_pos (k+2)
  have hs : -(boardHalf (k+2) : Int)<0 ∧ (0 : Int)<boardHalf (k+2) := by omega
  by_cases hz : (groupChannel (centerGroup T b (k+2) r 0)).n=0
  · exact Or.inl hz
  · have hm := (centerGroup_presence T k v b hb r 0 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).2.2.1.mp hz
    classical
    by_cases hblock : BlockedOffset (k+2) r
    · exact Or.inr (Or.inr (R.v_upper hb hr hs hm hblock (by omega) board_center_free))
    · exact Or.inr (Or.inl (R.v_zero ⟨hr.1,hr.2,hm,hblock⟩ hs))

theorem row_copy (R : BoardTraces T b k) {v : Nat} (hv : v<4) (hb : FullBoardAt T (k+1) v b)
    {r s : Int} (hr : -(boardHalf (k+2) : Int)<r ∧ r<boardHalf (k+2))
    (hs : TapeOffset (k+2) s) (hpos : 0≤s) (hnot : ¬TapeOffset (k+2) r) :
    (centerTM T b (k+2) r s).e=(centerTM T b (k+2) r s).w := by
  have hc := centerGroup_exposed_copy T k v b hv hb r s hr ⟨hs.1,hs.2.1⟩
    (free_row_not_covered hs.2.2.2)
  have he := R.h_zero hs hr
  have hw : (groupChannel (centerGroup T b (k+2) r s)).w=1 := hc.1.symm.trans he
  have hn : (groupChannel (centerGroup T b (k+2) r s)).n=0 ∨
      (groupChannel (centerGroup T b (k+2) r s)).n=3 := by
    by_cases hz : (groupChannel (centerGroup T b (k+2) r s)).n=0
    · exact Or.inl hz
    · have hm := (centerGroup_presence T k v b hb r s ⟨by omega,by omega⟩ ⟨by have := hs.1; omega,by have := hs.2.1; omega⟩).2.2.1.mp hz
      have hblock := interior_channel_not_free_blocked hr.1 hr.2 hm hnot
      exact Or.inr (R.v_upper hb hr ⟨hs.1,hs.2.1⟩ hm hblock hpos (free_row_not_covered hs.2.2.2))
  have hf := concrete_EW_zero_noncomp_row _ (centerGroup_mem T b (k+2) r s) he hw hn
  have ht := centerTM_mem T b (k+2) r s
  rw [hf] at ht
  exact (concrete_row_transmitter_shape ht).2.2

theorem column_copy (R : BoardTraces T b k) {v : Nat} (hv : v<4) (hb : FullBoardAt T (k+1) v b)
    {r s : Int} (hr : TapeOffset (k+2) r)
    (hs : -(boardHalf (k+2) : Int)<s ∧ s<boardHalf (k+2)) (hnot : ¬TapeOffset (k+2) s)
    (hdata : (centerTM T b (k+2) r s).s≠.blank) :
    (centerTM T b (k+2) r s).n=(centerTM T b (k+2) r s).s := by
  have hc := centerGroup_exposed_copy T k v b hv hb r s ⟨hr.1,hr.2.1⟩ hs
    (free_column_not_covered hr.2.2.2)
  have hn := R.v_zero hr hs
  have hS : (groupChannel (centerGroup T b (k+2) r s)).s=1 := hc.2.symm.trans hn
  have he : (groupChannel (centerGroup T b (k+2) r s)).e≠1 := by
    intro hone
    have hp := centerGroup_presence T k v b hb r s ⟨by have := hr.1; omega,by have := hr.2.1; omega⟩ ⟨by omega,by omega⟩
    have hm : s%4=1 := hp.1.mp (by omega)
    have hblock := interior_channel_not_free_blocked hs.1 hs.2 hm hnot
    have htrace := R.horizontal r s ⟨hr.1,hr.2.1⟩ hs hm (free_row_not_covered hr.2.2.2)
    have hzero : horizontalTrace T b (k+2) s r=.zero := by
      change decodeChannel (hCode T (centerCell b (k+2) r s))=.zero
      rw [←centerGroup_e_code,hone]; rfl
    exact ((board_zero_iff_free htrace).mp hzero) hblock
  have hf := concrete_NS_zero_not_H_column _ (centerGroup_mem T b (k+2) r s) hn hS he
  exact (concrete_column_nonblank_copies hf (centerTM_mem T b (k+2) r s) hdata).1

theorem computation (R : BoardTraces T b k) {r s : Int} (hr : TapeOffset (k+2) r)
    (hs : TapeOffset (k+2) s) (hdata : (centerTM T b (k+2) r s).s≠.blank) :
    centerTM T b (k+2) r s ∈ tmComp :=
  concrete_NE_zero_nonblank_comp (centerGroup_mem T b (k+2) r s)
    (R.v_zero hr ⟨hs.1,hs.2.1⟩) (R.h_zero hs ⟨hr.1,hr.2.1⟩)
    (centerTM_mem T b (k+2) r s) hdata
end BoardTraces

#print axioms BoardTraces.row_copy
#print axioms BoardTraces.column_copy
#print axioms BoardTraces.computation
end K230Verification
