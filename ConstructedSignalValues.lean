module
public import ConstructedChannels
public import ConcreteRoleExtensions
public section
namespace K230Verification

theorem channelCode_zero_iff (c : Channel) : channelCode c=1 ↔ c=.zero := by cases c <;> decide

theorem innerChannel_zero_iff {N : Nat} (hN : 2≤N) (r s : Int) :
    innerChannel N (BoardCovered N r) s=.zero ↔ ¬BlockedOffset N r := by
  simp only [innerChannel,if_neg (show N≠1 by omega)]
  exact board_zero_iff_free (segmentChannel_compatible _ _)

theorem innerChannel_upper_b {N : Nat} (hN : 2≤N) {r s : Int}
    (hb : BlockedOffset N r) (hs : 0≤s) : innerChannel N (BoardCovered N r) s=.b := by
  simp only [innerChannel,if_neg (show N≠1 by omega)]
  exact board_upper_blocked_is_b hb hs (segmentChannel_compatible _ _)

theorem pieceV_zero_iff {N : Nat} (hN : 2≤N) (bottom : Int → Channel) {r s : Int}
    (hr : r%4=1) (hs : -(boardHalf N : Int)≤s ∧ s<(boardHalf N : Int)) :
    pieceV N bottom r s=1 ↔ ¬BlockedOffset N r := by
  rw [pieceV_inner N bottom r s hr hs,channelCode_zero_iff,innerChannel_zero_iff hN]

theorem pieceH_zero_iff {N : Nat} (hN : 2≤N) (left : Int → Channel) {r s : Int}
    (hs : s%4=1) (hr : -(boardHalf N : Int)≤r ∧ r<(boardHalf N : Int)) :
    pieceH N left r s=1 ↔ ¬BlockedOffset N s :=
  pieceV_zero_iff hN left hs hr

theorem pieceV_tape_zero {N : Nat} (hN : 2≤N) (bottom : Int → Channel) {r s : Int}
    (hr : TapeOffset N r) (hs : -(boardHalf N : Int)≤s ∧ s<(boardHalf N : Int)) :
    pieceV N bottom r s=1 := (pieceV_zero_iff hN bottom hr.2.2.1 hs).mpr hr.2.2.2

theorem pieceH_tape_zero {N : Nat} (hN : 2≤N) (left : Int → Channel) {r s : Int}
    (hs : TapeOffset N s) (hr : -(boardHalf N : Int)≤r ∧ r<(boardHalf N : Int)) :
    pieceH N left r s=1 := pieceV_tape_zero hN left hs hr

theorem pieceV_one_iff_tape {N : Nat} (hN : 2≤N) (bottom : Int → Channel) {r s : Int}
    (hr : -(boardHalf N : Int)<r ∧ r<(boardHalf N : Int))
    (hs : -(boardHalf N : Int)≤s ∧ s<(boardHalf N : Int)) :
    pieceV N bottom r s=1 ↔ TapeOffset N r := by
  constructor
  · intro h
    have hm := (pieceV_presence N bottom r s).mp (by omega)
    exact ⟨hr.1,hr.2,hm,(pieceV_zero_iff hN bottom hm hs).mp h⟩
  · intro h
    exact pieceV_tape_zero hN bottom h hs

theorem pieceH_one_iff_tape {N : Nat} (hN : 2≤N) (left : Int → Channel) {r s : Int}
    (hs : -(boardHalf N : Int)<s ∧ s<(boardHalf N : Int))
    (hr : -(boardHalf N : Int)≤r ∧ r<(boardHalf N : Int)) :
    pieceH N left r s=1 ↔ TapeOffset N s := pieceV_one_iff_tape hN left hs hr

theorem pieceV_upper_b {N : Nat} (hN : 2≤N) (bottom : Int → Channel) {r s : Int}
    (hm : r%4=1) (hb : BlockedOffset N r)
    (hs : 0≤s ∧ s<(boardHalf N : Int)) : pieceV N bottom r s=3 := by
  have hp := board_half_pos N
  rw [pieceV_inner N bottom r s hm ⟨by omega,hs.2⟩,innerChannel_upper_b hN hb hs.1]
  rfl

theorem pieceV_upper_nonfree {N : Nat} (hN : 2≤N) (bottom : Int → Channel) {r s : Int}
    (hr : -(boardHalf N : Int)<r ∧ r<(boardHalf N : Int))
    (hnot : ¬TapeOffset N r) (hs : 0≤s ∧ s<(boardHalf N : Int)) :
    pieceV N bottom r s=0 ∨ pieceV N bottom r s=3 := by
  by_cases hm : r%4=1
  · right
    have hb : BlockedOffset N r := by
      classical
      by_cases hb : BlockedOffset N r
      · exact hb
      · exact False.elim (hnot ⟨hr.1,hr.2,hm,hb⟩)
    exact pieceV_upper_b hN bottom hm hb hs
  · exact Or.inl (pieceV_absent N bottom r s hm)

theorem pieceV_initial_values {N : Nat} (hN : 2≤N) (bottom : Int → Channel) {r : Int}
    (hr : -(boardHalf N : Int)<r ∧ r<(boardHalf N : Int)) :
    pieceV N bottom r 0=0 ∨ pieceV N bottom r 0=1 ∨ pieceV N bottom r 0=3 := by
  classical
  have hp := board_half_pos N
  by_cases ht : TapeOffset N r
  · exact Or.inr (Or.inl (pieceV_tape_zero hN bottom ht ⟨by omega,by omega⟩))
  · rcases pieceV_upper_nonfree hN bottom (s:=0) hr ht ⟨by omega,by omega⟩ with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

#print axioms pieceV_one_iff_tape
#print axioms pieceV_upper_nonfree
end K230Verification
