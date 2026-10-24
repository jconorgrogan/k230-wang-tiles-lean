module
public import PieceChannelLegality
public import CanonicalBoardContract
public section
namespace K230Verification
@[expose] def outerChoice (f : Int → Bool) (t : Int) : Channel := if f t then .b else .a
@[expose] noncomputable def boolPieceChannels (N : Nat) (left bottom : Int → Bool) (r s : Int) : Quad Nat :=
  pieceChannels N (outerChoice left) (outerChoice bottom) r s

theorem outerChoice_allowed (f : Int → Bool) (t : Int) : EndAllows .outerLeft (outerChoice f t) := by
  unfold outerChoice
  split <;> simp [EndAllows]

theorem boolPieceChannels_west (N : Nat) (left bottom : Int → Bool) (s : Int) :
    (boolPieceChannels N left bottom (-(boardHalf N:Int)) s).w=incomingOuterDigit left s := by
  by_cases hm : s%4=1
  · change pieceH N (outerChoice left) (-(boardHalf N:Int)-1) s=_
    rw [pieceH_left_outer N _ s hm]
    simp [incomingOuterDigit,hm,outerChoice]
    split <;> rfl
  · change pieceH N (outerChoice left) (-(boardHalf N:Int)-1) s=_
    rw [pieceH_absent _ _ _ _ hm]
    simp [incomingOuterDigit,hm]

theorem boolPieceChannels_east (N : Nat) (left bottom : Int → Bool) (s : Int) :
    (boolPieceChannels N left bottom (boardHalf N) s).e=outgoingOuterDigit s := by
  by_cases hm : s%4=1
  · change pieceH N (outerChoice left) (boardHalf N) s=_
    rw [pieceH_right_outer N _ s hm]
    simp [outgoingOuterDigit,hm]
  · change pieceH N (outerChoice left) (boardHalf N) s=_
    rw [pieceH_absent _ _ _ _ hm]
    simp [outgoingOuterDigit,hm]

theorem boolPieceChannels_south (N : Nat) (left bottom : Int → Bool) (r : Int) :
    (boolPieceChannels N left bottom r (-(boardHalf N:Int))).s=incomingOuterDigit bottom r :=
  boolPieceChannels_west N bottom left r

theorem boolPieceChannels_north (N : Nat) (left bottom : Int → Bool) (r : Int) :
    (boolPieceChannels N left bottom r (boardHalf N)).n=outgoingOuterDigit r :=
  boolPieceChannels_east N bottom left r

theorem boolPieceChannels_match_h (N : Nat) (left bottom : Int → Bool) (r s : Int) :
    (boolPieceChannels N left bottom r s).e=(boolPieceChannels N left bottom (r+1) s).w :=
  pieceChannels_match_h _ _ _ _ _
theorem boolPieceChannels_match_v (N : Nat) (left bottom : Int → Bool) (r s : Int) :
    (boolPieceChannels N left bottom r s).n=(boolPieceChannels N left bottom r (s+1)).s :=
  pieceChannels_match_v _ _ _ _ _
theorem boolPieceChannels_legal (n v : Nat) (hn : 1≤n) (hv : v<4)
    (left bottom : Int → Bool) (r s : Int)
    (hr : -(boardHalf (n+1):Int)≤r ∧ r≤boardHalf (n+1))
    (hs : -(boardHalf (n+1):Int)≤s ∧ s≤boardHalf (n+1))
    (he : ¬BoardCovered (n+1) r s) :
    ChannelLegal (K230Concrete.boardAtRelative n v r s).val (boolPieceChannels (n+1) left bottom r s) :=
  pieceChannels_legal n v hn hv _ _ (fun t _ => outerChoice_allowed left t)
    (fun t _ => outerChoice_allowed bottom t) r s hr hs he

#print axioms boolPieceChannels_legal
end K230Verification
