module
public import ChannelConstruction
public import ActualChannelMasks
public section
set_option maxHeartbeats 0
namespace K230Verification

@[expose] noncomputable def innerChannel (N : Nat) (covered : Int → Prop) (x : Int) : Channel :=
  if N=1 then .a else segmentChannel covered x

@[expose] noncomputable def pieceH (N : Nat) (left : Int → Channel) (r s : Int) : Nat :=
  if s%4=1 then
    if r=-(boardHalf N:Int)-1 then channelCode (left s)
    else if r=(boardHalf N:Int) then 3
    else channelCode (innerChannel N (BoardCovered N s) r)
  else 0
@[expose] noncomputable def pieceV (N : Nat) (bottom : Int → Channel) (r s : Int) : Nat :=
  if r%4=1 then
    if s=-(boardHalf N:Int)-1 then channelCode (bottom r)
    else if s=(boardHalf N:Int) then 3
    else channelCode (innerChannel N (BoardCovered N r) s)
  else 0
@[expose] noncomputable def pieceChannels (N : Nat) (left bottom : Int → Channel) (r s : Int) : Quad Nat :=
  ⟨pieceV N bottom r s,pieceH N left r s,pieceV N bottom r (s-1),pieceH N left (r-1) s⟩

theorem channelCode_pos (c : Channel) : 0<channelCode c := by cases c <;> decide
theorem channelCode_lt_four (c : Channel) : channelCode c<4 := by cases c <;> decide

theorem code_inner_left {c : Channel} (h : EndAllows .innerLeft c) : channelCode c=1 ∨ channelCode c=2 := by
  cases c <;> simp_all [EndAllows,channelCode]
theorem code_inner_right {c : Channel} (h : EndAllows .innerRight c) : channelCode c=1 ∨ channelCode c=3 := by
  cases c <;> simp_all [EndAllows,channelCode]
theorem code_outer_left {c : Channel} (h : EndAllows .outerLeft c) : channelCode c=2 ∨ channelCode c=3 := by
  cases c <;> simp_all [EndAllows,channelCode]

theorem pieceH_bounds (N : Nat) (left : Int → Channel) (r s : Int) : pieceH N left r s<4 := by
  unfold pieceH
  split
  · split
    · exact channelCode_lt_four _
    · split
      · decide
      · exact channelCode_lt_four _
  · decide

theorem pieceV_bounds (N : Nat) (bottom : Int → Channel) (r s : Int) : pieceV N bottom r s<4 := by
  exact pieceH_bounds N bottom s r

theorem pieceH_presence (N : Nat) (left : Int → Channel) (r s : Int) : pieceH N left r s≠0 ↔ s%4=1 := by
  unfold pieceH
  split
  · rename_i h
    simp only [h,iff_true]
    split
    · exact Nat.ne_of_gt (channelCode_pos _)
    · split
      · decide
      · exact Nat.ne_of_gt (channelCode_pos _)
  · simp_all

theorem pieceV_presence (N : Nat) (bottom : Int → Channel) (r s : Int) : pieceV N bottom r s≠0 ↔ r%4=1 := by
  exact pieceH_presence N bottom s r

theorem pieceH_absent (N : Nat) (left : Int → Channel) (r s : Int) (h : s%4≠1) : pieceH N left r s=0 := by
  simp [pieceH,h]
theorem pieceV_absent (N : Nat) (bottom : Int → Channel) (r s : Int) (h : r%4≠1) : pieceV N bottom r s=0 := by
  exact pieceH_absent N bottom s r h

theorem pieceH_inner (N : Nat) (left : Int → Channel) (r s : Int) (hmod : s%4=1)
    (hr : -(boardHalf N:Int)≤r ∧ r<(boardHalf N:Int)) :
    pieceH N left r s=channelCode (innerChannel N (BoardCovered N s) r) := by
  simp [pieceH,hmod,show r≠-(boardHalf N:Int)-1 by omega,show r≠(boardHalf N:Int) by omega]

theorem pieceV_inner (N : Nat) (bottom : Int → Channel) (r s : Int) (hmod : r%4=1)
    (hs : -(boardHalf N:Int)≤s ∧ s<(boardHalf N:Int)) :
    pieceV N bottom r s=channelCode (innerChannel N (BoardCovered N r) s) :=
  pieceH_inner N bottom s r hmod hs

theorem pieceH_left_outer (N : Nat) (left : Int → Channel) (s : Int) (hmod : s%4=1) :
    pieceH N left (-(boardHalf N:Int)-1) s=channelCode (left s) := by simp [pieceH,hmod]

theorem pieceH_right_outer (N : Nat) (left : Int → Channel) (s : Int) (hmod : s%4=1) :
    pieceH N left (boardHalf N) s=3 := by
  have hp := board_half_pos N
  simp [pieceH,hmod,show (boardHalf N:Int)≠-(boardHalf N:Int)-1 by omega]

theorem pieceH_copy (N : Nat) (left : Int → Channel) (r s : Int)
    (hr : -(boardHalf N:Int)<r ∧ r<(boardHalf N:Int))
    (he : ¬BoardCovered N s r) : pieceH N left r s=pieceH N left (r-1) s := by
  by_cases hm : s%4=1
  · rw [pieceH_inner N left r s hm ⟨by omega,hr.2⟩,
      pieceH_inner N left (r-1) s hm ⟨by omega,by omega⟩]
    unfold innerChannel
    split
    · rfl
    · exact congrArg channelCode (segmentChannel_copy he).symm
  · rw [pieceH_absent N left r s hm,pieceH_absent N left (r-1) s hm]

theorem pieceV_copy (N : Nat) (bottom : Int → Channel) (r s : Int)
    (hs : -(boardHalf N:Int)<s ∧ s<(boardHalf N:Int))
    (he : ¬BoardCovered N r s) : pieceV N bottom r s=pieceV N bottom r (s-1) :=
  pieceH_copy N bottom s r hs he

theorem pieceChannels_match_h (N : Nat) (left bottom : Int → Channel) (r s : Int) :
    (pieceChannels N left bottom r s).e=(pieceChannels N left bottom (r+1) s).w := by
  simp [pieceChannels]

theorem pieceChannels_match_v (N : Nat) (left bottom : Int → Channel) (r s : Int) :
    (pieceChannels N left bottom r s).n=(pieceChannels N left bottom r (s+1)).s := by
  simp [pieceChannels]

theorem pieceH_left_masks (N : Nat) (left : Int → Channel) (hN : 2≤N)
    (hl : ∀ s, s%4=1 → EndAllows .outerLeft (left s)) (s : Int) (hm : s%4=1) :
    (pieceH N left (-(boardHalf N:Int)) s=1 ∨ pieceH N left (-(boardHalf N:Int)) s=2) ∧
    (pieceH N left (-(boardHalf N:Int)-1) s=2 ∨ pieceH N left (-(boardHalf N:Int)-1) s=3) := by
  have hp := board_half_pos N
  rw [pieceH_inner N left (-(boardHalf N:Int)) s hm ⟨by omega,by omega⟩,
    pieceH_left_outer N left s hm]
  constructor
  · apply code_inner_left
    simpa only [innerChannel,if_neg (show N≠1 by omega)] using
      (segmentChannel_inner_left (covered:=BoardCovered N s) (H:=(boardHalf N:Int)) (fun _ hc => hc.1))
  · exact code_outer_left (hl s hm)

theorem pieceH_right_masks (N : Nat) (left : Int → Channel) (hN : 2≤N)
    (s : Int) (hm : s%4=1) :
    (pieceH N left ((boardHalf N:Int)-1) s=1 ∨ pieceH N left ((boardHalf N:Int)-1) s=3) ∧
    pieceH N left (boardHalf N) s=3 := by
  have hp := board_half_pos N
  rw [pieceH_inner N left ((boardHalf N:Int)-1) s hm ⟨by omega,by omega⟩,
    pieceH_right_outer N left s hm]
  refine ⟨?_,rfl⟩
  apply code_inner_right
  simpa only [innerChannel,if_neg (show N≠1 by omega)] using
    (segmentChannel_inner_right (covered:=BoardCovered N s) (H:=(boardHalf N:Int)) (fun _ hc => hc.2.1))

theorem pieceV_bottom_masks (N : Nat) (bottom : Int → Channel) (hN : 2≤N)
    (hb : ∀ r, r%4=1 → EndAllows .outerLeft (bottom r)) (r : Int) (hm : r%4=1) :
    (pieceV N bottom r (-(boardHalf N:Int))=1 ∨ pieceV N bottom r (-(boardHalf N:Int))=2) ∧
    (pieceV N bottom r (-(boardHalf N:Int)-1)=2 ∨ pieceV N bottom r (-(boardHalf N:Int)-1)=3) :=
  pieceH_left_masks N bottom hN hb r hm

theorem pieceV_top_masks (N : Nat) (bottom : Int → Channel) (hN : 2≤N)
    (r : Int) (hm : r%4=1) :
    (pieceV N bottom r ((boardHalf N:Int)-1)=1 ∨ pieceV N bottom r ((boardHalf N:Int)-1)=3) ∧
    pieceV N bottom r (boardHalf N)=3 :=
  pieceH_right_masks N bottom hN r hm

#print axioms pieceH_copy
#print axioms pieceChannels_match_h
#print axioms pieceH_left_masks
end K230Verification
