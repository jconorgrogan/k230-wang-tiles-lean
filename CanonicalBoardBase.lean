module
public import LevelTwoRaw
public import ChannelCompleteness
public import CanonicalBoardContract
public import Mathlib.Tactic.IntervalCases
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace K230Verification
open K230Concrete

theorem decorate_base_projection (g : Nat × Nat × Nat) (t : Quad TMColor) :
    fullBase (decorate g t)=⟨(Wang156.tile g.1).n,(Wang156.tile g.1).e,(Wang156.tile g.1).s,(Wang156.tile g.1).w⟩ := rfl

theorem levelTwo_channel_projection (v : Nat) (l b : Bool) (x y : Nat) :
    fullChannels (levelTwoTile v l b x y)=levelTwoChannels l b x y := by
  apply unpack_pack_channels
  all_goals simp only [levelTwoChannels]; split_ifs <;> decide

theorem levelTwo_tm_projection (v : Nat) (l b : Bool) (x y : Nat) :
    fullTM (levelTwoTile v l b x y)=levelTwoTM x y := rfl

@[expose] def canonicalBoardZero (v : Fin 4) (left bottom : Int → Bool) :
    CanonicalBoard 0 v.val left bottom where
  patch := levelTwoRawSquare v (left 1) (bottom 1)
  base := by
    intro x y hx hy
    change fullBase (decorate (levelTwoGroup v.val (left 1) (bottom 1) x y) (levelTwoTM x y))=_
    rw [decorate_base_projection]
    have h : redBoard 0 v.val x y=boardCore v.val x y := by
      simp only [redBoard, squareSize, Nat.mul_zero, width, Nat.div_one, Nat.mod_one, expanded]
    exact congrArg baseTileQuad h.symm
  west := by
    intro j hj
    change j≤4 at hj
    change (fullChannels (levelTwoTile v.val (left 1) (bottom 1) 0 j)).w = incomingOuterDigit left ((j:Int)-2) ∧ (fullTM (levelTwoTile v.val (left 1) (bottom 1) 0 j)).w=.blank
    rw [levelTwo_channel_projection,levelTwo_tm_projection]
    interval_cases j <;> simp [levelTwoChannels,levelTwoTM,tmBlank,incomingOuterDigit]
  east := by
    intro j hj
    change j≤4 at hj
    change (fullChannels (levelTwoTile v.val (left 1) (bottom 1) 4 j)).e = outgoingOuterDigit ((j:Int)-2) ∧ (fullTM (levelTwoTile v.val (left 1) (bottom 1) 4 j)).e=.blank
    rw [levelTwo_channel_projection,levelTwo_tm_projection]
    interval_cases j <;> simp [levelTwoChannels,levelTwoTM,tmBlank,outgoingOuterDigit]
  south := by
    intro j hj
    change j≤4 at hj
    change (fullChannels (levelTwoTile v.val (left 1) (bottom 1) j 0)).s = incomingOuterDigit bottom ((j:Int)-2) ∧ (fullTM (levelTwoTile v.val (left 1) (bottom 1) j 0)).s=.blank
    rw [levelTwo_channel_projection,levelTwo_tm_projection]
    interval_cases j <;> simp [levelTwoChannels,levelTwoTM,tmBlank,incomingOuterDigit]
  north := by
    intro j hj
    change j≤4 at hj
    change (fullChannels (levelTwoTile v.val (left 1) (bottom 1) j 4)).n = outgoingOuterDigit ((j:Int)-2) ∧ (fullTM (levelTwoTile v.val (left 1) (bottom 1) j 4)).n=.blank
    rw [levelTwo_channel_projection,levelTwo_tm_projection]
    interval_cases j <;> simp [levelTwoChannels,levelTwoTM,tmBlank,outgoingOuterDigit]

theorem canonicalBoard_zero_exists (v : Fin 4) (left bottom : Int → Bool) :
    Nonempty (CanonicalBoard 0 v.val left bottom) := ⟨canonicalBoardZero v left bottom⟩
end K230Verification
