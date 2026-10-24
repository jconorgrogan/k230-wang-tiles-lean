module
public import FullPlaneData
public import SortProof
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Nodup
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification
@[expose] def colorCode : TMColor → Nat
  | .blank => 0
  | .symbol false => 1 | .symbol true => 2
  | .head q a => 3+2*q+(if a then 1 else 0)
  | .move .left q => 1000+2*q
  | .move .right q => 1001+2*q
  | .iL => 2000 | .iR => 2001 | .iH => 2002 | .iX => 2003
@[expose] def quadCode (q : Quad TMColor) : Nat :=
  ((colorCode q.n * 4096 + colorCode q.e) * 4096 + colorCode q.s) * 4096 + colorCode q.w
@[expose] def projectTM (q : Quad FullColor) : Quad TMColor := ⟨q.n.2.2,q.e.2.2,q.s.2.2,q.w.2.2⟩
theorem decorate_injective (g : Nat × Nat × Nat) : Function.Injective (decorate g) := by
  intro a b h
  have hh := congrArg projectTM h
  cases a
  cases b
  simpa [projectTM,decorate] using hh
@[expose] def baseColorCode (c : FullColor) : Nat := c.1*4+c.2.1
@[expose] def baseQuadCode (q : Quad FullColor) : Nat :=
  ((baseColorCode q.n*1024+baseColorCode q.e)*1024+baseColorCode q.s)*1024+baseColorCode q.w
@[expose] def groupCode (g : Nat × Nat × Nat) : Nat := baseQuadCode (decorate g tmBlank)
theorem decorate_groupCode (g : Nat × Nat × Nat) (t : Quad TMColor) :
    baseQuadCode (decorate g t) = groupCode g := rfl
theorem family0_chain : (fastSort 10 ((tmFamily 0).map quadCode)).IsChain (· < ·) := by decide
theorem family1_chain : (fastSort 10 ((tmFamily 1).map quadCode)).IsChain (· < ·) := by decide
theorem family2_chain : (fastSort 10 ((tmFamily 2).map quadCode)).IsChain (· < ·) := by decide
theorem family3_chain : (fastSort 10 ((tmFamily 3).map quadCode)).IsChain (· < ·) := by decide
theorem family4_chain : (fastSort 10 ((tmFamily 4).map quadCode)).IsChain (· < ·) := by decide
theorem family5_chain : (fastSort 10 ((tmFamily 5).map quadCode)).IsChain (· < ·) := by decide
theorem family6_chain : (fastSort 10 ((tmFamily 6).map quadCode)).IsChain (· < ·) := by decide
theorem family7_chain : (fastSort 10 ((tmFamily 7).map quadCode)).IsChain (· < ·) := by decide
theorem family8_chain : (fastSort 10 ((tmFamily 8).map quadCode)).IsChain (· < ·) := by decide
theorem family9_chain : (fastSort 10 ((tmFamily 9).map quadCode)).IsChain (· < ·) := by decide
theorem family10_chain : (fastSort 10 ((tmFamily 10).map quadCode)).IsChain (· < ·) := by decide
theorem family11_chain : (fastSort 10 ((tmFamily 11).map quadCode)).IsChain (· < ·) := by decide
theorem family12_chain : (fastSort 10 ((tmFamily 12).map quadCode)).IsChain (· < ·) := by decide
theorem family13_chain : (fastSort 10 ((tmFamily 13).map quadCode)).IsChain (· < ·) := by decide
theorem family_nodup (k : Nat) (h : k < 14) : (tmFamily k).Nodup := by
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nodup_of_fast_codes quadCode (tmFamily 0) 10 family0_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 1) 10 family1_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 2) 10 family2_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 3) 10 family3_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 4) 10 family4_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 5) 10 family5_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 6) 10 family6_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 7) 10 family7_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 8) 10 family8_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 9) 10 family9_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 10) 10 family10_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 11) 10 family11_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 12) 10 family12_chain
  · exact nodup_of_fast_codes quadCode (tmFamily 13) 10 family13_chain
theorem group_codes_nodup : (exactGroups.toList.map groupCode).Nodup := by decide
theorem groups_family_bound : ∀ g ∈ exactGroups.toList, g.2.2 < 14 := by
  have h : exactGroups.toList.all (fun g => decide (g.2.2 < 14)) = true := by decide
  simpa using List.all_eq_true.mp h
theorem exact_fullplane_nodup : exactFullPlaneTiles.Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro g hg
    exact (family_nodup g.2.2 (groups_family_bound g hg)).map (decorate_injective g)
  · have hp : exactGroups.toList.Pairwise (fun g h => groupCode g ≠ groupCode h) := by
      simpa only [List.Nodup, List.pairwise_map] using group_codes_nodup
    apply hp.imp
    intro g h hne t hg hh
    obtain ⟨a,_,ha⟩ := List.mem_map.mp hg
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hh
    have eq := congrArg baseQuadCode (ha.trans hb.symm)
    exact hne (by simpa only [decorate_groupCode] using eq)
#print axioms exact_fullplane_nodup
end K230Verification
