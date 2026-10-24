module
public import ExactTarget
public import GlobalRecognition
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification
open K230PhaseHierarchy

theorem exact_group_base_checked :
    exactGroups.toList.all (fun g => decide (g.1 < 156)) = true := by decide +kernel

theorem exact_group_base_bound (g : Nat × Nat × Nat) (h : g ∈ exactGroups.toList) :
    g.1 < 156 := by
  exact of_decide_eq_true (List.all_eq_true.mp exact_group_base_checked g h)

theorem indexed_decomposition (i : Fin 11487) :
    ∃ g ∈ exactGroups.toList, ∃ t ∈ tmFamily g.2.2,
      indexedFullTile i = decorate g t := by
  have hm : indexedFullTile i ∈ exactFullPlaneTiles := List.getElem_mem _
  obtain ⟨g,hg,ht⟩ := List.mem_flatMap.mp hm
  obtain ⟨t,ht,he⟩ := List.mem_map.mp ht
  exact ⟨g,hg,t,ht,he.symm⟩

@[expose] noncomputable def indexedGroup (i : Fin 11487) : Nat × Nat × Nat :=
  Classical.choose (indexed_decomposition i)

theorem indexedGroup_spec (i : Fin 11487) : indexedGroup i ∈ exactGroups.toList ∧
    ∃ t ∈ tmFamily (indexedGroup i).2.2, indexedFullTile i = decorate (indexedGroup i) t :=
  Classical.choose_spec (indexed_decomposition i)

@[expose] noncomputable def indexedBase (i : Fin 11487) : Fin 156 :=
  ⟨(indexedGroup i).1,exact_group_base_bound _ (indexedGroup_spec i).1⟩

@[expose] def baseQuad (k : Fin 156) : Quad Nat :=
  let b := Wang156.tile k.val
  ⟨b.n,b.e,b.s,b.w⟩

@[expose] def eraseDecoration (t : Quad FullColor) : Quad Nat :=
  ⟨t.n.1,t.e.1,t.s.1,t.w.1⟩

theorem indexedBase_spec (i : Fin 11487) :
    eraseDecoration (indexedFullTile i) = baseQuad (indexedBase i) := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  rfl

@[expose] noncomputable def projectPlane (T : Cell → Fin 11487) : Tiling (Fin 156) :=
  fun p => indexedBase (T p)

@[expose] def FullValid (T : Cell → Fin 11487) : Prop :=
  ∀ s : EdgeSite, edgeCompatible indexedWangTile s (T s.1) (T (edgeNeighbor s))

theorem exact_base_valid (T : Cell → Fin 11487) (h : FullValid T) :
    wangValid Wang156.presentation (projectPlane T) := by
  intro p
  have hb0 := indexedBase_spec (T p)
  constructor
  · have hb1 := indexedBase_spec (T (p.1+1,p.2))
    have hh := h (p,true)
    simp only [edgeCompatible, edgeNeighbor, indexedWangTile] at hh
    change (indexedFullTile (T p)).e = (indexedFullTile (T (p.1+1,p.2))).w at hh
    have hp := congrArg (fun c : FullColor => c.1) hh
    have he := congrArg Quad.e hb0
    have hw := congrArg Quad.w hb1
    change (indexedFullTile (T p)).e.1 = (Wang156.tile (indexedBase (T p)).val).e at he
    change (indexedFullTile (T (p.1+1,p.2))).w.1 =
      (Wang156.tile (indexedBase (T (p.1+1,p.2))).val).w at hw
    exact he.symm.trans (hp.trans hw)
  · have hb1 := indexedBase_spec (T (p.1,p.2+1))
    have hh := h (p,false)
    simp only [edgeCompatible, edgeNeighbor, indexedWangTile] at hh
    change (indexedFullTile (T p)).n = (indexedFullTile (T (p.1,p.2+1))).s at hh
    have hp := congrArg (fun c : FullColor => c.1) hh
    have hn := congrArg Quad.n hb0
    have hs := congrArg Quad.s hb1
    change (indexedFullTile (T p)).n.1 = (Wang156.tile (indexedBase (T p)).val).n at hn
    change (indexedFullTile (T (p.1,p.2+1))).s.1 =
      (Wang156.tile (indexedBase (T (p.1,p.2+1))).val).s at hs
    exact hn.symm.trans (hp.trans hs)

theorem exact_plane_projects (h : ExactPlane) :
    ∃ T : Tiling (Fin 156), wangValid Wang156.presentation T := by
  rw [ExactPlane,TilesPlane] at h
  obtain ⟨T,hT⟩ := h
  exact ⟨projectPlane T,exact_base_valid T hT⟩

theorem exact_full_tiling_supertile (T : Cell → Fin 11487) (h : FullValid T) (n : Nat) :
    ∃ k b, HasSupertile Wang156.exactSystem (projectPlane T) n k b :=
  Wang156.exact_arbitrary_supertile (projectPlane T) (exact_base_valid T h) n

/-- Coordinates belong to the original decorated plane, not a replacement tiling. -/
theorem exact_full_tiling_supertile_lift (T : Cell → Fin 11487) (h : FullValid T) (n : Nat) :
    ∃ (k : Fin 156) (b : Point), ∀ bits,
      eraseDecoration (indexedFullTile
        (T (b.1 + (binaryOffset n bits).1, b.2 + (binaryOffset n bits).2))) =
      baseQuad (supertile Wang156.exactSystem n k bits) := by
  obtain ⟨k,b,hb⟩ := exact_full_tiling_supertile T h n
  refine ⟨k,b,fun bits => ?_⟩
  rw [indexedBase_spec]
  exact congrArg baseQuad (hb bits)

#print axioms indexedBase_spec
#print axioms exact_base_valid
#print axioms exact_full_tiling_supertile_lift
end K230Verification
