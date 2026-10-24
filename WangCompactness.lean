module
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Discrete

public section
namespace K230Verification

/-- Compactness for finite-alphabet binary local constraints, including Wang
    edge matching. Finite satisfiability, not a finite collection of samples,
    is the hypothesis. -/
theorem binary_constraint_compactness {P I T : Type*} [Finite T]
    [TopologicalSpace T] [DiscreteTopology T]
    (first second : I → P) (relation : I → Set (T × T))
    (finite_sat : ∀ s : Finset I, ∃ f : P → T,
      ∀ i ∈ s, (f (first i), f (second i)) ∈ relation i) :
    ∃ f : P → T, ∀ i, (f (first i), f (second i)) ∈ relation i := by
  classical
  let C : I → Set (P → T) := fun i => {f | (f (first i), f (second i)) ∈ relation i}
  have closed : ∀ i, IsClosed (C i) := by
    intro i
    exact (isClosed_discrete (relation i)).preimage
      ((continuous_apply (first i)).prodMk (continuous_apply (second i)))
  have compact : IsCompact (Set.univ : Set (P → T)) := isCompact_univ
  have finite_nonempty : ∀ s : Finset I, (Set.univ ∩ ⋂ i ∈ s, C i).Nonempty := by
    intro s
    obtain ⟨f,hf⟩ := finite_sat s
    refine ⟨f,Set.mem_univ _,?_⟩
    simpa only [Set.mem_iInter, C, Set.mem_ofPred_eq] using hf
  obtain ⟨f,_,hf⟩ := compact.inter_iInter_nonempty C closed finite_nonempty
  exact ⟨f,by simpa only [Set.mem_iInter, C, Set.mem_ofPred_eq] using hf⟩

structure WangTile (C : Type*) where
  north : C
  east : C
  south : C
  west : C

abbrev Cell := Int × Int
abbrev EdgeSite := Cell × Bool

def edgeNeighbor (s : EdgeSite) : Cell :=
  if s.2 then (s.1.1+1,s.1.2) else (s.1.1,s.1.2+1)

def edgeCompatible {C : Type*} {N : Nat} (tiles : Fin N → WangTile C)
    (s : EdgeSite) (a b : Fin N) : Prop :=
  if s.2 then (tiles a).east = (tiles b).west
  else (tiles a).north = (tiles b).south

def edgeRadius (s : EdgeSite) : Nat := max s.1.1.natAbs s.1.2.natAbs

/-- Unseeded, boundary-free Wang tiling of every integer cell. -/
def TilesPlane {C : Type*} {N : Nat} (tiles : Fin N → WangTile C) : Prop :=
  ∃ f : Cell → Fin N, ∀ s : EdgeSite,
    edgeCompatible tiles s (f s.1) (f (edgeNeighbor s))

/-- Arbitrarily large finite windows tile. Assignments outside the window
    are arbitrary and unconstrained; the quantified constraints are finite. -/
def TilesEveryWindow {C : Type*} {N : Nat} (tiles : Fin N → WangTile C) : Prop :=
  ∀ n : Nat, ∃ f : Cell → Fin N, ∀ s : EdgeSite, edgeRadius s ≤ n →
    edgeCompatible tiles s (f s.1) (f (edgeNeighbor s))

theorem tilesPlane_iff_everyWindow {C : Type*} {N : Nat} (tiles : Fin N → WangTile C) :
    TilesPlane tiles ↔ TilesEveryWindow tiles := by
  classical
  constructor
  · rintro ⟨f,hf⟩ n
    exact ⟨f,fun s _ => hf s⟩
  · intro h
    let : TopologicalSpace (Fin N) := ⊥
    apply binary_constraint_compactness (T:=Fin N) (fun s : EdgeSite => s.1)
      edgeNeighbor (fun s => {ab | edgeCompatible tiles s ab.1 ab.2})
    intro u
    obtain ⟨f,hf⟩ := h (u.sup edgeRadius)
    refine ⟨f,?_⟩
    intro s hs
    exact hf s (Finset.le_sup hs)

#print axioms tilesPlane_iff_everyWindow
#print axioms binary_constraint_compactness
end K230Verification
