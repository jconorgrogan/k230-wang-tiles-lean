module
public import FullBoardIndexing
public import ConcreteRoles
public import ChannelTrace
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Verification

@[expose] def decodeChannel (c : Nat) : Channel :=
  if c=1 then .zero else if c=2 then .a else .b
@[expose] def channelCode : Channel → Nat
  | .zero => 1 | .a => 2 | .b => 3

theorem decodeChannel_code (c : Channel) : decodeChannel (channelCode c)=c := by
  cases c <;> rfl

theorem channelCode_decode (c : Nat) (hc : 0<c ∧ c<4) : channelCode (decodeChannel c)=c := by
  have hh : c=1 ∨ c=2 ∨ c=3 := by omega
  rcases hh with rfl|rfl|rfl <;> rfl

theorem decode_zero_iff (c : Nat) : decodeChannel c=.zero ↔ c=1 := by
  by_cases h1 : c=1 <;> by_cases h2 : c=2 <;> simp [decodeChannel,h1,h2]

theorem decode_a_iff (c : Nat) : decodeChannel c=.a ↔ c=2 := by
  unfold decodeChannel
  split <;> simp_all

theorem decode_b_iff (c : Nat) (hc : 0<c ∧ c<4) : decodeChannel c=.b ↔ c=3 := by
  have hh : c=1 ∨ c=2 ∨ c=3 := by omega
  rcases hh with rfl|rfl|rfl <;> decide

theorem indexed_channels (i : Fin 11487) :
    fullChannels (indexedFullTile i)=groupChannel (indexedGroup i) := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  rfl

theorem indexed_channel_bounds (i : Fin 11487) :
    (indexedFullTile i).n.2.1<4 ∧ (indexedFullTile i).e.2.1<4 ∧
    (indexedFullTile i).s.2.1<4 ∧ (indexedFullTile i).w.2.1<4 := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  exact ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩

@[expose] noncomputable def hCode (T : Cell → Fin 11487) (p : Cell) : Nat :=
  (indexedFullTile (T p)).e.2.1
@[expose] noncomputable def vCode (T : Cell → Fin 11487) (p : Cell) : Nat :=
  (indexedFullTile (T p)).n.2.1
@[expose] noncomputable def hChannel (T : Cell → Fin 11487) (p : Cell) : Channel := decodeChannel (hCode T p)
@[expose] noncomputable def vChannel (T : Cell → Fin 11487) (p : Cell) : Channel := decodeChannel (vCode T p)

theorem actual_horizontal_match (T : Cell → Fin 11487) (h : FullValid T) (p : Cell) :
    (indexedFullTile (T p)).e.2.1=(indexedFullTile (T (p.1+1,p.2))).w.2.1 := by
  have hh := h (p,true)
  change (indexedFullTile (T p)).e=(indexedFullTile (T (p.1+1,p.2))).w at hh
  exact congrArg (fun c : FullColor => c.2.1) hh

theorem actual_vertical_match (T : Cell → Fin 11487) (h : FullValid T) (p : Cell) :
    (indexedFullTile (T p)).n.2.1=(indexedFullTile (T (p.1,p.2+1))).s.2.1 := by
  have hh := h (p,false)
  change (indexedFullTile (T p)).n=(indexedFullTile (T (p.1,p.2+1))).s at hh
  exact congrArg (fun c : FullColor => c.2.1) hh

theorem indexed_hcopy (i : Fin 11487) (hn : ¬hBoundary (indexedGroup i).1) :
    (indexedFullTile i).e.2.1=(indexedFullTile i).w.2.1 := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  exact (concrete_channel_copy _ (indexedGroup_spec i).1).1 hn

theorem indexed_vcopy (i : Fin 11487) (hn : ¬vBoundary (indexedGroup i).1) :
    (indexedFullTile i).n.2.1=(indexedFullTile i).s.2.1 := by
  obtain ⟨t,_,ht⟩ := (indexedGroup_spec i).2
  rw [ht]
  exact (concrete_channel_copy _ (indexedGroup_spec i).1).2 hn

theorem actual_hcopy (T : Cell → Fin 11487) (h : FullValid T) (p : Cell)
    (hn : ¬hBoundary (indexedGroup (T p)).1) :
    hChannel T p=hChannel T (p.1-1,p.2) := by
  have hm := actual_horizontal_match T h (p.1-1,p.2)
  have he : (p.1-1+1,p.2)=p := by apply Prod.ext <;> dsimp <;> omega
  simp only [he] at hm
  exact congrArg decodeChannel ((indexed_hcopy (T p) hn).trans hm.symm)

theorem actual_vcopy (T : Cell → Fin 11487) (h : FullValid T) (p : Cell)
    (hn : ¬vBoundary (indexedGroup (T p)).1) :
    vChannel T p=vChannel T (p.1,p.2-1) := by
  have hm := actual_vertical_match T h (p.1,p.2-1)
  have he : (p.1,p.2-1+1)=p := by apply Prod.ext <;> dsimp <;> omega
  simp only [he] at hm
  exact congrArg decodeChannel ((indexed_vcopy (T p) hn).trans hm.symm)

#print axioms actual_hcopy
#print axioms actual_vcopy
end K230Verification
