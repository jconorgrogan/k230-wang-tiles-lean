module
public import ActualChannels
public section
namespace K230Verification

theorem decode_inner_left {c : Nat} (h : c=1 ∨ c=2) : EndAllows .innerLeft (decodeChannel c) := by
  rcases h with rfl|rfl <;> simp [EndAllows,decodeChannel]

theorem decode_inner_right {c : Nat} (h : c=1 ∨ c=3) : EndAllows .innerRight (decodeChannel c) := by
  rcases h with rfl|rfl <;> simp [EndAllows,decodeChannel]

theorem decode_outer_left {c : Nat} (h : c=2 ∨ c=3) : EndAllows .outerLeft (decodeChannel c) := by
  rcases h with rfl|rfl <;> simp [EndAllows,decodeChannel]

theorem decode_outer_right {c : Nat} (h : c=3) : EndAllows .outerRight (decodeChannel c) := by
  subst c
  simp [EndAllows,decodeChannel]

theorem indexed_left_inner (i : Fin 11487)
    (hb : (indexedGroup i).1=100 ∨ (indexedGroup i).1=116) :
    EndAllows .innerLeft (decodeChannel (indexedFullTile i).e.2.1) := by
  have he := congrArg Quad.e (indexed_channels i)
  change (indexedFullTile i).e.2.1=(groupChannel (indexedGroup i)).e at he
  rw [he]
  apply decode_inner_left
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h
  · exact ((concrete_channel_sides _ hg).1 (Or.inl h)).1
  · exact ((concrete_channel_sides _ hg).1 (Or.inr h)).1

theorem indexed_right_inner (i : Fin 11487)
    (hb : (indexedGroup i).1=95 ∨ (indexedGroup i).1=111) :
    EndAllows .innerRight (decodeChannel (indexedFullTile i).w.2.1) := by
  have he := congrArg Quad.w (indexed_channels i)
  change (indexedFullTile i).w.2.1=(groupChannel (indexedGroup i)).w at he
  rw [he]
  apply decode_inner_right
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h
  · exact ((concrete_channel_sides _ hg).2.1 (Or.inl h)).1
  · exact ((concrete_channel_sides _ hg).2.1 (Or.inr h)).1

theorem indexed_bottom_inner (i : Fin 11487)
    (hb : (indexedGroup i).1=136 ∨ (indexedGroup i).1=142) :
    EndAllows .innerLeft (decodeChannel (indexedFullTile i).n.2.1) := by
  have he := congrArg Quad.n (indexed_channels i)
  change (indexedFullTile i).n.2.1=(groupChannel (indexedGroup i)).n at he
  rw [he]
  apply decode_inner_left
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h
  · exact ((concrete_channel_sides _ hg).2.2.1 (Or.inl h)).1
  · exact ((concrete_channel_sides _ hg).2.2.1 (Or.inr h)).1

theorem indexed_top_inner (i : Fin 11487)
    (hb : (indexedGroup i).1=134 ∨ (indexedGroup i).1=140) :
    EndAllows .innerRight (decodeChannel (indexedFullTile i).s.2.1) := by
  have he := congrArg Quad.s (indexed_channels i)
  change (indexedFullTile i).s.2.1=(groupChannel (indexedGroup i)).s at he
  rw [he]
  apply decode_inner_right
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h
  · exact ((concrete_channel_sides _ hg).2.2.2 (Or.inl h)).1
  · exact ((concrete_channel_sides _ hg).2.2.2 (Or.inr h)).1

theorem indexed_left_outer (i : Fin 11487)
    (hb : (indexedGroup i).1=100 ∨ (indexedGroup i).1=116 ∨ (indexedGroup i).1=101) :
    EndAllows .outerLeft (decodeChannel (indexedFullTile i).w.2.1) := by
  have he := congrArg Quad.w (indexed_channels i)
  change (indexedFullTile i).w.2.1=(groupChannel (indexedGroup i)).w at he
  rw [he]
  apply decode_outer_left
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h|h
  · exact ((concrete_channel_sides _ hg).1 (Or.inl h)).2
  · exact ((concrete_channel_sides _ hg).1 (Or.inr h)).2
  · exact ((concrete_level_two_sides _ hg).1 h).2

theorem indexed_right_outer (i : Fin 11487)
    (hb : (indexedGroup i).1=95 ∨ (indexedGroup i).1=111 ∨ (indexedGroup i).1=96) :
    EndAllows .outerRight (decodeChannel (indexedFullTile i).e.2.1) := by
  have he := congrArg Quad.e (indexed_channels i)
  change (indexedFullTile i).e.2.1=(groupChannel (indexedGroup i)).e at he
  rw [he]
  apply decode_outer_right
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h|h
  · exact ((concrete_channel_sides _ hg).2.1 (Or.inl h)).2
  · exact ((concrete_channel_sides _ hg).2.1 (Or.inr h)).2
  · exact ((concrete_level_two_sides _ hg).2.1 h).2

theorem indexed_bottom_outer (i : Fin 11487)
    (hb : (indexedGroup i).1=136 ∨ (indexedGroup i).1=142 ∨ (indexedGroup i).1=151) :
    EndAllows .outerLeft (decodeChannel (indexedFullTile i).s.2.1) := by
  have he := congrArg Quad.s (indexed_channels i)
  change (indexedFullTile i).s.2.1=(groupChannel (indexedGroup i)).s at he
  rw [he]
  apply decode_outer_left
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h|h
  · exact ((concrete_channel_sides _ hg).2.2.1 (Or.inl h)).2
  · exact ((concrete_channel_sides _ hg).2.2.1 (Or.inr h)).2
  · exact ((concrete_level_two_sides _ hg).2.2.1 h).2

theorem indexed_top_outer (i : Fin 11487)
    (hb : (indexedGroup i).1=134 ∨ (indexedGroup i).1=140 ∨ (indexedGroup i).1=150) :
    EndAllows .outerRight (decodeChannel (indexedFullTile i).n.2.1) := by
  have he := congrArg Quad.n (indexed_channels i)
  change (indexedFullTile i).n.2.1=(groupChannel (indexedGroup i)).n at he
  rw [he]
  apply decode_outer_right
  have hg := (indexedGroup_spec i).1
  rcases hb with h|h|h
  · exact ((concrete_channel_sides _ hg).2.2.2 (Or.inl h)).2
  · exact ((concrete_channel_sides _ hg).2.2.2 (Or.inr h)).2
  · exact ((concrete_level_two_sides _ hg).2.2.2 h).2

#print axioms indexed_left_outer
#print axioms indexed_top_outer
end K230Verification
