module
public import ChannelClasses
public import ConcreteRoles
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 10000
namespace K230Verification
/-- Complete local obstruction-channel specification, including the inert
    level-2 exception. Digits0/1/2/3 mean absent/zero/a/b. -/
@[expose] def ChannelLegal (b : Nat) (c : Quad Nat) : Prop :=
  b<156 ∧ c.n<4 ∧ c.e<4 ∧ c.s<4 ∧ c.w<4 ∧
  (c.n≠0 ↔ HasVChannel b) ∧ (c.s≠0 ↔ HasVChannel b) ∧
  (c.e≠0 ↔ HasHChannel b) ∧ (c.w≠0 ↔ HasHChannel b) ∧
  (¬hBoundary b → c.e=c.w) ∧ (¬vBoundary b → c.n=c.s) ∧
  ((b=100 ∨ b=116) → (c.e=1 ∨ c.e=2) ∧ (c.w=2 ∨ c.w=3)) ∧
  ((b=95 ∨ b=111) → (c.w=1 ∨ c.w=3) ∧ c.e=3) ∧
  ((b=136 ∨ b=142) → (c.n=1 ∨ c.n=2) ∧ (c.s=2 ∨ c.s=3)) ∧
  ((b=134 ∨ b=140) → (c.s=1 ∨ c.s=3) ∧ c.n=3) ∧
  (b=101 → c.e=2 ∧ (c.w=2 ∨ c.w=3)) ∧
  (b=96 → c.w=2 ∧ c.e=3) ∧
  (b=151 → c.n=2 ∧ (c.s=2 ∨ c.s=3)) ∧
  (b=150 → c.s=2 ∧ c.n=3)
@[expose] instance channelLegalDecidable (b : Nat) (c : Quad Nat) : Decidable (ChannelLegal b c) := by
  unfold ChannelLegal HasVChannel HasHChannel hBoundary vBoundary
  infer_instance
@[expose] def packChannels (c : Quad Nat) : Nat := 64*c.n+16*c.e+4*c.s+c.w
@[expose] def LegalGroupClaim (b : Nat) : Prop := ∀ p : Fin 256,
  ChannelLegal b (groupChannel (b,p.val,0)) → ∃ f : Fin 14, (b,p.val,f.val) ∈ exactGroups.toList
@[expose] instance legalGroupClaimDecidable (b : Nat) : Decidable (LegalGroupClaim b) := by
  unfold LegalGroupClaim
  infer_instance
theorem legal_group_0 : LegalGroupClaim 0 := by decide
theorem legal_group_1 : LegalGroupClaim 1 := by decide
theorem legal_group_2 : LegalGroupClaim 2 := by decide
theorem legal_group_3 : LegalGroupClaim 3 := by decide
theorem legal_group_4 : LegalGroupClaim 4 := by decide
theorem legal_group_5 : LegalGroupClaim 5 := by decide
theorem legal_group_6 : LegalGroupClaim 6 := by decide
theorem legal_group_7 : LegalGroupClaim 7 := by decide
theorem legal_group_8 : LegalGroupClaim 8 := by decide
theorem legal_group_9 : LegalGroupClaim 9 := by decide
theorem legal_group_10 : LegalGroupClaim 10 := by decide
theorem legal_group_11 : LegalGroupClaim 11 := by decide
theorem legal_group_12 : LegalGroupClaim 12 := by decide
theorem legal_group_13 : LegalGroupClaim 13 := by decide
theorem legal_group_14 : LegalGroupClaim 14 := by decide
theorem legal_group_15 : LegalGroupClaim 15 := by decide
theorem legal_group_16 : LegalGroupClaim 16 := by decide
theorem legal_group_17 : LegalGroupClaim 17 := by decide
theorem legal_group_18 : LegalGroupClaim 18 := by decide
theorem legal_group_19 : LegalGroupClaim 19 := by decide
theorem legal_group_20 : LegalGroupClaim 20 := by decide
theorem legal_group_21 : LegalGroupClaim 21 := by decide
theorem legal_group_22 : LegalGroupClaim 22 := by decide
theorem legal_group_23 : LegalGroupClaim 23 := by decide
theorem legal_group_24 : LegalGroupClaim 24 := by decide
theorem legal_group_25 : LegalGroupClaim 25 := by decide
theorem legal_group_26 : LegalGroupClaim 26 := by decide
theorem legal_group_27 : LegalGroupClaim 27 := by decide
theorem legal_group_28 : LegalGroupClaim 28 := by decide
theorem legal_group_29 : LegalGroupClaim 29 := by decide
theorem legal_group_30 : LegalGroupClaim 30 := by decide
theorem legal_group_31 : LegalGroupClaim 31 := by decide
theorem legal_group_32 : LegalGroupClaim 32 := by decide
theorem legal_group_33 : LegalGroupClaim 33 := by decide
theorem legal_group_34 : LegalGroupClaim 34 := by decide
theorem legal_group_35 : LegalGroupClaim 35 := by decide
theorem legal_group_36 : LegalGroupClaim 36 := by decide
theorem legal_group_37 : LegalGroupClaim 37 := by decide
theorem legal_group_38 : LegalGroupClaim 38 := by decide
theorem legal_group_39 : LegalGroupClaim 39 := by decide
theorem legal_group_40 : LegalGroupClaim 40 := by decide
theorem legal_group_41 : LegalGroupClaim 41 := by decide
theorem legal_group_42 : LegalGroupClaim 42 := by decide
theorem legal_group_43 : LegalGroupClaim 43 := by decide
theorem legal_group_44 : LegalGroupClaim 44 := by decide
theorem legal_group_45 : LegalGroupClaim 45 := by decide
theorem legal_group_46 : LegalGroupClaim 46 := by decide
theorem legal_group_47 : LegalGroupClaim 47 := by decide
theorem legal_group_48 : LegalGroupClaim 48 := by decide
theorem legal_group_49 : LegalGroupClaim 49 := by decide
theorem legal_group_50 : LegalGroupClaim 50 := by decide
theorem legal_group_51 : LegalGroupClaim 51 := by decide
theorem legal_group_52 : LegalGroupClaim 52 := by decide
theorem legal_group_53 : LegalGroupClaim 53 := by decide
theorem legal_group_54 : LegalGroupClaim 54 := by decide
theorem legal_group_55 : LegalGroupClaim 55 := by decide
theorem legal_group_56 : LegalGroupClaim 56 := by decide
theorem legal_group_57 : LegalGroupClaim 57 := by decide
theorem legal_group_58 : LegalGroupClaim 58 := by decide
theorem legal_group_59 : LegalGroupClaim 59 := by decide
theorem legal_group_60 : LegalGroupClaim 60 := by decide
theorem legal_group_61 : LegalGroupClaim 61 := by decide
theorem legal_group_62 : LegalGroupClaim 62 := by decide
theorem legal_group_63 : LegalGroupClaim 63 := by decide
theorem legal_group_64 : LegalGroupClaim 64 := by decide
theorem legal_group_65 : LegalGroupClaim 65 := by decide
theorem legal_group_66 : LegalGroupClaim 66 := by decide
theorem legal_group_67 : LegalGroupClaim 67 := by decide
theorem legal_group_68 : LegalGroupClaim 68 := by decide
theorem legal_group_69 : LegalGroupClaim 69 := by decide
theorem legal_group_70 : LegalGroupClaim 70 := by decide
theorem legal_group_71 : LegalGroupClaim 71 := by decide
theorem legal_group_72 : LegalGroupClaim 72 := by decide
theorem legal_group_73 : LegalGroupClaim 73 := by decide
theorem legal_group_74 : LegalGroupClaim 74 := by decide
theorem legal_group_75 : LegalGroupClaim 75 := by decide
theorem legal_group_76 : LegalGroupClaim 76 := by decide
theorem legal_group_77 : LegalGroupClaim 77 := by decide
theorem legal_group_78 : LegalGroupClaim 78 := by decide
theorem legal_group_79 : LegalGroupClaim 79 := by decide
theorem legal_group_80 : LegalGroupClaim 80 := by decide
theorem legal_group_81 : LegalGroupClaim 81 := by decide
theorem legal_group_82 : LegalGroupClaim 82 := by decide
theorem legal_group_83 : LegalGroupClaim 83 := by decide
theorem legal_group_84 : LegalGroupClaim 84 := by decide
theorem legal_group_85 : LegalGroupClaim 85 := by decide
theorem legal_group_86 : LegalGroupClaim 86 := by decide
theorem legal_group_87 : LegalGroupClaim 87 := by decide
theorem legal_group_88 : LegalGroupClaim 88 := by decide
theorem legal_group_89 : LegalGroupClaim 89 := by decide
theorem legal_group_90 : LegalGroupClaim 90 := by decide
theorem legal_group_91 : LegalGroupClaim 91 := by decide
theorem legal_group_92 : LegalGroupClaim 92 := by decide
theorem legal_group_93 : LegalGroupClaim 93 := by decide
theorem legal_group_94 : LegalGroupClaim 94 := by decide
theorem legal_group_95 : LegalGroupClaim 95 := by decide
theorem legal_group_96 : LegalGroupClaim 96 := by decide
theorem legal_group_97 : LegalGroupClaim 97 := by decide
theorem legal_group_98 : LegalGroupClaim 98 := by decide
theorem legal_group_99 : LegalGroupClaim 99 := by decide
theorem legal_group_100 : LegalGroupClaim 100 := by decide
theorem legal_group_101 : LegalGroupClaim 101 := by decide
theorem legal_group_102 : LegalGroupClaim 102 := by decide
theorem legal_group_103 : LegalGroupClaim 103 := by decide
theorem legal_group_104 : LegalGroupClaim 104 := by decide
theorem legal_group_105 : LegalGroupClaim 105 := by decide
theorem legal_group_106 : LegalGroupClaim 106 := by decide
theorem legal_group_107 : LegalGroupClaim 107 := by decide
theorem legal_group_108 : LegalGroupClaim 108 := by decide
theorem legal_group_109 : LegalGroupClaim 109 := by decide
theorem legal_group_110 : LegalGroupClaim 110 := by decide
theorem legal_group_111 : LegalGroupClaim 111 := by decide
theorem legal_group_112 : LegalGroupClaim 112 := by decide
theorem legal_group_113 : LegalGroupClaim 113 := by decide
theorem legal_group_114 : LegalGroupClaim 114 := by decide
theorem legal_group_115 : LegalGroupClaim 115 := by decide
theorem legal_group_116 : LegalGroupClaim 116 := by decide
theorem legal_group_117 : LegalGroupClaim 117 := by decide
theorem legal_group_118 : LegalGroupClaim 118 := by decide
theorem legal_group_119 : LegalGroupClaim 119 := by decide
theorem legal_group_120 : LegalGroupClaim 120 := by decide
theorem legal_group_121 : LegalGroupClaim 121 := by decide
theorem legal_group_122 : LegalGroupClaim 122 := by decide
theorem legal_group_123 : LegalGroupClaim 123 := by decide
theorem legal_group_124 : LegalGroupClaim 124 := by decide
theorem legal_group_125 : LegalGroupClaim 125 := by decide
theorem legal_group_126 : LegalGroupClaim 126 := by decide
theorem legal_group_127 : LegalGroupClaim 127 := by decide
theorem legal_group_128 : LegalGroupClaim 128 := by decide
theorem legal_group_129 : LegalGroupClaim 129 := by decide
theorem legal_group_130 : LegalGroupClaim 130 := by decide
theorem legal_group_131 : LegalGroupClaim 131 := by decide
theorem legal_group_132 : LegalGroupClaim 132 := by decide
theorem legal_group_133 : LegalGroupClaim 133 := by decide
theorem legal_group_134 : LegalGroupClaim 134 := by decide
theorem legal_group_135 : LegalGroupClaim 135 := by decide
theorem legal_group_136 : LegalGroupClaim 136 := by decide
theorem legal_group_137 : LegalGroupClaim 137 := by decide
theorem legal_group_138 : LegalGroupClaim 138 := by decide
theorem legal_group_139 : LegalGroupClaim 139 := by decide
theorem legal_group_140 : LegalGroupClaim 140 := by decide
theorem legal_group_141 : LegalGroupClaim 141 := by decide
theorem legal_group_142 : LegalGroupClaim 142 := by decide
theorem legal_group_143 : LegalGroupClaim 143 := by decide
theorem legal_group_144 : LegalGroupClaim 144 := by decide
theorem legal_group_145 : LegalGroupClaim 145 := by decide
theorem legal_group_146 : LegalGroupClaim 146 := by decide
theorem legal_group_147 : LegalGroupClaim 147 := by decide
theorem legal_group_148 : LegalGroupClaim 148 := by decide
theorem legal_group_149 : LegalGroupClaim 149 := by decide
theorem legal_group_150 : LegalGroupClaim 150 := by decide
theorem legal_group_151 : LegalGroupClaim 151 := by decide
theorem legal_group_152 : LegalGroupClaim 152 := by decide
theorem legal_group_153 : LegalGroupClaim 153 := by decide
theorem legal_group_154 : LegalGroupClaim 154 := by decide
theorem legal_group_155 : LegalGroupClaim 155 := by decide
theorem legal_group_claim (b : Nat) (hb : b<156) : LegalGroupClaim b := by
  match b with
  | 0 => exact legal_group_0
  | 1 => exact legal_group_1
  | 2 => exact legal_group_2
  | 3 => exact legal_group_3
  | 4 => exact legal_group_4
  | 5 => exact legal_group_5
  | 6 => exact legal_group_6
  | 7 => exact legal_group_7
  | 8 => exact legal_group_8
  | 9 => exact legal_group_9
  | 10 => exact legal_group_10
  | 11 => exact legal_group_11
  | 12 => exact legal_group_12
  | 13 => exact legal_group_13
  | 14 => exact legal_group_14
  | 15 => exact legal_group_15
  | 16 => exact legal_group_16
  | 17 => exact legal_group_17
  | 18 => exact legal_group_18
  | 19 => exact legal_group_19
  | 20 => exact legal_group_20
  | 21 => exact legal_group_21
  | 22 => exact legal_group_22
  | 23 => exact legal_group_23
  | 24 => exact legal_group_24
  | 25 => exact legal_group_25
  | 26 => exact legal_group_26
  | 27 => exact legal_group_27
  | 28 => exact legal_group_28
  | 29 => exact legal_group_29
  | 30 => exact legal_group_30
  | 31 => exact legal_group_31
  | 32 => exact legal_group_32
  | 33 => exact legal_group_33
  | 34 => exact legal_group_34
  | 35 => exact legal_group_35
  | 36 => exact legal_group_36
  | 37 => exact legal_group_37
  | 38 => exact legal_group_38
  | 39 => exact legal_group_39
  | 40 => exact legal_group_40
  | 41 => exact legal_group_41
  | 42 => exact legal_group_42
  | 43 => exact legal_group_43
  | 44 => exact legal_group_44
  | 45 => exact legal_group_45
  | 46 => exact legal_group_46
  | 47 => exact legal_group_47
  | 48 => exact legal_group_48
  | 49 => exact legal_group_49
  | 50 => exact legal_group_50
  | 51 => exact legal_group_51
  | 52 => exact legal_group_52
  | 53 => exact legal_group_53
  | 54 => exact legal_group_54
  | 55 => exact legal_group_55
  | 56 => exact legal_group_56
  | 57 => exact legal_group_57
  | 58 => exact legal_group_58
  | 59 => exact legal_group_59
  | 60 => exact legal_group_60
  | 61 => exact legal_group_61
  | 62 => exact legal_group_62
  | 63 => exact legal_group_63
  | 64 => exact legal_group_64
  | 65 => exact legal_group_65
  | 66 => exact legal_group_66
  | 67 => exact legal_group_67
  | 68 => exact legal_group_68
  | 69 => exact legal_group_69
  | 70 => exact legal_group_70
  | 71 => exact legal_group_71
  | 72 => exact legal_group_72
  | 73 => exact legal_group_73
  | 74 => exact legal_group_74
  | 75 => exact legal_group_75
  | 76 => exact legal_group_76
  | 77 => exact legal_group_77
  | 78 => exact legal_group_78
  | 79 => exact legal_group_79
  | 80 => exact legal_group_80
  | 81 => exact legal_group_81
  | 82 => exact legal_group_82
  | 83 => exact legal_group_83
  | 84 => exact legal_group_84
  | 85 => exact legal_group_85
  | 86 => exact legal_group_86
  | 87 => exact legal_group_87
  | 88 => exact legal_group_88
  | 89 => exact legal_group_89
  | 90 => exact legal_group_90
  | 91 => exact legal_group_91
  | 92 => exact legal_group_92
  | 93 => exact legal_group_93
  | 94 => exact legal_group_94
  | 95 => exact legal_group_95
  | 96 => exact legal_group_96
  | 97 => exact legal_group_97
  | 98 => exact legal_group_98
  | 99 => exact legal_group_99
  | 100 => exact legal_group_100
  | 101 => exact legal_group_101
  | 102 => exact legal_group_102
  | 103 => exact legal_group_103
  | 104 => exact legal_group_104
  | 105 => exact legal_group_105
  | 106 => exact legal_group_106
  | 107 => exact legal_group_107
  | 108 => exact legal_group_108
  | 109 => exact legal_group_109
  | 110 => exact legal_group_110
  | 111 => exact legal_group_111
  | 112 => exact legal_group_112
  | 113 => exact legal_group_113
  | 114 => exact legal_group_114
  | 115 => exact legal_group_115
  | 116 => exact legal_group_116
  | 117 => exact legal_group_117
  | 118 => exact legal_group_118
  | 119 => exact legal_group_119
  | 120 => exact legal_group_120
  | 121 => exact legal_group_121
  | 122 => exact legal_group_122
  | 123 => exact legal_group_123
  | 124 => exact legal_group_124
  | 125 => exact legal_group_125
  | 126 => exact legal_group_126
  | 127 => exact legal_group_127
  | 128 => exact legal_group_128
  | 129 => exact legal_group_129
  | 130 => exact legal_group_130
  | 131 => exact legal_group_131
  | 132 => exact legal_group_132
  | 133 => exact legal_group_133
  | 134 => exact legal_group_134
  | 135 => exact legal_group_135
  | 136 => exact legal_group_136
  | 137 => exact legal_group_137
  | 138 => exact legal_group_138
  | 139 => exact legal_group_139
  | 140 => exact legal_group_140
  | 141 => exact legal_group_141
  | 142 => exact legal_group_142
  | 143 => exact legal_group_143
  | 144 => exact legal_group_144
  | 145 => exact legal_group_145
  | 146 => exact legal_group_146
  | 147 => exact legal_group_147
  | 148 => exact legal_group_148
  | 149 => exact legal_group_149
  | 150 => exact legal_group_150
  | 151 => exact legal_group_151
  | 152 => exact legal_group_152
  | 153 => exact legal_group_153
  | 154 => exact legal_group_154
  | 155 => exact legal_group_155
  | n+156 => omega

theorem unpack_pack_channels (b f : Nat) (c : Quad Nat)
    (hn : c.n<4) (he : c.e<4) (hs : c.s<4) (hw : c.w<4) :
    groupChannel (b,packChannels c,f)=c := by
  cases c with
  | mk n e s w =>
    simp only [Quad.mk.injEq,groupChannel,packChannels]
    simp only at hn he hs hw
    omega

theorem legal_channels_have_group {b : Nat} {c : Quad Nat} (h : ChannelLegal b c) :
    ∃ g ∈ exactGroups.toList, g.1=b ∧ groupChannel g=c := by
  have hb := h.1
  have hn := h.2.1
  have he := h.2.2.1
  have hs := h.2.2.2.1
  have hw := h.2.2.2.2.1
  have hp : packChannels c < 256 := by unfold packChannels; omega
  have hu := unpack_pack_channels b 0 c hn he hs hw
  obtain ⟨f,hf⟩ := legal_group_claim b hb ⟨packChannels c,hp⟩ (hu.symm ▸ h)
  exact ⟨(b,packChannels c,f.val),hf,rfl,unpack_pack_channels b f.val c hn he hs hw⟩
#print axioms legal_channels_have_group
end K230Verification
