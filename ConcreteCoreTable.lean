module
public import ConcreteExpansion
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete

@[expose] def indexTile (k : Nat) : Fin 156 := ⟨k%156, by omega⟩
@[expose] def boardVariant (k : Fin 156) : Nat :=
  (Wang156.tile k.val).px + 2*(Wang156.tile k.val).py
@[expose] def coreRepresentative (v : Nat) : Fin 156 :=
  if v=0 then ⟨0, by decide⟩ else if v=1 then ⟨120, by decide⟩
  else if v=2 then ⟨88, by decide⟩ else ⟨152, by decide⟩
@[expose] def boardCore (v x y : Nat) : Fin 156 :=
  expanded 3 (coreRepresentative v) (x+2) (y+2)

@[expose] def coreAt (k : Nat) : Bool := (List.range 5).all fun x => (List.range 5).all fun y =>
  (expanded 3 (indexTile k) (x+2) (y+2)).val == (boardCore (boardVariant (indexTile k)) x y).val

theorem core_at_0 : coreAt 0 = true := by decide +kernel
theorem core_at_1 : coreAt 1 = true := by decide +kernel
theorem core_at_2 : coreAt 2 = true := by decide +kernel
theorem core_at_3 : coreAt 3 = true := by decide +kernel
theorem core_at_4 : coreAt 4 = true := by decide +kernel
theorem core_at_5 : coreAt 5 = true := by decide +kernel
theorem core_at_6 : coreAt 6 = true := by decide +kernel
theorem core_at_7 : coreAt 7 = true := by decide +kernel
theorem core_at_8 : coreAt 8 = true := by decide +kernel
theorem core_at_9 : coreAt 9 = true := by decide +kernel
theorem core_at_10 : coreAt 10 = true := by decide +kernel
theorem core_at_11 : coreAt 11 = true := by decide +kernel
theorem core_at_12 : coreAt 12 = true := by decide +kernel
theorem core_at_13 : coreAt 13 = true := by decide +kernel
theorem core_at_14 : coreAt 14 = true := by decide +kernel
theorem core_at_15 : coreAt 15 = true := by decide +kernel
theorem core_at_16 : coreAt 16 = true := by decide +kernel
theorem core_at_17 : coreAt 17 = true := by decide +kernel
theorem core_at_18 : coreAt 18 = true := by decide +kernel
theorem core_at_19 : coreAt 19 = true := by decide +kernel
theorem core_at_20 : coreAt 20 = true := by decide +kernel
theorem core_at_21 : coreAt 21 = true := by decide +kernel
theorem core_at_22 : coreAt 22 = true := by decide +kernel
theorem core_at_23 : coreAt 23 = true := by decide +kernel
theorem core_at_24 : coreAt 24 = true := by decide +kernel
theorem core_at_25 : coreAt 25 = true := by decide +kernel
theorem core_at_26 : coreAt 26 = true := by decide +kernel
theorem core_at_27 : coreAt 27 = true := by decide +kernel
theorem core_at_28 : coreAt 28 = true := by decide +kernel
theorem core_at_29 : coreAt 29 = true := by decide +kernel
theorem core_at_30 : coreAt 30 = true := by decide +kernel
theorem core_at_31 : coreAt 31 = true := by decide +kernel
theorem core_at_32 : coreAt 32 = true := by decide +kernel
theorem core_at_33 : coreAt 33 = true := by decide +kernel
theorem core_at_34 : coreAt 34 = true := by decide +kernel
theorem core_at_35 : coreAt 35 = true := by decide +kernel
theorem core_at_36 : coreAt 36 = true := by decide +kernel
theorem core_at_37 : coreAt 37 = true := by decide +kernel
theorem core_at_38 : coreAt 38 = true := by decide +kernel
theorem core_at_39 : coreAt 39 = true := by decide +kernel
theorem core_at_40 : coreAt 40 = true := by decide +kernel
theorem core_at_41 : coreAt 41 = true := by decide +kernel
theorem core_at_42 : coreAt 42 = true := by decide +kernel
theorem core_at_43 : coreAt 43 = true := by decide +kernel
theorem core_at_44 : coreAt 44 = true := by decide +kernel
theorem core_at_45 : coreAt 45 = true := by decide +kernel
theorem core_at_46 : coreAt 46 = true := by decide +kernel
theorem core_at_47 : coreAt 47 = true := by decide +kernel
theorem core_at_48 : coreAt 48 = true := by decide +kernel
theorem core_at_49 : coreAt 49 = true := by decide +kernel
theorem core_at_50 : coreAt 50 = true := by decide +kernel
theorem core_at_51 : coreAt 51 = true := by decide +kernel
theorem core_at_52 : coreAt 52 = true := by decide +kernel
theorem core_at_53 : coreAt 53 = true := by decide +kernel
theorem core_at_54 : coreAt 54 = true := by decide +kernel
theorem core_at_55 : coreAt 55 = true := by decide +kernel
theorem core_at_56 : coreAt 56 = true := by decide +kernel
theorem core_at_57 : coreAt 57 = true := by decide +kernel
theorem core_at_58 : coreAt 58 = true := by decide +kernel
theorem core_at_59 : coreAt 59 = true := by decide +kernel
theorem core_at_60 : coreAt 60 = true := by decide +kernel
theorem core_at_61 : coreAt 61 = true := by decide +kernel
theorem core_at_62 : coreAt 62 = true := by decide +kernel
theorem core_at_63 : coreAt 63 = true := by decide +kernel
theorem core_at_64 : coreAt 64 = true := by decide +kernel
theorem core_at_65 : coreAt 65 = true := by decide +kernel
theorem core_at_66 : coreAt 66 = true := by decide +kernel
theorem core_at_67 : coreAt 67 = true := by decide +kernel
theorem core_at_68 : coreAt 68 = true := by decide +kernel
theorem core_at_69 : coreAt 69 = true := by decide +kernel
theorem core_at_70 : coreAt 70 = true := by decide +kernel
theorem core_at_71 : coreAt 71 = true := by decide +kernel
theorem core_at_72 : coreAt 72 = true := by decide +kernel
theorem core_at_73 : coreAt 73 = true := by decide +kernel
theorem core_at_74 : coreAt 74 = true := by decide +kernel
theorem core_at_75 : coreAt 75 = true := by decide +kernel
theorem core_at_76 : coreAt 76 = true := by decide +kernel
theorem core_at_77 : coreAt 77 = true := by decide +kernel
theorem core_at_78 : coreAt 78 = true := by decide +kernel
theorem core_at_79 : coreAt 79 = true := by decide +kernel
theorem core_at_80 : coreAt 80 = true := by decide +kernel
theorem core_at_81 : coreAt 81 = true := by decide +kernel
theorem core_at_82 : coreAt 82 = true := by decide +kernel
theorem core_at_83 : coreAt 83 = true := by decide +kernel
theorem core_at_84 : coreAt 84 = true := by decide +kernel
theorem core_at_85 : coreAt 85 = true := by decide +kernel
theorem core_at_86 : coreAt 86 = true := by decide +kernel
theorem core_at_87 : coreAt 87 = true := by decide +kernel
theorem core_at_88 : coreAt 88 = true := by decide +kernel
theorem core_at_89 : coreAt 89 = true := by decide +kernel
theorem core_at_90 : coreAt 90 = true := by decide +kernel
theorem core_at_91 : coreAt 91 = true := by decide +kernel
theorem core_at_92 : coreAt 92 = true := by decide +kernel
theorem core_at_93 : coreAt 93 = true := by decide +kernel
theorem core_at_94 : coreAt 94 = true := by decide +kernel
theorem core_at_95 : coreAt 95 = true := by decide +kernel
theorem core_at_96 : coreAt 96 = true := by decide +kernel
theorem core_at_97 : coreAt 97 = true := by decide +kernel
theorem core_at_98 : coreAt 98 = true := by decide +kernel
theorem core_at_99 : coreAt 99 = true := by decide +kernel
theorem core_at_100 : coreAt 100 = true := by decide +kernel
theorem core_at_101 : coreAt 101 = true := by decide +kernel
theorem core_at_102 : coreAt 102 = true := by decide +kernel
theorem core_at_103 : coreAt 103 = true := by decide +kernel
theorem core_at_104 : coreAt 104 = true := by decide +kernel
theorem core_at_105 : coreAt 105 = true := by decide +kernel
theorem core_at_106 : coreAt 106 = true := by decide +kernel
theorem core_at_107 : coreAt 107 = true := by decide +kernel
theorem core_at_108 : coreAt 108 = true := by decide +kernel
theorem core_at_109 : coreAt 109 = true := by decide +kernel
theorem core_at_110 : coreAt 110 = true := by decide +kernel
theorem core_at_111 : coreAt 111 = true := by decide +kernel
theorem core_at_112 : coreAt 112 = true := by decide +kernel
theorem core_at_113 : coreAt 113 = true := by decide +kernel
theorem core_at_114 : coreAt 114 = true := by decide +kernel
theorem core_at_115 : coreAt 115 = true := by decide +kernel
theorem core_at_116 : coreAt 116 = true := by decide +kernel
theorem core_at_117 : coreAt 117 = true := by decide +kernel
theorem core_at_118 : coreAt 118 = true := by decide +kernel
theorem core_at_119 : coreAt 119 = true := by decide +kernel
theorem core_at_120 : coreAt 120 = true := by decide +kernel
theorem core_at_121 : coreAt 121 = true := by decide +kernel
theorem core_at_122 : coreAt 122 = true := by decide +kernel
theorem core_at_123 : coreAt 123 = true := by decide +kernel
theorem core_at_124 : coreAt 124 = true := by decide +kernel
theorem core_at_125 : coreAt 125 = true := by decide +kernel
theorem core_at_126 : coreAt 126 = true := by decide +kernel
theorem core_at_127 : coreAt 127 = true := by decide +kernel
theorem core_at_128 : coreAt 128 = true := by decide +kernel
theorem core_at_129 : coreAt 129 = true := by decide +kernel
theorem core_at_130 : coreAt 130 = true := by decide +kernel
theorem core_at_131 : coreAt 131 = true := by decide +kernel
theorem core_at_132 : coreAt 132 = true := by decide +kernel
theorem core_at_133 : coreAt 133 = true := by decide +kernel
theorem core_at_134 : coreAt 134 = true := by decide +kernel
theorem core_at_135 : coreAt 135 = true := by decide +kernel
theorem core_at_136 : coreAt 136 = true := by decide +kernel
theorem core_at_137 : coreAt 137 = true := by decide +kernel
theorem core_at_138 : coreAt 138 = true := by decide +kernel
theorem core_at_139 : coreAt 139 = true := by decide +kernel
theorem core_at_140 : coreAt 140 = true := by decide +kernel
theorem core_at_141 : coreAt 141 = true := by decide +kernel
theorem core_at_142 : coreAt 142 = true := by decide +kernel
theorem core_at_143 : coreAt 143 = true := by decide +kernel
theorem core_at_144 : coreAt 144 = true := by decide +kernel
theorem core_at_145 : coreAt 145 = true := by decide +kernel
theorem core_at_146 : coreAt 146 = true := by decide +kernel
theorem core_at_147 : coreAt 147 = true := by decide +kernel
theorem core_at_148 : coreAt 148 = true := by decide +kernel
theorem core_at_149 : coreAt 149 = true := by decide +kernel
theorem core_at_150 : coreAt 150 = true := by decide +kernel
theorem core_at_151 : coreAt 151 = true := by decide +kernel
theorem core_at_152 : coreAt 152 = true := by decide +kernel
theorem core_at_153 : coreAt 153 = true := by decide +kernel
theorem core_at_154 : coreAt 154 = true := by decide +kernel
theorem core_at_155 : coreAt 155 = true := by decide +kernel

theorem core_at_all (k : Fin 156) : coreAt k.val = true := by
  rcases k with ⟨k,hk⟩
  match k with
  | 0 => exact core_at_0
  | 1 => exact core_at_1
  | 2 => exact core_at_2
  | 3 => exact core_at_3
  | 4 => exact core_at_4
  | 5 => exact core_at_5
  | 6 => exact core_at_6
  | 7 => exact core_at_7
  | 8 => exact core_at_8
  | 9 => exact core_at_9
  | 10 => exact core_at_10
  | 11 => exact core_at_11
  | 12 => exact core_at_12
  | 13 => exact core_at_13
  | 14 => exact core_at_14
  | 15 => exact core_at_15
  | 16 => exact core_at_16
  | 17 => exact core_at_17
  | 18 => exact core_at_18
  | 19 => exact core_at_19
  | 20 => exact core_at_20
  | 21 => exact core_at_21
  | 22 => exact core_at_22
  | 23 => exact core_at_23
  | 24 => exact core_at_24
  | 25 => exact core_at_25
  | 26 => exact core_at_26
  | 27 => exact core_at_27
  | 28 => exact core_at_28
  | 29 => exact core_at_29
  | 30 => exact core_at_30
  | 31 => exact core_at_31
  | 32 => exact core_at_32
  | 33 => exact core_at_33
  | 34 => exact core_at_34
  | 35 => exact core_at_35
  | 36 => exact core_at_36
  | 37 => exact core_at_37
  | 38 => exact core_at_38
  | 39 => exact core_at_39
  | 40 => exact core_at_40
  | 41 => exact core_at_41
  | 42 => exact core_at_42
  | 43 => exact core_at_43
  | 44 => exact core_at_44
  | 45 => exact core_at_45
  | 46 => exact core_at_46
  | 47 => exact core_at_47
  | 48 => exact core_at_48
  | 49 => exact core_at_49
  | 50 => exact core_at_50
  | 51 => exact core_at_51
  | 52 => exact core_at_52
  | 53 => exact core_at_53
  | 54 => exact core_at_54
  | 55 => exact core_at_55
  | 56 => exact core_at_56
  | 57 => exact core_at_57
  | 58 => exact core_at_58
  | 59 => exact core_at_59
  | 60 => exact core_at_60
  | 61 => exact core_at_61
  | 62 => exact core_at_62
  | 63 => exact core_at_63
  | 64 => exact core_at_64
  | 65 => exact core_at_65
  | 66 => exact core_at_66
  | 67 => exact core_at_67
  | 68 => exact core_at_68
  | 69 => exact core_at_69
  | 70 => exact core_at_70
  | 71 => exact core_at_71
  | 72 => exact core_at_72
  | 73 => exact core_at_73
  | 74 => exact core_at_74
  | 75 => exact core_at_75
  | 76 => exact core_at_76
  | 77 => exact core_at_77
  | 78 => exact core_at_78
  | 79 => exact core_at_79
  | 80 => exact core_at_80
  | 81 => exact core_at_81
  | 82 => exact core_at_82
  | 83 => exact core_at_83
  | 84 => exact core_at_84
  | 85 => exact core_at_85
  | 86 => exact core_at_86
  | 87 => exact core_at_87
  | 88 => exact core_at_88
  | 89 => exact core_at_89
  | 90 => exact core_at_90
  | 91 => exact core_at_91
  | 92 => exact core_at_92
  | 93 => exact core_at_93
  | 94 => exact core_at_94
  | 95 => exact core_at_95
  | 96 => exact core_at_96
  | 97 => exact core_at_97
  | 98 => exact core_at_98
  | 99 => exact core_at_99
  | 100 => exact core_at_100
  | 101 => exact core_at_101
  | 102 => exact core_at_102
  | 103 => exact core_at_103
  | 104 => exact core_at_104
  | 105 => exact core_at_105
  | 106 => exact core_at_106
  | 107 => exact core_at_107
  | 108 => exact core_at_108
  | 109 => exact core_at_109
  | 110 => exact core_at_110
  | 111 => exact core_at_111
  | 112 => exact core_at_112
  | 113 => exact core_at_113
  | 114 => exact core_at_114
  | 115 => exact core_at_115
  | 116 => exact core_at_116
  | 117 => exact core_at_117
  | 118 => exact core_at_118
  | 119 => exact core_at_119
  | 120 => exact core_at_120
  | 121 => exact core_at_121
  | 122 => exact core_at_122
  | 123 => exact core_at_123
  | 124 => exact core_at_124
  | 125 => exact core_at_125
  | 126 => exact core_at_126
  | 127 => exact core_at_127
  | 128 => exact core_at_128
  | 129 => exact core_at_129
  | 130 => exact core_at_130
  | 131 => exact core_at_131
  | 132 => exact core_at_132
  | 133 => exact core_at_133
  | 134 => exact core_at_134
  | 135 => exact core_at_135
  | 136 => exact core_at_136
  | 137 => exact core_at_137
  | 138 => exact core_at_138
  | 139 => exact core_at_139
  | 140 => exact core_at_140
  | 141 => exact core_at_141
  | 142 => exact core_at_142
  | 143 => exact core_at_143
  | 144 => exact core_at_144
  | 145 => exact core_at_145
  | 146 => exact core_at_146
  | 147 => exact core_at_147
  | 148 => exact core_at_148
  | 149 => exact core_at_149
  | 150 => exact core_at_150
  | 151 => exact core_at_151
  | 152 => exact core_at_152
  | 153 => exact core_at_153
  | 154 => exact core_at_154
  | 155 => exact core_at_155
  | n+156 => omega

theorem core_identity (k : Fin 156) (x y : Nat) (hx : x<5) (hy : y<5) :
    expanded 3 k (x+2) (y+2) = boardCore (boardVariant k) x y := by
  have hxy := List.all_eq_true.mp
    (List.all_eq_true.mp (core_at_all k) x (List.mem_range.mpr hx)) y (List.mem_range.mpr hy)
  have hi : indexTile k.val = k := by apply Fin.ext; simp [indexTile, Nat.mod_eq_of_lt k.isLt]
  rw [hi] at hxy
  apply Fin.ext
  simpa using hxy

end K230Concrete
#print axioms K230Concrete.core_identity
