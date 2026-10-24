module
public import ConcreteWitness
public import ChannelClasses
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification

@[expose] def expansion2 (k x y : Nat) : Nat :=
  Wang156.sigma (Wang156.sigma k ((x/2)%2 + 2*((y/2)%2))) (x%2 + 2*(y%2))

theorem expanded_two_value (k : Fin 156) (x y : Nat) :
    (expanded 2 k x y).val = expansion2 k.val x y := rfl

@[expose] def localityAt (k : Nat) : Bool :=
  (expansion2 k 1 1 == 155) &&
  (List.range 4).all (fun x => (List.range 4).all fun y =>
    decide ((HasHChannel (expansion2 k x y) ↔ y=1) ∧
      (HasVChannel (expansion2 k x y) ↔ x=1)))
@[expose] def seedFixedCheck : Bool := seedBases.all fun k => expansion2 k 0 0 == k
theorem locality_at_0 : localityAt 0 = true := by decide +kernel
theorem locality_at_1 : localityAt 1 = true := by decide +kernel
theorem locality_at_2 : localityAt 2 = true := by decide +kernel
theorem locality_at_3 : localityAt 3 = true := by decide +kernel
theorem locality_at_4 : localityAt 4 = true := by decide +kernel
theorem locality_at_5 : localityAt 5 = true := by decide +kernel
theorem locality_at_6 : localityAt 6 = true := by decide +kernel
theorem locality_at_7 : localityAt 7 = true := by decide +kernel
theorem locality_at_8 : localityAt 8 = true := by decide +kernel
theorem locality_at_9 : localityAt 9 = true := by decide +kernel
theorem locality_at_10 : localityAt 10 = true := by decide +kernel
theorem locality_at_11 : localityAt 11 = true := by decide +kernel
theorem locality_at_12 : localityAt 12 = true := by decide +kernel
theorem locality_at_13 : localityAt 13 = true := by decide +kernel
theorem locality_at_14 : localityAt 14 = true := by decide +kernel
theorem locality_at_15 : localityAt 15 = true := by decide +kernel
theorem locality_at_16 : localityAt 16 = true := by decide +kernel
theorem locality_at_17 : localityAt 17 = true := by decide +kernel
theorem locality_at_18 : localityAt 18 = true := by decide +kernel
theorem locality_at_19 : localityAt 19 = true := by decide +kernel
theorem locality_at_20 : localityAt 20 = true := by decide +kernel
theorem locality_at_21 : localityAt 21 = true := by decide +kernel
theorem locality_at_22 : localityAt 22 = true := by decide +kernel
theorem locality_at_23 : localityAt 23 = true := by decide +kernel
theorem locality_at_24 : localityAt 24 = true := by decide +kernel
theorem locality_at_25 : localityAt 25 = true := by decide +kernel
theorem locality_at_26 : localityAt 26 = true := by decide +kernel
theorem locality_at_27 : localityAt 27 = true := by decide +kernel
theorem locality_at_28 : localityAt 28 = true := by decide +kernel
theorem locality_at_29 : localityAt 29 = true := by decide +kernel
theorem locality_at_30 : localityAt 30 = true := by decide +kernel
theorem locality_at_31 : localityAt 31 = true := by decide +kernel
theorem locality_at_32 : localityAt 32 = true := by decide +kernel
theorem locality_at_33 : localityAt 33 = true := by decide +kernel
theorem locality_at_34 : localityAt 34 = true := by decide +kernel
theorem locality_at_35 : localityAt 35 = true := by decide +kernel
theorem locality_at_36 : localityAt 36 = true := by decide +kernel
theorem locality_at_37 : localityAt 37 = true := by decide +kernel
theorem locality_at_38 : localityAt 38 = true := by decide +kernel
theorem locality_at_39 : localityAt 39 = true := by decide +kernel
theorem locality_at_40 : localityAt 40 = true := by decide +kernel
theorem locality_at_41 : localityAt 41 = true := by decide +kernel
theorem locality_at_42 : localityAt 42 = true := by decide +kernel
theorem locality_at_43 : localityAt 43 = true := by decide +kernel
theorem locality_at_44 : localityAt 44 = true := by decide +kernel
theorem locality_at_45 : localityAt 45 = true := by decide +kernel
theorem locality_at_46 : localityAt 46 = true := by decide +kernel
theorem locality_at_47 : localityAt 47 = true := by decide +kernel
theorem locality_at_48 : localityAt 48 = true := by decide +kernel
theorem locality_at_49 : localityAt 49 = true := by decide +kernel
theorem locality_at_50 : localityAt 50 = true := by decide +kernel
theorem locality_at_51 : localityAt 51 = true := by decide +kernel
theorem locality_at_52 : localityAt 52 = true := by decide +kernel
theorem locality_at_53 : localityAt 53 = true := by decide +kernel
theorem locality_at_54 : localityAt 54 = true := by decide +kernel
theorem locality_at_55 : localityAt 55 = true := by decide +kernel
theorem locality_at_56 : localityAt 56 = true := by decide +kernel
theorem locality_at_57 : localityAt 57 = true := by decide +kernel
theorem locality_at_58 : localityAt 58 = true := by decide +kernel
theorem locality_at_59 : localityAt 59 = true := by decide +kernel
theorem locality_at_60 : localityAt 60 = true := by decide +kernel
theorem locality_at_61 : localityAt 61 = true := by decide +kernel
theorem locality_at_62 : localityAt 62 = true := by decide +kernel
theorem locality_at_63 : localityAt 63 = true := by decide +kernel
theorem locality_at_64 : localityAt 64 = true := by decide +kernel
theorem locality_at_65 : localityAt 65 = true := by decide +kernel
theorem locality_at_66 : localityAt 66 = true := by decide +kernel
theorem locality_at_67 : localityAt 67 = true := by decide +kernel
theorem locality_at_68 : localityAt 68 = true := by decide +kernel
theorem locality_at_69 : localityAt 69 = true := by decide +kernel
theorem locality_at_70 : localityAt 70 = true := by decide +kernel
theorem locality_at_71 : localityAt 71 = true := by decide +kernel
theorem locality_at_72 : localityAt 72 = true := by decide +kernel
theorem locality_at_73 : localityAt 73 = true := by decide +kernel
theorem locality_at_74 : localityAt 74 = true := by decide +kernel
theorem locality_at_75 : localityAt 75 = true := by decide +kernel
theorem locality_at_76 : localityAt 76 = true := by decide +kernel
theorem locality_at_77 : localityAt 77 = true := by decide +kernel
theorem locality_at_78 : localityAt 78 = true := by decide +kernel
theorem locality_at_79 : localityAt 79 = true := by decide +kernel
theorem locality_at_80 : localityAt 80 = true := by decide +kernel
theorem locality_at_81 : localityAt 81 = true := by decide +kernel
theorem locality_at_82 : localityAt 82 = true := by decide +kernel
theorem locality_at_83 : localityAt 83 = true := by decide +kernel
theorem locality_at_84 : localityAt 84 = true := by decide +kernel
theorem locality_at_85 : localityAt 85 = true := by decide +kernel
theorem locality_at_86 : localityAt 86 = true := by decide +kernel
theorem locality_at_87 : localityAt 87 = true := by decide +kernel
theorem locality_at_88 : localityAt 88 = true := by decide +kernel
theorem locality_at_89 : localityAt 89 = true := by decide +kernel
theorem locality_at_90 : localityAt 90 = true := by decide +kernel
theorem locality_at_91 : localityAt 91 = true := by decide +kernel
theorem locality_at_92 : localityAt 92 = true := by decide +kernel
theorem locality_at_93 : localityAt 93 = true := by decide +kernel
theorem locality_at_94 : localityAt 94 = true := by decide +kernel
theorem locality_at_95 : localityAt 95 = true := by decide +kernel
theorem locality_at_96 : localityAt 96 = true := by decide +kernel
theorem locality_at_97 : localityAt 97 = true := by decide +kernel
theorem locality_at_98 : localityAt 98 = true := by decide +kernel
theorem locality_at_99 : localityAt 99 = true := by decide +kernel
theorem locality_at_100 : localityAt 100 = true := by decide +kernel
theorem locality_at_101 : localityAt 101 = true := by decide +kernel
theorem locality_at_102 : localityAt 102 = true := by decide +kernel
theorem locality_at_103 : localityAt 103 = true := by decide +kernel
theorem locality_at_104 : localityAt 104 = true := by decide +kernel
theorem locality_at_105 : localityAt 105 = true := by decide +kernel
theorem locality_at_106 : localityAt 106 = true := by decide +kernel
theorem locality_at_107 : localityAt 107 = true := by decide +kernel
theorem locality_at_108 : localityAt 108 = true := by decide +kernel
theorem locality_at_109 : localityAt 109 = true := by decide +kernel
theorem locality_at_110 : localityAt 110 = true := by decide +kernel
theorem locality_at_111 : localityAt 111 = true := by decide +kernel
theorem locality_at_112 : localityAt 112 = true := by decide +kernel
theorem locality_at_113 : localityAt 113 = true := by decide +kernel
theorem locality_at_114 : localityAt 114 = true := by decide +kernel
theorem locality_at_115 : localityAt 115 = true := by decide +kernel
theorem locality_at_116 : localityAt 116 = true := by decide +kernel
theorem locality_at_117 : localityAt 117 = true := by decide +kernel
theorem locality_at_118 : localityAt 118 = true := by decide +kernel
theorem locality_at_119 : localityAt 119 = true := by decide +kernel
theorem locality_at_120 : localityAt 120 = true := by decide +kernel
theorem locality_at_121 : localityAt 121 = true := by decide +kernel
theorem locality_at_122 : localityAt 122 = true := by decide +kernel
theorem locality_at_123 : localityAt 123 = true := by decide +kernel
theorem locality_at_124 : localityAt 124 = true := by decide +kernel
theorem locality_at_125 : localityAt 125 = true := by decide +kernel
theorem locality_at_126 : localityAt 126 = true := by decide +kernel
theorem locality_at_127 : localityAt 127 = true := by decide +kernel
theorem locality_at_128 : localityAt 128 = true := by decide +kernel
theorem locality_at_129 : localityAt 129 = true := by decide +kernel
theorem locality_at_130 : localityAt 130 = true := by decide +kernel
theorem locality_at_131 : localityAt 131 = true := by decide +kernel
theorem locality_at_132 : localityAt 132 = true := by decide +kernel
theorem locality_at_133 : localityAt 133 = true := by decide +kernel
theorem locality_at_134 : localityAt 134 = true := by decide +kernel
theorem locality_at_135 : localityAt 135 = true := by decide +kernel
theorem locality_at_136 : localityAt 136 = true := by decide +kernel
theorem locality_at_137 : localityAt 137 = true := by decide +kernel
theorem locality_at_138 : localityAt 138 = true := by decide +kernel
theorem locality_at_139 : localityAt 139 = true := by decide +kernel
theorem locality_at_140 : localityAt 140 = true := by decide +kernel
theorem locality_at_141 : localityAt 141 = true := by decide +kernel
theorem locality_at_142 : localityAt 142 = true := by decide +kernel
theorem locality_at_143 : localityAt 143 = true := by decide +kernel
theorem locality_at_144 : localityAt 144 = true := by decide +kernel
theorem locality_at_145 : localityAt 145 = true := by decide +kernel
theorem locality_at_146 : localityAt 146 = true := by decide +kernel
theorem locality_at_147 : localityAt 147 = true := by decide +kernel
theorem locality_at_148 : localityAt 148 = true := by decide +kernel
theorem locality_at_149 : localityAt 149 = true := by decide +kernel
theorem locality_at_150 : localityAt 150 = true := by decide +kernel
theorem locality_at_151 : localityAt 151 = true := by decide +kernel
theorem locality_at_152 : localityAt 152 = true := by decide +kernel
theorem locality_at_153 : localityAt 153 = true := by decide +kernel
theorem locality_at_154 : localityAt 154 = true := by decide +kernel
theorem locality_at_155 : localityAt 155 = true := by decide +kernel
theorem locality_at_all (k : Fin 156) : localityAt k.val = true := by
  rcases k with ⟨k,hk⟩
  match k with
  | 0 => exact locality_at_0
  | 1 => exact locality_at_1
  | 2 => exact locality_at_2
  | 3 => exact locality_at_3
  | 4 => exact locality_at_4
  | 5 => exact locality_at_5
  | 6 => exact locality_at_6
  | 7 => exact locality_at_7
  | 8 => exact locality_at_8
  | 9 => exact locality_at_9
  | 10 => exact locality_at_10
  | 11 => exact locality_at_11
  | 12 => exact locality_at_12
  | 13 => exact locality_at_13
  | 14 => exact locality_at_14
  | 15 => exact locality_at_15
  | 16 => exact locality_at_16
  | 17 => exact locality_at_17
  | 18 => exact locality_at_18
  | 19 => exact locality_at_19
  | 20 => exact locality_at_20
  | 21 => exact locality_at_21
  | 22 => exact locality_at_22
  | 23 => exact locality_at_23
  | 24 => exact locality_at_24
  | 25 => exact locality_at_25
  | 26 => exact locality_at_26
  | 27 => exact locality_at_27
  | 28 => exact locality_at_28
  | 29 => exact locality_at_29
  | 30 => exact locality_at_30
  | 31 => exact locality_at_31
  | 32 => exact locality_at_32
  | 33 => exact locality_at_33
  | 34 => exact locality_at_34
  | 35 => exact locality_at_35
  | 36 => exact locality_at_36
  | 37 => exact locality_at_37
  | 38 => exact locality_at_38
  | 39 => exact locality_at_39
  | 40 => exact locality_at_40
  | 41 => exact locality_at_41
  | 42 => exact locality_at_42
  | 43 => exact locality_at_43
  | 44 => exact locality_at_44
  | 45 => exact locality_at_45
  | 46 => exact locality_at_46
  | 47 => exact locality_at_47
  | 48 => exact locality_at_48
  | 49 => exact locality_at_49
  | 50 => exact locality_at_50
  | 51 => exact locality_at_51
  | 52 => exact locality_at_52
  | 53 => exact locality_at_53
  | 54 => exact locality_at_54
  | 55 => exact locality_at_55
  | 56 => exact locality_at_56
  | 57 => exact locality_at_57
  | 58 => exact locality_at_58
  | 59 => exact locality_at_59
  | 60 => exact locality_at_60
  | 61 => exact locality_at_61
  | 62 => exact locality_at_62
  | 63 => exact locality_at_63
  | 64 => exact locality_at_64
  | 65 => exact locality_at_65
  | 66 => exact locality_at_66
  | 67 => exact locality_at_67
  | 68 => exact locality_at_68
  | 69 => exact locality_at_69
  | 70 => exact locality_at_70
  | 71 => exact locality_at_71
  | 72 => exact locality_at_72
  | 73 => exact locality_at_73
  | 74 => exact locality_at_74
  | 75 => exact locality_at_75
  | 76 => exact locality_at_76
  | 77 => exact locality_at_77
  | 78 => exact locality_at_78
  | 79 => exact locality_at_79
  | 80 => exact locality_at_80
  | 81 => exact locality_at_81
  | 82 => exact locality_at_82
  | 83 => exact locality_at_83
  | 84 => exact locality_at_84
  | 85 => exact locality_at_85
  | 86 => exact locality_at_86
  | 87 => exact locality_at_87
  | 88 => exact locality_at_88
  | 89 => exact locality_at_89
  | 90 => exact locality_at_90
  | 91 => exact locality_at_91
  | 92 => exact locality_at_92
  | 93 => exact locality_at_93
  | 94 => exact locality_at_94
  | 95 => exact locality_at_95
  | 96 => exact locality_at_96
  | 97 => exact locality_at_97
  | 98 => exact locality_at_98
  | 99 => exact locality_at_99
  | 100 => exact locality_at_100
  | 101 => exact locality_at_101
  | 102 => exact locality_at_102
  | 103 => exact locality_at_103
  | 104 => exact locality_at_104
  | 105 => exact locality_at_105
  | 106 => exact locality_at_106
  | 107 => exact locality_at_107
  | 108 => exact locality_at_108
  | 109 => exact locality_at_109
  | 110 => exact locality_at_110
  | 111 => exact locality_at_111
  | 112 => exact locality_at_112
  | 113 => exact locality_at_113
  | 114 => exact locality_at_114
  | 115 => exact locality_at_115
  | 116 => exact locality_at_116
  | 117 => exact locality_at_117
  | 118 => exact locality_at_118
  | 119 => exact locality_at_119
  | 120 => exact locality_at_120
  | 121 => exact locality_at_121
  | 122 => exact locality_at_122
  | 123 => exact locality_at_123
  | 124 => exact locality_at_124
  | 125 => exact locality_at_125
  | 126 => exact locality_at_126
  | 127 => exact locality_at_127
  | 128 => exact locality_at_128
  | 129 => exact locality_at_129
  | 130 => exact locality_at_130
  | 131 => exact locality_at_131
  | 132 => exact locality_at_132
  | 133 => exact locality_at_133
  | 134 => exact locality_at_134
  | 135 => exact locality_at_135
  | 136 => exact locality_at_136
  | 137 => exact locality_at_137
  | 138 => exact locality_at_138
  | 139 => exact locality_at_139
  | 140 => exact locality_at_140
  | 141 => exact locality_at_141
  | 142 => exact locality_at_142
  | 143 => exact locality_at_143
  | 144 => exact locality_at_144
  | 145 => exact locality_at_145
  | 146 => exact locality_at_146
  | 147 => exact locality_at_147
  | 148 => exact locality_at_148
  | 149 => exact locality_at_149
  | 150 => exact locality_at_150
  | 151 => exact locality_at_151
  | 152 => exact locality_at_152
  | 153 => exact locality_at_153
  | 154 => exact locality_at_154
  | 155 => exact locality_at_155
  | n+156 => omega

theorem seedFixed_checked : seedFixedCheck = true := by decide +kernel


end K230Concrete
