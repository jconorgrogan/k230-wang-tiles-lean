module
public import RawExpansion
public import CoreCoordinates
public import ChannelClasses
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Concrete
open K230Verification
@[expose] def seedRecurrenceAt (k : Nat) : Bool :=
  (List.range 4).all fun x => (List.range 4).all fun y =>
    decide (SeedBase (rawExpanded 2 k x y) ↔
      x=0 ∧ y=0 ∧ (SeedBase k ∨ (Wang156.tile k).px=1 ∧ (Wang156.tile k).py=1))
theorem seed_recurrence_0 : seedRecurrenceAt 0=true := by decide +kernel
theorem seed_recurrence_1 : seedRecurrenceAt 1=true := by decide +kernel
theorem seed_recurrence_2 : seedRecurrenceAt 2=true := by decide +kernel
theorem seed_recurrence_3 : seedRecurrenceAt 3=true := by decide +kernel
theorem seed_recurrence_4 : seedRecurrenceAt 4=true := by decide +kernel
theorem seed_recurrence_5 : seedRecurrenceAt 5=true := by decide +kernel
theorem seed_recurrence_6 : seedRecurrenceAt 6=true := by decide +kernel
theorem seed_recurrence_7 : seedRecurrenceAt 7=true := by decide +kernel
theorem seed_recurrence_8 : seedRecurrenceAt 8=true := by decide +kernel
theorem seed_recurrence_9 : seedRecurrenceAt 9=true := by decide +kernel
theorem seed_recurrence_10 : seedRecurrenceAt 10=true := by decide +kernel
theorem seed_recurrence_11 : seedRecurrenceAt 11=true := by decide +kernel
theorem seed_recurrence_12 : seedRecurrenceAt 12=true := by decide +kernel
theorem seed_recurrence_13 : seedRecurrenceAt 13=true := by decide +kernel
theorem seed_recurrence_14 : seedRecurrenceAt 14=true := by decide +kernel
theorem seed_recurrence_15 : seedRecurrenceAt 15=true := by decide +kernel
theorem seed_recurrence_16 : seedRecurrenceAt 16=true := by decide +kernel
theorem seed_recurrence_17 : seedRecurrenceAt 17=true := by decide +kernel
theorem seed_recurrence_18 : seedRecurrenceAt 18=true := by decide +kernel
theorem seed_recurrence_19 : seedRecurrenceAt 19=true := by decide +kernel
theorem seed_recurrence_20 : seedRecurrenceAt 20=true := by decide +kernel
theorem seed_recurrence_21 : seedRecurrenceAt 21=true := by decide +kernel
theorem seed_recurrence_22 : seedRecurrenceAt 22=true := by decide +kernel
theorem seed_recurrence_23 : seedRecurrenceAt 23=true := by decide +kernel
theorem seed_recurrence_24 : seedRecurrenceAt 24=true := by decide +kernel
theorem seed_recurrence_25 : seedRecurrenceAt 25=true := by decide +kernel
theorem seed_recurrence_26 : seedRecurrenceAt 26=true := by decide +kernel
theorem seed_recurrence_27 : seedRecurrenceAt 27=true := by decide +kernel
theorem seed_recurrence_28 : seedRecurrenceAt 28=true := by decide +kernel
theorem seed_recurrence_29 : seedRecurrenceAt 29=true := by decide +kernel
theorem seed_recurrence_30 : seedRecurrenceAt 30=true := by decide +kernel
theorem seed_recurrence_31 : seedRecurrenceAt 31=true := by decide +kernel
theorem seed_recurrence_32 : seedRecurrenceAt 32=true := by decide +kernel
theorem seed_recurrence_33 : seedRecurrenceAt 33=true := by decide +kernel
theorem seed_recurrence_34 : seedRecurrenceAt 34=true := by decide +kernel
theorem seed_recurrence_35 : seedRecurrenceAt 35=true := by decide +kernel
theorem seed_recurrence_36 : seedRecurrenceAt 36=true := by decide +kernel
theorem seed_recurrence_37 : seedRecurrenceAt 37=true := by decide +kernel
theorem seed_recurrence_38 : seedRecurrenceAt 38=true := by decide +kernel
theorem seed_recurrence_39 : seedRecurrenceAt 39=true := by decide +kernel
theorem seed_recurrence_40 : seedRecurrenceAt 40=true := by decide +kernel
theorem seed_recurrence_41 : seedRecurrenceAt 41=true := by decide +kernel
theorem seed_recurrence_42 : seedRecurrenceAt 42=true := by decide +kernel
theorem seed_recurrence_43 : seedRecurrenceAt 43=true := by decide +kernel
theorem seed_recurrence_44 : seedRecurrenceAt 44=true := by decide +kernel
theorem seed_recurrence_45 : seedRecurrenceAt 45=true := by decide +kernel
theorem seed_recurrence_46 : seedRecurrenceAt 46=true := by decide +kernel
theorem seed_recurrence_47 : seedRecurrenceAt 47=true := by decide +kernel
theorem seed_recurrence_48 : seedRecurrenceAt 48=true := by decide +kernel
theorem seed_recurrence_49 : seedRecurrenceAt 49=true := by decide +kernel
theorem seed_recurrence_50 : seedRecurrenceAt 50=true := by decide +kernel
theorem seed_recurrence_51 : seedRecurrenceAt 51=true := by decide +kernel
theorem seed_recurrence_52 : seedRecurrenceAt 52=true := by decide +kernel
theorem seed_recurrence_53 : seedRecurrenceAt 53=true := by decide +kernel
theorem seed_recurrence_54 : seedRecurrenceAt 54=true := by decide +kernel
theorem seed_recurrence_55 : seedRecurrenceAt 55=true := by decide +kernel
theorem seed_recurrence_56 : seedRecurrenceAt 56=true := by decide +kernel
theorem seed_recurrence_57 : seedRecurrenceAt 57=true := by decide +kernel
theorem seed_recurrence_58 : seedRecurrenceAt 58=true := by decide +kernel
theorem seed_recurrence_59 : seedRecurrenceAt 59=true := by decide +kernel
theorem seed_recurrence_60 : seedRecurrenceAt 60=true := by decide +kernel
theorem seed_recurrence_61 : seedRecurrenceAt 61=true := by decide +kernel
theorem seed_recurrence_62 : seedRecurrenceAt 62=true := by decide +kernel
theorem seed_recurrence_63 : seedRecurrenceAt 63=true := by decide +kernel
theorem seed_recurrence_64 : seedRecurrenceAt 64=true := by decide +kernel
theorem seed_recurrence_65 : seedRecurrenceAt 65=true := by decide +kernel
theorem seed_recurrence_66 : seedRecurrenceAt 66=true := by decide +kernel
theorem seed_recurrence_67 : seedRecurrenceAt 67=true := by decide +kernel
theorem seed_recurrence_68 : seedRecurrenceAt 68=true := by decide +kernel
theorem seed_recurrence_69 : seedRecurrenceAt 69=true := by decide +kernel
theorem seed_recurrence_70 : seedRecurrenceAt 70=true := by decide +kernel
theorem seed_recurrence_71 : seedRecurrenceAt 71=true := by decide +kernel
theorem seed_recurrence_72 : seedRecurrenceAt 72=true := by decide +kernel
theorem seed_recurrence_73 : seedRecurrenceAt 73=true := by decide +kernel
theorem seed_recurrence_74 : seedRecurrenceAt 74=true := by decide +kernel
theorem seed_recurrence_75 : seedRecurrenceAt 75=true := by decide +kernel
theorem seed_recurrence_76 : seedRecurrenceAt 76=true := by decide +kernel
theorem seed_recurrence_77 : seedRecurrenceAt 77=true := by decide +kernel
theorem seed_recurrence_78 : seedRecurrenceAt 78=true := by decide +kernel
theorem seed_recurrence_79 : seedRecurrenceAt 79=true := by decide +kernel
theorem seed_recurrence_80 : seedRecurrenceAt 80=true := by decide +kernel
theorem seed_recurrence_81 : seedRecurrenceAt 81=true := by decide +kernel
theorem seed_recurrence_82 : seedRecurrenceAt 82=true := by decide +kernel
theorem seed_recurrence_83 : seedRecurrenceAt 83=true := by decide +kernel
theorem seed_recurrence_84 : seedRecurrenceAt 84=true := by decide +kernel
theorem seed_recurrence_85 : seedRecurrenceAt 85=true := by decide +kernel
theorem seed_recurrence_86 : seedRecurrenceAt 86=true := by decide +kernel
theorem seed_recurrence_87 : seedRecurrenceAt 87=true := by decide +kernel
theorem seed_recurrence_88 : seedRecurrenceAt 88=true := by decide +kernel
theorem seed_recurrence_89 : seedRecurrenceAt 89=true := by decide +kernel
theorem seed_recurrence_90 : seedRecurrenceAt 90=true := by decide +kernel
theorem seed_recurrence_91 : seedRecurrenceAt 91=true := by decide +kernel
theorem seed_recurrence_92 : seedRecurrenceAt 92=true := by decide +kernel
theorem seed_recurrence_93 : seedRecurrenceAt 93=true := by decide +kernel
theorem seed_recurrence_94 : seedRecurrenceAt 94=true := by decide +kernel
theorem seed_recurrence_95 : seedRecurrenceAt 95=true := by decide +kernel
theorem seed_recurrence_96 : seedRecurrenceAt 96=true := by decide +kernel
theorem seed_recurrence_97 : seedRecurrenceAt 97=true := by decide +kernel
theorem seed_recurrence_98 : seedRecurrenceAt 98=true := by decide +kernel
theorem seed_recurrence_99 : seedRecurrenceAt 99=true := by decide +kernel
theorem seed_recurrence_100 : seedRecurrenceAt 100=true := by decide +kernel
theorem seed_recurrence_101 : seedRecurrenceAt 101=true := by decide +kernel
theorem seed_recurrence_102 : seedRecurrenceAt 102=true := by decide +kernel
theorem seed_recurrence_103 : seedRecurrenceAt 103=true := by decide +kernel
theorem seed_recurrence_104 : seedRecurrenceAt 104=true := by decide +kernel
theorem seed_recurrence_105 : seedRecurrenceAt 105=true := by decide +kernel
theorem seed_recurrence_106 : seedRecurrenceAt 106=true := by decide +kernel
theorem seed_recurrence_107 : seedRecurrenceAt 107=true := by decide +kernel
theorem seed_recurrence_108 : seedRecurrenceAt 108=true := by decide +kernel
theorem seed_recurrence_109 : seedRecurrenceAt 109=true := by decide +kernel
theorem seed_recurrence_110 : seedRecurrenceAt 110=true := by decide +kernel
theorem seed_recurrence_111 : seedRecurrenceAt 111=true := by decide +kernel
theorem seed_recurrence_112 : seedRecurrenceAt 112=true := by decide +kernel
theorem seed_recurrence_113 : seedRecurrenceAt 113=true := by decide +kernel
theorem seed_recurrence_114 : seedRecurrenceAt 114=true := by decide +kernel
theorem seed_recurrence_115 : seedRecurrenceAt 115=true := by decide +kernel
theorem seed_recurrence_116 : seedRecurrenceAt 116=true := by decide +kernel
theorem seed_recurrence_117 : seedRecurrenceAt 117=true := by decide +kernel
theorem seed_recurrence_118 : seedRecurrenceAt 118=true := by decide +kernel
theorem seed_recurrence_119 : seedRecurrenceAt 119=true := by decide +kernel
theorem seed_recurrence_120 : seedRecurrenceAt 120=true := by decide +kernel
theorem seed_recurrence_121 : seedRecurrenceAt 121=true := by decide +kernel
theorem seed_recurrence_122 : seedRecurrenceAt 122=true := by decide +kernel
theorem seed_recurrence_123 : seedRecurrenceAt 123=true := by decide +kernel
theorem seed_recurrence_124 : seedRecurrenceAt 124=true := by decide +kernel
theorem seed_recurrence_125 : seedRecurrenceAt 125=true := by decide +kernel
theorem seed_recurrence_126 : seedRecurrenceAt 126=true := by decide +kernel
theorem seed_recurrence_127 : seedRecurrenceAt 127=true := by decide +kernel
theorem seed_recurrence_128 : seedRecurrenceAt 128=true := by decide +kernel
theorem seed_recurrence_129 : seedRecurrenceAt 129=true := by decide +kernel
theorem seed_recurrence_130 : seedRecurrenceAt 130=true := by decide +kernel
theorem seed_recurrence_131 : seedRecurrenceAt 131=true := by decide +kernel
theorem seed_recurrence_132 : seedRecurrenceAt 132=true := by decide +kernel
theorem seed_recurrence_133 : seedRecurrenceAt 133=true := by decide +kernel
theorem seed_recurrence_134 : seedRecurrenceAt 134=true := by decide +kernel
theorem seed_recurrence_135 : seedRecurrenceAt 135=true := by decide +kernel
theorem seed_recurrence_136 : seedRecurrenceAt 136=true := by decide +kernel
theorem seed_recurrence_137 : seedRecurrenceAt 137=true := by decide +kernel
theorem seed_recurrence_138 : seedRecurrenceAt 138=true := by decide +kernel
theorem seed_recurrence_139 : seedRecurrenceAt 139=true := by decide +kernel
theorem seed_recurrence_140 : seedRecurrenceAt 140=true := by decide +kernel
theorem seed_recurrence_141 : seedRecurrenceAt 141=true := by decide +kernel
theorem seed_recurrence_142 : seedRecurrenceAt 142=true := by decide +kernel
theorem seed_recurrence_143 : seedRecurrenceAt 143=true := by decide +kernel
theorem seed_recurrence_144 : seedRecurrenceAt 144=true := by decide +kernel
theorem seed_recurrence_145 : seedRecurrenceAt 145=true := by decide +kernel
theorem seed_recurrence_146 : seedRecurrenceAt 146=true := by decide +kernel
theorem seed_recurrence_147 : seedRecurrenceAt 147=true := by decide +kernel
theorem seed_recurrence_148 : seedRecurrenceAt 148=true := by decide +kernel
theorem seed_recurrence_149 : seedRecurrenceAt 149=true := by decide +kernel
theorem seed_recurrence_150 : seedRecurrenceAt 150=true := by decide +kernel
theorem seed_recurrence_151 : seedRecurrenceAt 151=true := by decide +kernel
theorem seed_recurrence_152 : seedRecurrenceAt 152=true := by decide +kernel
theorem seed_recurrence_153 : seedRecurrenceAt 153=true := by decide +kernel
theorem seed_recurrence_154 : seedRecurrenceAt 154=true := by decide +kernel
theorem seed_recurrence_155 : seedRecurrenceAt 155=true := by decide +kernel

theorem seedRecurrenceChecked (k : Fin 156) : seedRecurrenceAt k.val=true := by
  rcases k with ⟨k,hk⟩
  match k with
  | 0 => exact seed_recurrence_0
  | 1 => exact seed_recurrence_1
  | 2 => exact seed_recurrence_2
  | 3 => exact seed_recurrence_3
  | 4 => exact seed_recurrence_4
  | 5 => exact seed_recurrence_5
  | 6 => exact seed_recurrence_6
  | 7 => exact seed_recurrence_7
  | 8 => exact seed_recurrence_8
  | 9 => exact seed_recurrence_9
  | 10 => exact seed_recurrence_10
  | 11 => exact seed_recurrence_11
  | 12 => exact seed_recurrence_12
  | 13 => exact seed_recurrence_13
  | 14 => exact seed_recurrence_14
  | 15 => exact seed_recurrence_15
  | 16 => exact seed_recurrence_16
  | 17 => exact seed_recurrence_17
  | 18 => exact seed_recurrence_18
  | 19 => exact seed_recurrence_19
  | 20 => exact seed_recurrence_20
  | 21 => exact seed_recurrence_21
  | 22 => exact seed_recurrence_22
  | 23 => exact seed_recurrence_23
  | 24 => exact seed_recurrence_24
  | 25 => exact seed_recurrence_25
  | 26 => exact seed_recurrence_26
  | 27 => exact seed_recurrence_27
  | 28 => exact seed_recurrence_28
  | 29 => exact seed_recurrence_29
  | 30 => exact seed_recurrence_30
  | 31 => exact seed_recurrence_31
  | 32 => exact seed_recurrence_32
  | 33 => exact seed_recurrence_33
  | 34 => exact seed_recurrence_34
  | 35 => exact seed_recurrence_35
  | 36 => exact seed_recurrence_36
  | 37 => exact seed_recurrence_37
  | 38 => exact seed_recurrence_38
  | 39 => exact seed_recurrence_39
  | 40 => exact seed_recurrence_40
  | 41 => exact seed_recurrence_41
  | 42 => exact seed_recurrence_42
  | 43 => exact seed_recurrence_43
  | 44 => exact seed_recurrence_44
  | 45 => exact seed_recurrence_45
  | 46 => exact seed_recurrence_46
  | 47 => exact seed_recurrence_47
  | 48 => exact seed_recurrence_48
  | 49 => exact seed_recurrence_49
  | 50 => exact seed_recurrence_50
  | 51 => exact seed_recurrence_51
  | 52 => exact seed_recurrence_52
  | 53 => exact seed_recurrence_53
  | 54 => exact seed_recurrence_54
  | 55 => exact seed_recurrence_55
  | 56 => exact seed_recurrence_56
  | 57 => exact seed_recurrence_57
  | 58 => exact seed_recurrence_58
  | 59 => exact seed_recurrence_59
  | 60 => exact seed_recurrence_60
  | 61 => exact seed_recurrence_61
  | 62 => exact seed_recurrence_62
  | 63 => exact seed_recurrence_63
  | 64 => exact seed_recurrence_64
  | 65 => exact seed_recurrence_65
  | 66 => exact seed_recurrence_66
  | 67 => exact seed_recurrence_67
  | 68 => exact seed_recurrence_68
  | 69 => exact seed_recurrence_69
  | 70 => exact seed_recurrence_70
  | 71 => exact seed_recurrence_71
  | 72 => exact seed_recurrence_72
  | 73 => exact seed_recurrence_73
  | 74 => exact seed_recurrence_74
  | 75 => exact seed_recurrence_75
  | 76 => exact seed_recurrence_76
  | 77 => exact seed_recurrence_77
  | 78 => exact seed_recurrence_78
  | 79 => exact seed_recurrence_79
  | 80 => exact seed_recurrence_80
  | 81 => exact seed_recurrence_81
  | 82 => exact seed_recurrence_82
  | 83 => exact seed_recurrence_83
  | 84 => exact seed_recurrence_84
  | 85 => exact seed_recurrence_85
  | 86 => exact seed_recurrence_86
  | 87 => exact seed_recurrence_87
  | 88 => exact seed_recurrence_88
  | 89 => exact seed_recurrence_89
  | 90 => exact seed_recurrence_90
  | 91 => exact seed_recurrence_91
  | 92 => exact seed_recurrence_92
  | 93 => exact seed_recurrence_93
  | 94 => exact seed_recurrence_94
  | 95 => exact seed_recurrence_95
  | 96 => exact seed_recurrence_96
  | 97 => exact seed_recurrence_97
  | 98 => exact seed_recurrence_98
  | 99 => exact seed_recurrence_99
  | 100 => exact seed_recurrence_100
  | 101 => exact seed_recurrence_101
  | 102 => exact seed_recurrence_102
  | 103 => exact seed_recurrence_103
  | 104 => exact seed_recurrence_104
  | 105 => exact seed_recurrence_105
  | 106 => exact seed_recurrence_106
  | 107 => exact seed_recurrence_107
  | 108 => exact seed_recurrence_108
  | 109 => exact seed_recurrence_109
  | 110 => exact seed_recurrence_110
  | 111 => exact seed_recurrence_111
  | 112 => exact seed_recurrence_112
  | 113 => exact seed_recurrence_113
  | 114 => exact seed_recurrence_114
  | 115 => exact seed_recurrence_115
  | 116 => exact seed_recurrence_116
  | 117 => exact seed_recurrence_117
  | 118 => exact seed_recurrence_118
  | 119 => exact seed_recurrence_119
  | 120 => exact seed_recurrence_120
  | 121 => exact seed_recurrence_121
  | 122 => exact seed_recurrence_122
  | 123 => exact seed_recurrence_123
  | 124 => exact seed_recurrence_124
  | 125 => exact seed_recurrence_125
  | 126 => exact seed_recurrence_126
  | 127 => exact seed_recurrence_127
  | 128 => exact seed_recurrence_128
  | 129 => exact seed_recurrence_129
  | 130 => exact seed_recurrence_130
  | 131 => exact seed_recurrence_131
  | 132 => exact seed_recurrence_132
  | 133 => exact seed_recurrence_133
  | 134 => exact seed_recurrence_134
  | 135 => exact seed_recurrence_135
  | 136 => exact seed_recurrence_136
  | 137 => exact seed_recurrence_137
  | 138 => exact seed_recurrence_138
  | 139 => exact seed_recurrence_139
  | 140 => exact seed_recurrence_140
  | 141 => exact seed_recurrence_141
  | 142 => exact seed_recurrence_142
  | 143 => exact seed_recurrence_143
  | 144 => exact seed_recurrence_144
  | 145 => exact seed_recurrence_145
  | 146 => exact seed_recurrence_146
  | 147 => exact seed_recurrence_147
  | 148 => exact seed_recurrence_148
  | 149 => exact seed_recurrence_149
  | 150 => exact seed_recurrence_150
  | 151 => exact seed_recurrence_151
  | 152 => exact seed_recurrence_152
  | 153 => exact seed_recurrence_153
  | 154 => exact seed_recurrence_154
  | 155 => exact seed_recurrence_155
  | k+156 => omega

theorem expanded_two_seed_iff (k : Fin 156) (x y : Nat) (hx:x<4) (hy:y<4) :
    SeedBase (expanded 2 k x y).val ↔
      x=0 ∧ y=0 ∧ (SeedBase k.val ∨ (Wang156.tile k.val).px=1 ∧ (Wang156.tile k.val).py=1) := by
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (seedRecurrenceChecked k) x (List.mem_range.mpr hx)) y (List.mem_range.mpr hy)
  rw [expanded_value]
  exact of_decide_eq_true h

@[expose] def seedCoreChecked : Bool :=
  (List.range 4).all fun v => (List.range 5).all fun x => (List.range 5).all fun y =>
    decide (SeedBase (rawExpanded 3 (representativeNat v) (x+2) (y+2)) ↔ x=2 ∧ y=2)
theorem seed_core_checked : seedCoreChecked=true := by decide +kernel

theorem core_seed_iff (v x y : Nat) (hv:v<4) (hx:x≤4) (hy:y≤4) :
    SeedBase (boardCore v x y).val ↔ x=2 ∧ y=2 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp seed_core_checked v (List.mem_range.mpr hv))
      x (List.mem_range.mpr (by omega))) y (List.mem_range.mpr (by omega))
  have he : (boardCore v x y).val = rawExpanded 3 (representativeNat v) (x+2) (y+2) := by
    change (expanded 3 (coreRepresentative v) (x+2) (y+2)).val = _
    rw [expanded_value,coreRepresentative_value]
  rw [he]
  exact of_decide_eq_true h
end K230Concrete
#print axioms K230Concrete.expanded_two_seed_iff
#print axioms K230Concrete.core_seed_iff
