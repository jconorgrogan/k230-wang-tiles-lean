module
public import RedStatusCertificate
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K230Concrete
theorem redRecurrenceChecked (k : Fin 156) : redRecurrenceAt k.val=true := by
  rcases k with ⟨k,hk⟩
  match k with
  | 0 => exact red_recurrence_0
  | 1 => exact red_recurrence_1
  | 2 => exact red_recurrence_2
  | 3 => exact red_recurrence_3
  | 4 => exact red_recurrence_4
  | 5 => exact red_recurrence_5
  | 6 => exact red_recurrence_6
  | 7 => exact red_recurrence_7
  | 8 => exact red_recurrence_8
  | 9 => exact red_recurrence_9
  | 10 => exact red_recurrence_10
  | 11 => exact red_recurrence_11
  | 12 => exact red_recurrence_12
  | 13 => exact red_recurrence_13
  | 14 => exact red_recurrence_14
  | 15 => exact red_recurrence_15
  | 16 => exact red_recurrence_16
  | 17 => exact red_recurrence_17
  | 18 => exact red_recurrence_18
  | 19 => exact red_recurrence_19
  | 20 => exact red_recurrence_20
  | 21 => exact red_recurrence_21
  | 22 => exact red_recurrence_22
  | 23 => exact red_recurrence_23
  | 24 => exact red_recurrence_24
  | 25 => exact red_recurrence_25
  | 26 => exact red_recurrence_26
  | 27 => exact red_recurrence_27
  | 28 => exact red_recurrence_28
  | 29 => exact red_recurrence_29
  | 30 => exact red_recurrence_30
  | 31 => exact red_recurrence_31
  | 32 => exact red_recurrence_32
  | 33 => exact red_recurrence_33
  | 34 => exact red_recurrence_34
  | 35 => exact red_recurrence_35
  | 36 => exact red_recurrence_36
  | 37 => exact red_recurrence_37
  | 38 => exact red_recurrence_38
  | 39 => exact red_recurrence_39
  | 40 => exact red_recurrence_40
  | 41 => exact red_recurrence_41
  | 42 => exact red_recurrence_42
  | 43 => exact red_recurrence_43
  | 44 => exact red_recurrence_44
  | 45 => exact red_recurrence_45
  | 46 => exact red_recurrence_46
  | 47 => exact red_recurrence_47
  | 48 => exact red_recurrence_48
  | 49 => exact red_recurrence_49
  | 50 => exact red_recurrence_50
  | 51 => exact red_recurrence_51
  | 52 => exact red_recurrence_52
  | 53 => exact red_recurrence_53
  | 54 => exact red_recurrence_54
  | 55 => exact red_recurrence_55
  | 56 => exact red_recurrence_56
  | 57 => exact red_recurrence_57
  | 58 => exact red_recurrence_58
  | 59 => exact red_recurrence_59
  | 60 => exact red_recurrence_60
  | 61 => exact red_recurrence_61
  | 62 => exact red_recurrence_62
  | 63 => exact red_recurrence_63
  | 64 => exact red_recurrence_64
  | 65 => exact red_recurrence_65
  | 66 => exact red_recurrence_66
  | 67 => exact red_recurrence_67
  | 68 => exact red_recurrence_68
  | 69 => exact red_recurrence_69
  | 70 => exact red_recurrence_70
  | 71 => exact red_recurrence_71
  | 72 => exact red_recurrence_72
  | 73 => exact red_recurrence_73
  | 74 => exact red_recurrence_74
  | 75 => exact red_recurrence_75
  | 76 => exact red_recurrence_76
  | 77 => exact red_recurrence_77
  | 78 => exact red_recurrence_78
  | 79 => exact red_recurrence_79
  | 80 => exact red_recurrence_80
  | 81 => exact red_recurrence_81
  | 82 => exact red_recurrence_82
  | 83 => exact red_recurrence_83
  | 84 => exact red_recurrence_84
  | 85 => exact red_recurrence_85
  | 86 => exact red_recurrence_86
  | 87 => exact red_recurrence_87
  | 88 => exact red_recurrence_88
  | 89 => exact red_recurrence_89
  | 90 => exact red_recurrence_90
  | 91 => exact red_recurrence_91
  | 92 => exact red_recurrence_92
  | 93 => exact red_recurrence_93
  | 94 => exact red_recurrence_94
  | 95 => exact red_recurrence_95
  | 96 => exact red_recurrence_96
  | 97 => exact red_recurrence_97
  | 98 => exact red_recurrence_98
  | 99 => exact red_recurrence_99
  | 100 => exact red_recurrence_100
  | 101 => exact red_recurrence_101
  | 102 => exact red_recurrence_102
  | 103 => exact red_recurrence_103
  | 104 => exact red_recurrence_104
  | 105 => exact red_recurrence_105
  | 106 => exact red_recurrence_106
  | 107 => exact red_recurrence_107
  | 108 => exact red_recurrence_108
  | 109 => exact red_recurrence_109
  | 110 => exact red_recurrence_110
  | 111 => exact red_recurrence_111
  | 112 => exact red_recurrence_112
  | 113 => exact red_recurrence_113
  | 114 => exact red_recurrence_114
  | 115 => exact red_recurrence_115
  | 116 => exact red_recurrence_116
  | 117 => exact red_recurrence_117
  | 118 => exact red_recurrence_118
  | 119 => exact red_recurrence_119
  | 120 => exact red_recurrence_120
  | 121 => exact red_recurrence_121
  | 122 => exact red_recurrence_122
  | 123 => exact red_recurrence_123
  | 124 => exact red_recurrence_124
  | 125 => exact red_recurrence_125
  | 126 => exact red_recurrence_126
  | 127 => exact red_recurrence_127
  | 128 => exact red_recurrence_128
  | 129 => exact red_recurrence_129
  | 130 => exact red_recurrence_130
  | 131 => exact red_recurrence_131
  | 132 => exact red_recurrence_132
  | 133 => exact red_recurrence_133
  | 134 => exact red_recurrence_134
  | 135 => exact red_recurrence_135
  | 136 => exact red_recurrence_136
  | 137 => exact red_recurrence_137
  | 138 => exact red_recurrence_138
  | 139 => exact red_recurrence_139
  | 140 => exact red_recurrence_140
  | 141 => exact red_recurrence_141
  | 142 => exact red_recurrence_142
  | 143 => exact red_recurrence_143
  | 144 => exact red_recurrence_144
  | 145 => exact red_recurrence_145
  | 146 => exact red_recurrence_146
  | 147 => exact red_recurrence_147
  | 148 => exact red_recurrence_148
  | 149 => exact red_recurrence_149
  | 150 => exact red_recurrence_150
  | 151 => exact red_recurrence_151
  | 152 => exact red_recurrence_152
  | 153 => exact red_recurrence_153
  | 154 => exact red_recurrence_154
  | 155 => exact red_recurrence_155
  | n+156 => omega

theorem red_status_step (k : Fin 156) (x y : Nat) (hx : x<4) (hy : y<4) :
    let a := lowestRed (Wang156.tile k.val).px (Wang156.tile k.val).py x y
    let b := refineRed (redStatus k.val) x y
    (a=0 ∨ b=0) ∧ redStatus (expanded 2 k x y).val = (if a=0 then b else a) := by
  have h := List.all_eq_true.mp (redRecurrenceChecked k) x (List.mem_range.mpr hx)
  have h := List.all_eq_true.mp h y (List.mem_range.mpr hy)
  simpa [expanded_value] using h

theorem red_status_boundary (k : Fin 156) :
    (K230Verification.hBoundary k.val → redStatus k.val=1 ∨ redStatus k.val=2) ∧
    (K230Verification.vBoundary k.val → redStatus k.val=3 ∨ redStatus k.val=4) := by
  have h : ∀ k : Fin 156,
    (K230Verification.hBoundary k.val → redStatus k.val=1 ∨ redStatus k.val=2) ∧
    (K230Verification.vBoundary k.val → redStatus k.val=3 ∨ redStatus k.val=4) := by decide +kernel
  exact h k

@[expose] def coreRedCheck : Bool := (List.range 4).all fun v =>
  (List.range 5).all fun x => (List.range 5).all fun y =>
    (redStatus (rawExpanded 3 (coreRepresentative v).val (x+2) (y+2)) ==
      rectStatus 0 4 0 4 x y) &&
    ((Wang156.tile (rawExpanded 3 (coreRepresentative v).val (x+2) (y+2))).px == x%2) &&
    ((Wang156.tile (rawExpanded 3 (coreRepresentative v).val (x+2) (y+2))).py == y%2)

theorem coreRedChecked : coreRedCheck=true := by decide +kernel

theorem core_red_status (v x y : Nat) (hv : v<4) (hx : x≤4) (hy : y≤4) :
    redStatus (boardCore v x y).val = rectStatus 0 4 0 4 x y ∧
    (Wang156.tile (boardCore v x y).val).px=x%2 ∧
    (Wang156.tile (boardCore v x y).val).py=y%2 := by
  have h := List.all_eq_true.mp coreRedChecked v (List.mem_range.mpr hv)
  have h := List.all_eq_true.mp h x (List.mem_range.mpr (by omega))
  have h := List.all_eq_true.mp h y (List.mem_range.mpr (by omega))
  simpa [boardCore,expanded_value,and_assoc] using h

end K230Concrete
#print axioms K230Concrete.red_status_step
#print axioms K230Concrete.core_red_status
