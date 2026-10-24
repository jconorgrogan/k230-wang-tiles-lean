module
public import ArcDomains
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Wang156
@[expose] def arc0 : ArcCertificate := ⟨⟨0, 120, 90, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc0_checked : checkArc arc0 = true := by decide +kernel
#print axioms arc0_checked
@[expose] def arc1 : ArcCertificate := ⟨⟨1, 148, 88, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc1_checked : checkArc arc1 = true := by decide +kernel
#print axioms arc1_checked
@[expose] def arc2 : ArcCertificate := ⟨⟨2, 121, 90, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc2_checked : checkArc arc2 = true := by decide +kernel
#print axioms arc2_checked
@[expose] def arc3 : ArcCertificate := ⟨⟨3, 149, 88, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc3_checked : checkArc arc3 = true := by decide +kernel
#print axioms arc3_checked
@[expose] def arc4 : ArcCertificate := ⟨⟨4, 150, 88, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc4_checked : checkArc arc4 = true := by decide +kernel
#print axioms arc4_checked
@[expose] def arc5 : ArcCertificate := ⟨⟨6, 124, 90, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc5_checked : checkArc arc5 = true := by decide +kernel
#print axioms arc5_checked
@[expose] def arc6 : ArcCertificate := ⟨⟨7, 151, 88, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc6_checked : checkArc arc6 = true := by decide +kernel
#print axioms arc6_checked
@[expose] def arc7 : ArcCertificate := ⟨⟨8, 125, 90, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc7_checked : checkArc arc7 = true := by decide +kernel
#print axioms arc7_checked
@[expose] def arc8 : ArcCertificate := ⟨⟨16, 120, 93, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc8_checked : checkArc arc8 = true := by decide +kernel
#print axioms arc8_checked
@[expose] def arc9 : ArcCertificate := ⟨⟨17, 148, 91, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc9_checked : checkArc arc9 = true := by decide +kernel
#print axioms arc9_checked
@[expose] def arc10 : ArcCertificate := ⟨⟨18, 121, 93, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc10_checked : checkArc arc10 = true := by decide +kernel
#print axioms arc10_checked
@[expose] def arc11 : ArcCertificate := ⟨⟨19, 149, 91, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc11_checked : checkArc arc11 = true := by decide +kernel
#print axioms arc11_checked
@[expose] def arc12 : ArcCertificate := ⟨⟨20, 150, 91, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc12_checked : checkArc arc12 = true := by decide +kernel
#print axioms arc12_checked
@[expose] def arc13 : ArcCertificate := ⟨⟨22, 124, 93, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc13_checked : checkArc arc13 = true := by decide +kernel
#print axioms arc13_checked
@[expose] def arc14 : ArcCertificate := ⟨⟨23, 151, 91, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc14_checked : checkArc arc14 = true := by decide +kernel
#print axioms arc14_checked
@[expose] def arc15 : ArcCertificate := ⟨⟨24, 125, 93, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc15_checked : checkArc arc15 = true := by decide +kernel
#print axioms arc15_checked
@[expose] def arc16 : ArcCertificate := ⟨⟨32, 120, 96, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc16_checked : checkArc arc16 = true := by decide +kernel
#print axioms arc16_checked
@[expose] def arc17 : ArcCertificate := ⟨⟨33, 121, 96, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc17_checked : checkArc arc17 = true := by decide +kernel
#print axioms arc17_checked
@[expose] def arc18 : ArcCertificate := ⟨⟨34, 125, 96, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc18_checked : checkArc arc18 = true := by decide +kernel
#print axioms arc18_checked
@[expose] def arc19 : ArcCertificate := ⟨⟨46, 120, 101, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc19_checked : checkArc arc19 = true := by decide +kernel
#print axioms arc19_checked
@[expose] def arc20 : ArcCertificate := ⟨⟨47, 148, 99, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc20_checked : checkArc arc20 = true := by decide +kernel
#print axioms arc20_checked
@[expose] def arc21 : ArcCertificate := ⟨⟨48, 121, 101, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc21_checked : checkArc arc21 = true := by decide +kernel
#print axioms arc21_checked
@[expose] def arc22 : ArcCertificate := ⟨⟨49, 149, 99, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc22_checked : checkArc arc22 = true := by decide +kernel
#print axioms arc22_checked
@[expose] def arc23 : ArcCertificate := ⟨⟨51, 125, 101, 154⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 4, 2⟩, ⟨1, 5, 2⟩, ⟨2, 1, 0⟩, ⟨2, 4, 2⟩, ⟨2, 4, 3⟩, ⟨2, 5, 2⟩, ⟨2, 5, 3⟩, ⟨3, 1, 0⟩, ⟨3, 1, 3⟩], 3, 1⟩
theorem arc23_checked : checkArc arc23 = true := by decide +kernel
#print axioms arc23_checked
@[expose] def arc24 : ArcCertificate := ⟨⟨54, 148, 102, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc24_checked : checkArc arc24 = true := by decide +kernel
#print axioms arc24_checked
@[expose] def arc25 : ArcCertificate := ⟨⟨56, 149, 102, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc25_checked : checkArc arc25 = true := by decide +kernel
#print axioms arc25_checked
@[expose] def arc26 : ArcCertificate := ⟨⟨57, 150, 102, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc26_checked : checkArc arc26 = true := by decide +kernel
#print axioms arc26_checked
@[expose] def arc27 : ArcCertificate := ⟨⟨59, 151, 102, 153⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc27_checked : checkArc arc27 = true := by decide +kernel
#print axioms arc27_checked
@[expose] def arc28 : ArcCertificate := ⟨⟨65, 144, 106, 152⟩, [⟨1, 2, 1⟩, ⟨1, 3, 1⟩, ⟨1, 3, 2⟩], 1, 3⟩
theorem arc28_checked : checkArc arc28 = true := by decide +kernel
#print axioms arc28_checked
@[expose] def arcCertificates : List ArcCertificate := [arc0, arc1, arc2, arc3, arc4, arc5, arc6, arc7, arc8, arc9, arc10, arc11, arc12, arc13, arc14, arc15, arc16, arc17, arc18, arc19, arc20, arc21, arc22, arc23, arc24, arc25, arc26, arc27, arc28]
theorem all_arcs_checked (c : ArcCertificate) (hc : c ∈ arcCertificates) : checkArc c = true := by
  simp only [arcCertificates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact arc0_checked
  · exact arc1_checked
  · exact arc2_checked
  · exact arc3_checked
  · exact arc4_checked
  · exact arc5_checked
  · exact arc6_checked
  · exact arc7_checked
  · exact arc8_checked
  · exact arc9_checked
  · exact arc10_checked
  · exact arc11_checked
  · exact arc12_checked
  · exact arc13_checked
  · exact arc14_checked
  · exact arc15_checked
  · exact arc16_checked
  · exact arc17_checked
  · exact arc18_checked
  · exact arc19_checked
  · exact arc20_checked
  · exact arc21_checked
  · exact arc22_checked
  · exact arc23_checked
  · exact arc24_checked
  · exact arc25_checked
  · exact arc26_checked
  · exact arc27_checked
  · exact arc28_checked
end Wang156
