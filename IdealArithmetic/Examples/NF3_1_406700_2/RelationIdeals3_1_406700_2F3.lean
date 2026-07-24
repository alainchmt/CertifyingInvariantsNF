import IdealArithmetic.Examples.NF3_1_406700_2.PrimesBelow3_1_406700_2F3
import IdealArithmetic.Examples.NF3_1_406700_2.ClassGroupData3_1_406700_2

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 247 ![![149, 0, 0], ![17, 1, 0]]
  ![-98, -48, -5] ![![247, 0, 0], ![-50, 1, 0]] where
    su := ![![36803, 0, 0], ![4199, 247, 0]]
    hsu := by decide
    w := ![![-24206, -11856, -1235], ![5187, 2470, 0]]
    hw := by decide
    g := ![![![585, -29833, 2925], ![-25, -144485, 0]], ![![118, -5508, 540], ![47, -26675, 0]]]
    h := ![![![2676318, 43912628, 13723955], ![600140, -408973860, 0]], ![![-573570, -9410977, -2941200], ![-128577, 87647760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {247} * I149N1 =  Ideal.span {B.equivFun.symm ![-98, -48, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 361 ![![157, 0, 0], ![19, 1, 0]]
  ![-435, 32, -22] ![![361, 0, 0], ![-126, 1, 0]] where
    su := ![![56677, 0, 0], ![6859, 361, 0]]
    hsu := by decide
    w := ![![-157035, 11552, -7942], ![56316, -3971, 2888]]
    hw := by decide
    g := ![![![-10463, 1706449, -67184], ![8521, 4850682, 0]], ![![-1208, 212010, -8347], ![1322, 602653, 0]]]
    h := ![![![13347, 247494, 68754], ![3314, -2158880, 0]], ![![-4800, -88755, -24656], ![-1076, 774200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {361} * I157N1 =  Ideal.span {B.equivFun.symm ![-435, 32, -22]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 247 ![![163, 0, 0], ![48, 1, 0]]
  ![276, -11, 4] ![![247, 0, 0], ![-50, 1, 0]] where
    su := ![![40261, 0, 0], ![11856, 247, 0]]
    hsu := by decide
    w := ![![68172, -2717, 988], ![-14079, 741, -247]]
    hw := by decide
    g := ![![![-4474, 250126, -24523], ![2124, 1211436, 0]], ![![-1361, 77109, -7560], ![745, 373464, 0]]]
    h := ![![![977239, 54541777, 5802723], ![622481, -189168769, 0]], ![![-201999, -11272509, -1199287], ![-128562, 39096756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {247} * I163N1 =  Ideal.span {B.equivFun.symm ![276, -11, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E163RS1 


noncomputable def E179RS1 : RelationCertificate Table 361 ![![179, 0, 0], ![68, 1, 0]]
  ![-154, -70, 3] ![![361, 0, 0], ![-126, 1, 0]] where
    su := ![![64619, 0, 0], ![24548, 361, 0]]
    hsu := by decide
    w := ![![-55594, -25270, 1083], ![19133, 8664, -722]]
    hw := by decide
    g := ![![![4551, -730566, 28763], ![-3456, -2076675, 0]], ![![1841, -286380, 11275], ![-1191, -814050, 0]]]
    h := ![![![2114, 192640, 14377], ![2002, -514696, 0]], ![![-791, -66300, -4948], ![-522, 177138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {361} * I179N1 =  Ideal.span {B.equivFun.symm ![-154, -70, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E179RS1 
