import IdealArithmetic.Examples.NF3_1_126635_1.PrimesBelow3_1_126635_1F2
import IdealArithmetic.Examples.NF3_1_126635_1.ClassGroupData3_1_126635_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 64 ![![83, 0, 0], ![-36, 1, 0]]
  ![31, -40, -17] ![![64, 0, 0], ![8, 1, 0]] where
    su := ![![5312, 0, 0], ![-2304, 64, 0]]
    hsu := by decide
    w := ![![1984, -2560, -1088], ![1472, -448, -256]]
    hw := by decide
    g := ![![![-7, 5977, 1994], ![108, -42525, 0]], ![![-1, -2518, -840], ![-19, 17913, 0]]]
    h := ![![![533, -6, -1], ![1228, 22, 0]], ![![421, 11, -2], ![970, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {64} * I83N0 =  Ideal.span {B.equivFun.symm ![31, -40, -17]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 8 ![![83, 0, 0], ![-25, 1, 0]]
  ![-79, 16, -7] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![664, 0, 0], ![-200, 8, 0]]
    hsu := by decide
    w := ![![-632, 128, -56], ![504, -112, 48]]
    hw := by decide
    g := ![![![-14, -39868, -121466], ![-4977, 323910, 0]], ![![4, 1446936, 4408633], ![180869, -11756355, 0]]]
    h := ![![![-7163, 302, -2], ![-23778, 53, 0]], ![![5761, -230, 0], ![19124, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {8} * I83N1 =  Ideal.span {B.equivFun.symm ![-79, 16, -7]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 256 ![![83, 0, 0], ![-23, 1, 0]]
  ![587, -8, -37] ![![256, 0, 0], ![-56, 1, 0]] where
    su := ![![21248, 0, 0], ![-5888, 256, 0]]
    hsu := by decide
    w := ![![150272, -2048, -9472], ![-30208, 768, 2048]]
    hw := by decide
    g := ![![![3568863, 4376437554, -238718252], ![16314811, 20370624155, 0]], ![![-761409, -933717919, 50930810], ![-3480730, -4346095781, 0]]]
    h := ![![![313, 95280, -12995], ![1104, 359516, 0]], ![![-38, -19167, 2614], ![-132, -72318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {256} * I83N2 =  Ideal.span {B.equivFun.symm ![587, -8, -37]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 65536 ![![89, 0, 0], ![-2, 1, 0]]
  ![-11603, 2760, 1693] ![![65536, 0, 0], ![-1592, 1, 0]] where
    su := ![![5832704, 0, 0], ![-131072, 65536, 0]]
    hsu := by decide
    w := ![![-760414208, 180879360, 110952448], ![18350080, -4390912, -2686976]]
    hw := by decide
    g := ![![![-15449022483, -41703646253754827, 78636668001494], ![-635971820002, -1717844224715303685, 0]], ![![247181670, 667247723932847, -1258166670185], ![10175438395, 27485070299081395, 0]]]
    h := ![![![-131, -5736, 17321], ![-28, -513292, 0]], ![![4, 138, -418], ![38, 12387, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {65536} * I89N1 =  Ideal.span {B.equivFun.symm ![-11603, 2760, 1693]} * (J0 ^ 16) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_16 E89RS1 
