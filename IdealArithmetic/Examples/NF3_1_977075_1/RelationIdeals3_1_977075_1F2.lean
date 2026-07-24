import IdealArithmetic.Examples.NF3_1_977075_1.PrimesBelow3_1_977075_1F2
import IdealArithmetic.Examples.NF3_1_977075_1.ClassGroupData3_1_977075_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 128 ![![83, 0, 0], ![0, 1, 0]]
  ![83, -61, -7] ![![128, 0, 0], ![-28, 1, 0]] where
    su := ![![10624, 0, 0], ![0, 128, 0]]
    hsu := by decide
    w := ![![10624, -7808, -896], ![0, 1280, 128]]
    hw := by decide
    g := ![![![429, 246302, -8797], ![1952, 1126025, 0]], ![![-396, -246330, 8798], ![-1809, -1126145, 0]]]
    h := ![![![1, -1, 0], ![22, -7, 0]], ![![0, 0, 0], ![10, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {128} * I83N0 =  Ideal.span {B.equivFun.symm ![83, -61, -7]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 64 ![![83, 0, 0], ![12, 1, 0]]
  ![215, 71, 5] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![5312, 0, 0], ![768, 64, 0]]
    hsu := by decide
    w := ![![13760, 4544, 320], ![-7680, -1408, -64]]
    hw := by decide
    g := ![![![-902435, -157288223, 5618588], ![-2062756, -359589593, 0]], ![![-119580, -20845565, 744637], ![-273327, -47656767, 0]]]
    h := ![![![193, 16, 0], ![-1317, 5, 0]], ![![-144, -24, -1], ![986, 82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {64} * I83N1 =  Ideal.span {B.equivFun.symm ![215, 71, 5]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 32 ![![83, 0, 0], ![-13, 1, 0]]
  ![-21, -5, 1] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![2656, 0, 0], ![-416, 32, 0]]
    hsu := by decide
    w := ![![-672, -160, 32], ![-416, 32, 0]]
    hw := by decide
    g := ![![![-3056991, 794816644, 198895223], ![24455928, -6364647137, 0]], ![![516136, -134195750, -33581196], ![-4129087, 1074598272, 0]]]
    h := ![![![-103, 21, -1], ![-656, 84, 0]], ![![-65, 18, -1], ![-414, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {32} * I83N2 =  Ideal.span {B.equivFun.symm ![-21, -5, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-35, 1, 0]]
  ![-843, 271, -25] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![178, 0, 0], ![-70, 2, 0]]
    hsu := by decide
    w := ![![-1686, 542, -50], ![8300, -2668, 246]]
    hw := by decide
    g := ![![![-607, 17, -125], ![10, 267, 0]], ![![207, -7, 51], ![-3, -108, 0]]]
    h := ![![![-13617, 452, -2], ![-34602, 153, 0]], ![![67190, -2095, 6], ![170736, -411, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-843, 271, -25]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E103RS1 : RelationCertificate Table 8 ![![103, 0, 0], ![3, 1, 0]]
  ![509, -163, 15] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![824, 0, 0], ![24, 8, 0]]
    hsu := by decide
    w := ![![4072, -1304, 120], ![-2944, 952, -88]]
    hw := by decide
    g := ![![![13007, -260297, -65889], ![-26033, 527120, 0]], ![![807, -16269, -4118], ![-1621, 32945, 0]]]
    h := ![![![11255, 3751, 1], ![-386252, -88, 0]], ![![-8144, -2715, -1], ![279488, 92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {8} * I103N1 =  Ideal.span {B.equivFun.symm ![509, -163, 15]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 16 ![![109, 0, 0], ![29, 1, 0]]
  ![-5, -5, 1] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![1744, 0, 0], ![464, 16, 0]]
    hsu := by decide
    w := ![![-80, -80, 16], ![-352, 48, 0]]
    hw := by decide
    g := ![![![88409, -6011492, -1508398], ![-353607, 24134365, 0]], ![![24019, -1633180, -409796], ![-96066, 6556735, 0]]]
    h := ![![![-1354, -76, -1], ![5089, 110, 0]], ![![-5830, -230, -1], ![21912, 109, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {16} * I109N0 =  Ideal.span {B.equivFun.symm ![-5, -5, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 8 ![![109, 0, 0], ![39, 1, 0]]
  ![43, -13, 1] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![872, 0, 0], ![312, 8, 0]]
    hsu := by decide
    w := ![![344, -104, 8], ![-160, 64, -8]]
    hw := by decide
    g := ![![![-163327049, 3266540327, 826843020], ![326654022, -6614744155, 0]], ![![-56939939, 1138798455, 288258359], ![113879847, -2306066870, 0]]]
    h := ![![![175, 4, 0], ![-488, 1, 0]], ![![-134, -42, -1], ![374, 108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {8} * I109N1 =  Ideal.span {B.equivFun.symm ![43, -13, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 4 ![![109, 0, 0], ![40, 1, 0]]
  ![287, 39, 1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![436, 0, 0], ![160, 4, 0]]
    hsu := by decide
    w := ![![1148, 156, 4], ![-332, 360, 40]]
    hw := by decide
    g := ![![![2530, -766, -27], ![-189, 408, 0]], ![![700, -212, -17], ![-52, 151, 0]]]
    h := ![![![2523, 63, 0], ![-6868, 1, 0]], ![![-767, -22, 0], ![2088, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {4} * I109N2 =  Ideal.span {B.equivFun.symm ![287, 39, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS2 


noncomputable def E127RS1 : RelationCertificate Table 8 ![![127, 0, 0], ![-22, 1, 0]]
  ![-337, 15, 5] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![1016, 0, 0], ![-176, 8, 0]]
    hsu := by decide
    w := ![![-2696, 120, 40], ![-3008, 88, 40]]
    hw := by decide
    g := ![![![170857, -3418488, -865315], ![-341881, 6922500, 0]], ![![-28674, 573757, 145235], ![57390, -1161875, 0]]]
    h := ![![![-3611, 187, -1], ![-20830, 132, 0]], ![![-4052, 207, -1], ![-23374, 132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {8} * I127N1 =  Ideal.span {B.equivFun.symm ![-337, 15, 5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E127RS1 
