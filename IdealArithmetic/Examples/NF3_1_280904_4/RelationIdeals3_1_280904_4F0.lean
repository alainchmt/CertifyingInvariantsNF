import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F0
import IdealArithmetic.Examples.NF3_1_280904_4.ClassGroupData3_1_280904_4

set_option linter.all false

noncomputable section


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![3, 2, 1]]
  ![-73, -2, 6] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![343, 0, 0], ![147, 98, 49]]
    hsu := by decide
    w := ![![-3577, -98, 294], ![-1764, -147, 98]]
    hw := by decide
    g := ![![![-1211911180, -23998777848, -3002106152], ![-885497054, 73551600725, 0]], ![![-511695871, -10132817923, -1267556007], ![-373876529, 31055122172, 0]]]
    h := ![![![-10, 0, 1], ![-1, 0, 0]], ![![-6, -1, 0], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![-73, -2, 6]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![7, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![-13, -31, -32], ![-7, 112, 0]], ![![-4, -8, -8], ![1, 28, 0]]]
    h := ![![![-13, -31, -32], ![-7, 112, 0]], ![![-4, -8, -8], ![1, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 49 ![![13, 0, 0], ![-5, 1, 0]]
  ![-23158, -10611, -2516] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![637, 0, 0], ![-245, 49, 0]]
    hsu := by decide
    w := ![![-1134742, -519939, -123284], ![-132055, -175322, -63994]]
    hw := by decide
    g := ![![![-1742970, 3222944, 266366], ![-503317, -8953826, 0]], ![![1391777, -981269, -19282], ![434440, 2308652, 0]]]
    h := ![![![22491, -161012, 64532], ![-21035, -420716, 0]], ![![2081, -15350, 5990], ![-1968, -39588, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {49} * I13N0 =  Ideal.span {B.equivFun.symm ![-23158, -10611, -2516]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 49 ![![13, 0, 0], ![-4, 1, 0]]
  ![1283, 62, -88] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![637, 0, 0], ![-196, 49, 0]]
    hsu := by decide
    w := ![![62867, 3038, -4312], ![29302, 2891, -1372]]
    hw := by decide
    g := ![![![81006, 1577345, 197414], ![58657, -4834915, 0]], ![![-23534, -447678, -56068], ![-16803, 1372492, 0]]]
    h := ![![![-391, 2312, -1172], ![302, 7574, 0]], ![![-176, 1061, -536], ![146, 3470, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {49} * I13N1 =  Ideal.span {B.equivFun.symm ![1283, 62, -88]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E23RS1 : RelationCertificate Table 49 ![![23, 0, 0], ![2, 1, 0]]
  ![106, 17, -2] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![1127, 0, 0], ![98, 49, 0]]
    hsu := by decide
    w := ![![5194, 833, -98], ![1911, 392, 0]]
    hw := by decide
    g := ![![![160, 3321, 416], ![168, -10184, 0]], ![![23, 496, 62], ![22, -1520, 0]]]
    h := ![![![-373, -761, -764], ![-50, 8785, 0]], ![![-137, -279, -280], ![-15, 3220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {49} * I23N1 =  Ideal.span {B.equivFun.symm ![106, 17, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 7 ![![23, 0, 0], ![-4, 1, 0]]
  ![3754, -519, 178] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![161, 0, 0], ![-28, 7, 0]]
    hsu := by decide
    w := ![![26278, -3633, 1246], ![-10633, 1470, -504]]
    hw := by decide
    g := ![![![-1, 13, 18], ![6, -69, 0]], ![![6, -3, -4], ![3, 13, 0]]]
    h := ![![![-28807, 122607, -61532], ![10348, 707707, 0]], ![![11660, -49612, 24898], ![-4166, -286363, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {7} * I23N2 =  Ideal.span {B.equivFun.symm ![3754, -519, 178]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 49 ![![29, 0, 0], ![-14, 1, 0]]
  ![113175975, -15647910, 5366054] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![1421, 0, 0], ![-686, 49, 0]]
    hsu := by decide
    w := ![![5545622775, -766747590, 262936646], ![1263928344, -174752963, 59927098]]
    hw := by decide
    g := ![![![579, -71, -10], ![233, 784, 0]], ![![-362, 14, 14], ![-77, -264, 0]]]
    h := ![![![-7329930933, 164642126982, -23565594434], ![9215902092, 341703802320, 0]], ![![-1670598208, 37524342955, -5370942806], ![2100438550, 77879282188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {49} * I29N1 =  Ideal.span {B.equivFun.symm ![113175975, -15647910, 5366054]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 49 ![![31, 0, 0], ![12, 1, 0]]
  ![-113639, 15712, -5388] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![1519, 0, 0], ![588, 49, 0]]
    hsu := by decide
    w := ![![-5568311, 769888, -264012], ![-1269100, 175469, -60172]]
    hw := by decide
    g := ![![![27, 618, 76], ![38, -1908, 0]], ![![18, 263, 32], ![14, -810, 0]]]
    h := ![![![32416, 577443, 96150], ![31207, -1493019, 0]], ![![7379, 131607, 21914], ![7136, -340281, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {49} * I31N1 =  Ideal.span {B.equivFun.symm ![-113639, 15712, -5388]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 7 ![![31, 0, 0], ![15, 1, 0]]
  ![212, -29, 10] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![217, 0, 0], ![105, 7, 0]]
    hsu := by decide
    w := ![![1484, -203, 70], ![-595, 84, -28]]
    hw := by decide
    g := ![![![10, 11, 12], ![12, -44, 0]], ![![7, 6, 6], ![5, -22, 0]]]
    h := ![![![-25495, -614672, -82094], ![-32127, 1272462, 0]], ![![10212, 246485, 32920], ![12907, -510262, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {7} * I31N2 =  Ideal.span {B.equivFun.symm ![212, -29, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS2 
