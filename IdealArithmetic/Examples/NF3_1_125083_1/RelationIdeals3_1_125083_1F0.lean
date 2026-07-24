import IdealArithmetic.Examples.NF3_1_125083_1.PrimesBelow3_1_125083_1F0
import IdealArithmetic.Examples.NF3_1_125083_1.ClassGroupData3_1_125083_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 8 ![![2, 0, 0], ![5, 1, 1]]
  ![3, 3, -1] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![16, 0, 0], ![40, 8, 8]]
    hsu := by decide
    w := ![![24, 24, -8], ![-64, 16, 0]]
    hw := by decide
    g := ![![![-2, -32, -16], ![-1, 127, 0]], ![![-23, -129, -65], ![-18, 508, 0]]]
    h := ![![![-1, 1, -1], ![1, 0, 0]], ![![-4, 1, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {8} * I2N1 =  Ideal.span {B.equivFun.symm ![3, 3, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![4, 0, 1]]
  ![-19, -3, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![8, 0, 2]]
    hsu := by decide
    w := ![![-38, -6, -2], ![-70, -12, -4]]
    hw := by decide
    g := ![![![-2, 0, -22], ![1, 44, 0]], ![![9, -1, -28], ![1, 55, 0]]]
    h := ![![![-5, -1, 0], ![-1, 0, 0]], ![![-5, -2, 1], ![-5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![-19, -3, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 8 ![![3, 0, 0], ![-1, 1, 0]]
  ![-41, -1, 3] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![24, 0, 0], ![-8, 8, 0]]
    hsu := by decide
    w := ![![-328, -8, 24], ![128, -64, 8]]
    hw := by decide
    g := ![![![47, 8, 4], ![20, -9, 0]], ![![45, 4, 2], ![19, 6, 0]]]
    h := ![![![-28, 16, -1], ![-43, 6, 0]], ![![12, -9, 0], ![20, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {8} * I3N1 =  Ideal.span {B.equivFun.symm ![-41, -1, 3]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![0, 1, 0]]
  ![-75, -263, 73] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![20, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-300, -1052, 292], ![4960, -1112, -44]]
    hw := by decide
    g := ![![![-79271, -46469, -27124], ![-51250, 85309, 0]], ![![-68536, 36107, 16846], ![-25237, -85323, 0]]]
    h := ![![![-15, -51, 0], ![-8, 73, 0]], ![![248, -54, 0], ![-8, -11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![-75, -263, 73]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4 ![![5, 0, 0], ![2, -1, 1]]
  ![-37657, -5969, -2081] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![20, 0, 0], ![8, -4, 4]]
    hsu := by decide
    w := ![![-150628, -23876, -8324], ![-220984, -35028, -12212]]
    hw := by decide
    g := ![![![93, -610, -318], ![-101, 1264, 0]], ![![2, -255, -108], ![-61, 474, 0]]]
    h := ![![![-6611, -1654, 44], ![-2301, 0, 0]], ![![-9698, -2427, 65], ![-3378, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4} * I5N1 =  Ideal.span {B.equivFun.symm ![-37657, -5969, -2081]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![0, 1, 0]]
  ![-14567, -2309, -805] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-29134, -4618, -1610], ![-56350, -8932, -3114]]
    hw := by decide
    g := ![![![14, -30, 7], ![-13, 3, 0]], ![![85, -6, -4], ![-1, 0, 0]]]
    h := ![![![-2081, -324, 0], ![-41, -805, 0]], ![![-4025, -626, 0], ![-84, -1557, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-14567, -2309, -805]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0], ![-1, 1, 0]]
  ![-271, -43, -15] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![28, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-1084, -172, -60], ![-1592, -252, -88]]
    hw := by decide
    g := ![![![77, -690, -361], ![-133, 1443, 0]], ![![1, -51, -28], ![-10, 111, 0]]]
    h := ![![![-84, 40, -3], ![-317, 6, 0]], ![![-124, 60, -5], ![-470, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![-271, -43, -15]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E13RS1 : RelationCertificate Table 4 ![![13, 0, 0], ![-5, 1, 0]]
  ![8523, 1351, 471] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![52, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![34092, 5404, 1884], ![50016, 7928, 2764]]
    hw := by decide
    g := ![![![-30781493, 307814559, 161602650], ![61562898, -646410581, 0]], ![![14206845, -142068124, -74585763], ![-28413605, 298343044, 0]]]
    h := ![![![192816, -42287, 828], ![499617, -10293, 0]], ![![282878, -62040, 1215], ![732982, -15104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {4} * I13N1 =  Ideal.span {B.equivFun.symm ![8523, 1351, 471]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 4 ![![13, 0, 0], ![-2, 1, 0]]
  ![-19, 1, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![52, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![-76, 4, 4], ![32, -24, 4]]
    hw := by decide
    g := ![![![-15687, 156601, 82215], ![31310, -328867, 0]], ![![3616, -36208, -19009], ![-7241, 76035, 0]]]
    h := ![![![-151, 77, -1], ![-972, 14, 0]], ![![68, -34, 0], ![438, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {4} * I13N2 =  Ideal.span {B.equivFun.symm ![-19, 1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 8 ![![17, 0, 0], ![5, 1, 0]]
  ![1014533, 160813, 56065] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![136, 0, 0], ![40, 8, 0]]
    hsu := by decide
    w := ![![8116264, 1286504, 448520], ![5953616, 943704, 329008]]
    hw := by decide
    g := ![![![-1195, 32491, 16391], ![3771, -131285, 0]], ![![-471, 10998, 5562], ![1264, -44485, 0]]]
    h := ![![![1684994, 366873, 9768], ![-5526073, -109991, 0]], ![![1236006, 269114, 7165], ![-4053580, -80679, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {8} * I17N1 =  Ideal.span {B.equivFun.symm ![1014533, 160813, 56065]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-6, 1, 0]]
  ![-11, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-22, -2, 2], ![70, -18, 0]]
    hw := by decide
    g := ![![![81, 10, -24], ![6, 57, 0]], ![![-9, -2, 10], ![1, -21, 0]]]
    h := ![![![-131, 28, -1], ![-413, 20, 0]], ![![431, -72, 0], ![1359, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-11, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 8 ![![23, 0, 0], ![9, 1, 0]]
  ![-313073, -49625, -17301] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![184, 0, 0], ![72, 8, 0]]
    hsu := by decide
    w := ![![-2504584, -397000, -138408], ![-1837216, -291216, -101528]]
    hw := by decide
    g := ![![![11281171973, -383559855675, -194600220886], ![-45124688966, 1556801767215, 0]], ![![3923885977, -133412125069, -67687034029], ![-15695544135, 541496272290, 0]]]
    h := ![![![-10412746, -1480337, -36610], ![26575565, 824729, 0]], ![![-7638190, -1085890, -26855], ![19494302, 604974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {8} * I23N1 =  Ideal.span {B.equivFun.symm ![-313073, -49625, -17301]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 8 ![![31, 0, 0], ![10, 1, 0]]
  ![4687, 743, 259] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![248, 0, 0], ![80, 8, 0]]
    hsu := by decide
    w := ![![37496, 5944, 2072], ![27504, 4360, 1520]]
    hw := by decide
    g := ![![![-741, 25854, 13126], ![3051, -104993, 0]], ![![-306, 10733, 5448], ![1269, -43582, 0]]]
    h := ![![![176307, 21116, 356], ![-546083, -10777, 0]], ![![129318, 15487, 261], ![-400542, -7901, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {8} * I31N0 =  Ideal.span {B.equivFun.symm ![4687, 743, 259]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![-8, 1, 0]]
  ![-153, -3, 11] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![62, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![-306, -6, 22], ![770, -230, 8]]
    hw := by decide
    g := ![![![-11337, -1438, -673], ![-718, 93, 0]], ![![1511, 191, 97], ![97, -27, 0]]]
    h := ![![![-215, 29, 0], ![-814, 11, 0]], ![![591, -75, 0], ![2242, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![-153, -3, 11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
