import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F2
import IdealArithmetic.Examples.NF3_1_410700_2.ClassGroupData3_1_410700_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 54 ![![83, 0, 0], ![25, 1, 0]]
  ![-15, -3, 1] ![![54, 0, 0], ![27, 27, 0]] where
    su := ![![4482, 0, 0], ![1350, 54, 0]]
    hsu := by decide
    w := ![![-810, -162, 54], ![5022, 540, -216]]
    hw := by decide
    g := ![![![26907, -134445, -242000], ![-53767, 161334, 0]], ![![10464, -52284, -94111], ![-20909, 62741, 0]]]
    h := ![![![-55, -11, -1], ![182, 28, 0]], ![![221, -8, -2], ![-730, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {54} * I83N1 =  Ideal.span {B.equivFun.symm ![-15, -3, 1]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 81 ![![89, 0, 0], ![42, 1, 0]]
  ![-5, 2, 0] ![![81, 0, 0], ![-99, 16, 3]] where
    su := ![![7209, 0, 0], ![3402, 81, 0]]
    hsu := by decide
    w := ![![-405, 162, 0], ![1701, 0, 81]]
    hw := by decide
    g := ![![![32, -6, -1], ![31, 0, 0]], ![![66, -11, -2], ![56, 0, 0]]]
    h := ![![![-1, -3741, -261], ![2, 7743, 0]], ![![-105, 15592, 1088], ![223, -32277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {81} * I89N1 =  Ideal.span {B.equivFun.symm ![-5, 2, 0]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 162 ![![101, 0, 0], ![18, 1, 0]]
  ![-31, -1, 1] ![![162, 0, 0], ![-756, -54, 27]] where
    su := ![![16362, 0, 0], ![2916, 162, 0]]
    hsu := by decide
    w := ![![-5022, -162, 162], ![5346, 972, -324]]
    hw := by decide
    g := ![![![-3947873706, 1184309178, -373769459], ![17966346089, 2620621556, 0]], ![![-664609262, 199373870, -62922643], ![3024564876, 441171503, 0]]]
    h := ![![![7, -6808, -1075], ![-41, 36192, 0]], ![![-15, 7232, 1142], ![86, -38448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {162} * I101N1 =  Ideal.span {B.equivFun.symm ![-31, -1, 1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 54 ![![103, 0, 0], ![16, 1, 0]]
  ![-75, -7, 3] ![![54, 0, 0], ![-9, 9, 0]] where
    su := ![![5562, 0, 0], ![864, 54, 0]]
    hsu := by decide
    w := ![![-4050, -378, 162], ![6102, 432, -216]]
    hw := by decide
    g := ![![![120392516, 27659044, -85276888728204], ![-15455577, 170553776232840, -3670700]], ![![20247831, 4651748, -14342022195198], ![-2599347, 28684044184614, -617345]]]
    h := ![![![-52557, -3404, -21], ![338331, 722, 0]], ![![79159, 5095, 26], ![-509579, -894, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {54} * I103N0 =  Ideal.span {B.equivFun.symm ![-75, -7, 3]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 162 ![![103, 0, 0], ![24, 1, 0]]
  ![-23, -5, -1] ![![162, 0, 0], ![-756, -54, 27]] where
    su := ![![16686, 0, 0], ![3888, 162, 0]]
    hsu := by decide
    w := ![![-3726, -810, -162], ![2916, 162, -162]]
    hw := by decide
    g := ![![![-737, 228, -72], ![3419, 498, 0]], ![![-153, 56, -18], ![822, 119, 0]]]
    h := ![![![7, -13408, -1609], ![-31, 55242, 0]], ![![-42, 10515, 1262], ![181, -43329, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {162} * I103N1 =  Ideal.span {B.equivFun.symm ![-23, -5, -1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 162 ![![103, 0, 0], ![-41, 1, 0]]
  ![-25, -1, 1] ![![162, 0, 0], ![-756, -54, 27]] where
    su := ![![16686, 0, 0], ![-6642, 162, 0]]
    hsu := by decide
    w := ![![-4050, -162, 162], ![810, 648, -162]]
    hw := by decide
    g := ![![![-5881944, 1764514, -556883], ![26768206, 3904485, 0]], ![![1960667, -588170, 185627], ![-8922731, -1301495, 0]]]
    h := ![![![-171348, 4726, -41], ![-430459, 1408, 0]], ![![34122, -899, 5], ![85721, -172, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {162} * I103N2 =  Ideal.span {B.equivFun.symm ![-25, -1, 1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E103RS2 


noncomputable def E107RS1 : RelationCertificate Table 9 ![![107, 0, 0], ![-47, 1, 0]]
  ![-13, -2, 0] ![![9, 0, 0], ![-81, -5, 3]] where
    su := ![![963, 0, 0], ![-423, 9, 0]]
    hsu := by decide
    w := ![![-117, -18, 0], ![-153, -9, -9]]
    hw := by decide
    g := ![![![51, 4, -2], ![2, 0, 0]], ![![55, 3, -2], ![8, 0, 0]]]
    h := ![![![-236, 51, -3], ![-537, 107, 0]], ![![-258, 36, -2], ![-587, 71, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {9} * I107N1 =  Ideal.span {B.equivFun.symm ![-13, -2, 0]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 54 ![![113, 0, 0], ![53, 1, 0]]
  ![-69, -7, 3] ![![54, 0, 0], ![-402, -6, 15]] where
    su := ![![6102, 0, 0], ![2862, 54, 0]]
    hsu := by decide
    w := ![![-3726, -378, 162], ![0, 1242, -270]]
    hw := by decide
    g := ![![![-2600421778, -7776891546, -4416849611], ![18995892580, 2579360313, -113]], ![![-1219683939, -3647619720, -2071648762], ![8909702800, 1209805420, -53]]]
    h := ![![![42375, 745, -3], ![-90348, 114, 0]], ![![424, -9, -1], ![-904, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {54} * I113N1 =  Ideal.span {B.equivFun.symm ![-69, -7, 3]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 1458 ![![131, 0, 0], ![15, 1, 0]]
  ![333, -71, 12] ![![1458, 0, 0], ![-451, -1, 1]] where
    su := ![![190998, 0, 0], ![21870, 1458, 0]]
    hsu := by decide
    w := ![![485514, -103518, 17496], ![-167670, 29160, -4374]]
    hw := by decide
    g := ![![![-18098888478038, 40535617200854, 292031616626], ![5570888284492, 143784328444185, -18]], ![![-3015467793309, 6753666022919, 48655581017], ![928169387148, 23956002170386, -3]]]
    h := ![![![1218, 80, 0], ![-10615, 4, 0]], ![![-440, -45, -3], ![3835, 130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {1458} * I131N1 =  Ideal.span {B.equivFun.symm ![333, -71, 12]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 9 ![![137, 0, 0], ![13, 1, 0]]
  ![-28, -1, 1] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![1233, 0, 0], ![117, 9, 0]]
    hsu := by decide
    w := ![![-252, -9, 9], ![117, 9, 0]]
    hw := by decide
    g := ![![![7, -60, -46], ![5, 137, 0]], ![![-2, -6, -4], ![7, 12, 0]]]
    h := ![![![-3202, -251, -1], ![33742, 46, 0]], ![![1469, 113, 0], ![-15480, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {9} * I137N1 =  Ideal.span {B.equivFun.symm ![-28, -1, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E137RS1 
