import IdealArithmetic.Examples.NF3_3_219961_2.PrimesBelow3_3_219961_2F0
import IdealArithmetic.Examples.NF3_3_219961_2.ClassGroupData3_3_219961_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![-26, 0, 1]]
  ![-2, 1, 1] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![4, 0, 0], ![-52, 0, 2]]
    hsu := by decide
    w := ![![-4, 2, 2], ![12, 14, 8]]
    hw := by decide
    g := ![![![15, 10, 5], ![-39, -3, 0]], ![![-11, -126, -64], ![448, 39, 0]]]
    h := ![![![6, 20, 9], ![-17, -3, 0]], ![![13, 140, 63], ![-122, -21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-2, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-25, -1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![2, 0, 0], ![-25, -1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-25, -1, 1]]
    hw := by decide
    g := ![![![3, 7, 2], ![-12, -2, 0]], ![![1, -83, -25], ![147, 24, 0]]]
    h := ![![![3, 7, 2], ![-12, -2, 0]], ![![1, -83, -25], ![147, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![32, 11, 3] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![64, 22, 6], ![302, 108, 30]]
    hw := by decide
    g := ![![![33, 72, 21], ![-124, -21, 0]], ![![21, 57, 12], ![-89, -14, 0]]]
    h := ![![![3797, 227, 33], ![2014, 0, -63]], ![![17542, 1052, 153], ![9299, 0, -291]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![32, 11, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS2 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![2, 1, 0]]
  ![134, 47, 13] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![28, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![536, 188, 52], ![1324, 464, 128]]
    hw := by decide
    g := ![![![29, 7, 3], ![-55, -4, 0]], ![![19, 10, 1], ![-14, -5, 0]]]
    h := ![![![566, 335, 75], ![-1914, -128, 0]], ![![1403, 835, 192], ![-4745, -328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![134, 47, 13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![2, 1, 0]]
  ![-46, -7, 3] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![44, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![-184, -28, 12], ![-484, -48, 24]]
    hw := by decide
    g := ![![![2212, 4328, 1186], ![-14543, -2450, 0]], ![![792, 1547, 424], ![-5194, -875, 0]]]
    h := ![![![0, -292, -391], ![-23, 1076, 0]], ![![1, -774, -1038], ![-66, 2856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![-46, -7, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![3, 1, 0]]
  ![-6, -3, -1] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![44, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![-24, -12, -4], ![-116, -32, -8]]
    hw := by decide
    g := ![![![-9, -31, -9], ![105, 18, 0]], ![![10, -12, -4], ![45, 7, 0]]]
    h := ![![![-6, -5, -3], ![20, 8, 0]], ![![-31, -12, -2], ![104, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![-6, -3, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 4 ![![11, 0, 0], ![5, 1, 0]]
  ![-742, -27, 23] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![44, 0, 0], ![20, 4, 0]]
    hsu := by decide
    w := ![![-2968, -108, 92], ![10076, 368, -312]]
    hw := by decide
    g := ![![![-31, -64, -19], ![221, 38, 0]], ![![-13, -34, -9], ![115, 19, 0]]]
    h := ![![![188, -7207, -4835], ![-562, 13302, 0]], ![![-651, 24464, 16414], ![1936, -45158, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {4} * I11N2 =  Ideal.span {B.equivFun.symm ![-742, -27, 23]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS2 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![0, 1, 0]]
  ![3648, 133, -113] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![38, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![7296, 266, -226], ![-49514, -1806, 1534]]
    hw := by decide
    g := ![![![2, 9, 5], ![-1, 0, 0]], ![![14, 20, 6], ![-20, -3, 0]]]
    h := ![![![192, 36, 113], ![14, -565, 0]], ![![-1303, -249, -767], ![-7, 3835, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![3648, 133, -113]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![6, 1, 0]]
  ![116, 9, -5] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![38, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![232, 18, -10], ![-582, 6, 10]]
    hw := by decide
    g := ![![![521, 4671, 1374], ![-8161, -1350, 0]], ![![227, 1803, 527], ![-3168, -525, 0]]]
    h := ![![![668, 134, 13], ![-2096, -63, 0]], ![![-1683, -343, -37], ![5281, 177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![116, 9, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![-7, 1, 0]]
  ![-32, -1, 1] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![38, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![-64, -2, 2], ![458, 18, -14]]
    hw := by decide
    g := ![![![-503, -4690, -1384], ![8167, 1350, 0]], ![![155, 1303, 384], ![-2267, -375, 0]]]
    h := ![![![-446, 71, -5], ![-1206, 24, 0]], ![![3235, -489, 19], ![8748, -92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![-32, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![7, 1, 0]]
  ![224, 29, -13] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![46, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![448, 58, -26], ![1278, 166, -74]]
    hw := by decide
    g := ![![![-623, -5694, -1674], ![9869, 1638, 0]], ![![-224, -2213, -653], ![3851, 637, 0]]]
    h := ![![![630, 93, 1], ![-2038, -9, 0]], ![![1807, 279, 9], ![-5846, -61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![224, 29, -13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-5, 1, 0]]
  ![92, 3, -3] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![46, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![184, 6, -6], ![-1274, -50, 38]]
    hw := by decide
    g := ![![![1128, 10132, 2981], ![-17625, -2912, 0]], ![![-170, -1588, -465], ![2759, 455, 0]]]
    h := ![![![764, -155, 3], ![3496, -18, 0]], ![![-5254, 1076, -31], ![-24041, 183, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![92, 3, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 2 ![![23, 0, 0], ![-3, 1, 0]]
  ![-220, -29, 13] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![46, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-440, -58, 26], ![-1378, -170, 78]]
    hw := by decide
    g := ![![![1056, 9497, 2801], ![-16517, -2730, 0]], ![![-99, -944, -278], ![1651, 273, 0]]]
    h := ![![![-344, 111, -1], ![-2564, 9, 0]], ![![-1093, 353, -3], ![-8150, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {2} * I23N2 =  Ideal.span {B.equivFun.symm ![-220, -29, 13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 


noncomputable def E31RS0 : RelationCertificate Table 4 ![![31, 0, 0], ![14, 1, 0]]
  ![-54, -7, 3] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![124, 0, 0], ![56, 4, 0]]
    hsu := by decide
    w := ![![-216, -28, 12], ![-284, -40, 16]]
    hw := by decide
    g := ![![![110, 174, 46], ![-569, -98, 0]], ![![55, 80, 21], ![-262, -45, 0]]]
    h := ![![![-1250, -131, -11], ![2764, 86, 0]], ![![-1615, -176, -16], ![3571, 125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {4} * I31N0 =  Ideal.span {B.equivFun.symm ![-54, -7, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-9, 1, 0]]
  ![-66, -5, 1] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![124, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![-264, -20, 4], ![700, 0, -32]]
    hw := by decide
    g := ![![![-5331, -10502, -2873], ![35285, 5940, 0]], ![![1343, 2630, 717], ![-8827, -1485, 0]]]
    h := ![![![-156, 19, -1], ![-530, 8, 0]], ![![442, -49, 0], ![1503, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-66, -5, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 4 ![![31, 0, 0], ![-6, 1, 0]]
  ![-674, -25, 21] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![124, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-2696, -100, 84], ![9060, 328, -280]]
    hw := by decide
    g := ![![![-2, -12, -4], ![27, 4, 0]], ![![22, -2, -2], ![10, 1, 0]]]
    h := ![![![-16298, 2779, -53], ![-84094, 416, 0]], ![![54813, -9336, 170], ![282823, -1335, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {4} * I31N2 =  Ideal.span {B.equivFun.symm ![-674, -25, 21]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS2 
