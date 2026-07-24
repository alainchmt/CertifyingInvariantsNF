import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F0
import IdealArithmetic.Examples.NF3_1_491724_2.ClassGroupData3_1_491724_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 7 ![![2, 0, 0], ![0, 1, 0]]
  ![-1238, -1, 6] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![14, 0, 0], ![0, 7, 0]]
    hsu := by decide
    w := ![![-8666, -7, 42], ![5810, -301, -7]]
    hw := by decide
    g := ![![![-1923, -563, -37], ![199, 0, 0]], ![![-13896, -4063, -267], ![1407, -2, 0]]]
    h := ![![![-619, -2, 2], ![3, 2, 0]], ![![415, -18, 0], ![-7, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {7} * I2N0 =  Ideal.span {B.equivFun.symm ![-1238, -1, 6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 7 ![![3, 0, 0], ![0, 1, 0]]
  ![687, 188, 13] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![21, 0, 0], ![0, 7, 0]]
    hsu := by decide
    w := ![![4809, 1316, 91], ![9219, 2527, 175]]
    hw := by decide
    g := ![![![-95, -10, 1], ![16, 0, 0]], ![![250, 17, 4], ![-28, -46, 0]]]
    h := ![![![229, 56, 0], ![20, 13, 0]], ![![439, 108, 0], ![37, 25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {7} * I3N0 =  Ideal.span {B.equivFun.symm ![687, 188, 13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-106, -6, 1]]
  ![4439, 314, -43] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![343, 0, 0], ![-5194, -294, 49]]
    hsu := by decide
    w := ![![217511, 15386, -2107], ![24941, 1813, -245]]
    hw := by decide
    g := ![![![-15, -118, -9], ![44, 438, 0]], ![![-18, 1702, 131], ![40, -6426, 0]]]
    h := ![![![89, 14, -1], ![-36, 0, 0]], ![![103, 7, -1], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![4439, 314, -43]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![7, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![4, -3, 0], ![21, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, -3, 0], ![21, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E13RS1 : RelationCertificate Table 49 ![![13, 0, 0], ![-5, 1, 0]]
  ![5269, 1444, 100] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![637, 0, 0], ![-245, 49, 0]]
    hsu := by decide
    w := ![![258181, 70756, 4900], ![144697, 39641, 2744]]
    hw := by decide
    g := ![![![66, 585, 44], ![67, -2192, 0]], ![![-79, -221, -16], ![14, 816, 0]]]
    h := ![![![1591483, -350956, 6578], ![4136802, -85414, 0]], ![![891951, -196691, 3686], ![2318482, -47862, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {49} * I13N1 =  Ideal.span {B.equivFun.symm ![5269, 1444, 100]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 7 ![![13, 0, 0], ![-2, 1, 0]]
  ![110335, 30225, 2092] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![91, 0, 0], ![-14, 7, 0]]
    hsu := by decide
    w := ![![772345, 211575, 14644], ![1483769, 406462, 28133]]
    hw := by decide
    g := ![![![-3103, -265, 35], ![412, -42, 0]], ![![2147, 175, -20], ![-275, 1, 0]]]
    h := ![![![1640921, -830526, 8478], ![10610819, -108122, 0]], ![![3152409, -1595545, 16289], ![20384675, -207738, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {7} * I13N2 =  Ideal.span {B.equivFun.symm ![110335, 30225, 2092]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 7 ![![19, 0, 0], ![-6, 1, 0]]
  ![-509, -37, 5] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![133, 0, 0], ![-42, 7, 0]]
    hsu := by decide
    w := ![![-3563, -259, 35], ![4319, 308, -42]]
    hw := by decide
    g := ![![![18, 16, -12], ![5, 86, 0]], ![![6, -2, 4], ![0, -27, 0]]]
    h := ![![![-22751, 4105, -53], ![-71960, 1012, 0]], ![![27599, -4972, 63], ![87294, -1203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {7} * I19N1 =  Ideal.span {B.equivFun.symm ![-509, -37, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS0 : RelationCertificate Table 49 ![![29, 0, 0], ![9, 1, 0]]
  ![-51517, -3167, 466] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![1421, 0, 0], ![441, 49, 0]]
    hsu := by decide
    w := ![![-2524333, -155183, 22834], ![-314629, -19992, 2891]]
    hw := by decide
    g := ![![![-51345, 10800501, 831125], ![206818, -40721850, 0]], ![![-16861, 3859068, 296962], ![74296, -14548490, 0]]]
    h := ![![![-156866, -19367, -209], ![499733, 6527, 0]], ![![-19568, -2416, -26], ![62339, 813, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {49} * I29N0 =  Ideal.span {B.equivFun.symm ![-51517, -3167, 466]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 49 ![![29, 0, 0], ![11, 1, 0]]
  ![-221357, -60638, -4197] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![1421, 0, 0], ![539, 49, 0]]
    hsu := by decide
    w := ![![-10846493, -2971262, -205653], ![-6075755, -1664383, -115199]]
    hw := by decide
    g := ![![![7624417105338, -1507288612199081, -115990392755591], ![-28738187547499, 5683529245023520, 0]], ![![2848201791965, -563067585009380, -43329744419610], ![-10735529830854, 2123157476560837, 0]]]
    h := ![![![-558821, -59616, -819], ![1453132, 19554, 0]], ![![-313029, -33397, -459], ![813986, 10960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {49} * I29N1 =  Ideal.span {B.equivFun.symm ![-221357, -60638, -4197]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 7 ![![31, 0, 0], ![-11, 1, 0]]
  ![55, 15, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![217, 0, 0], ![-77, 7, 0]]
    hsu := by decide
    w := ![![385, 105, 7], ![707, 196, 14]]
    hw := by decide
    g := ![![![-261, -11043, 11262], ![-1540, -78832, 0]], ![![73, 2548, -2599], ![360, 18192, 0]]]
    h := ![![![5082, -494, 3], ![14317, -92, 0]], ![![9316, -911, 6], ![26245, -184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {7} * I31N1 =  Ideal.span {B.equivFun.symm ![55, 15, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
