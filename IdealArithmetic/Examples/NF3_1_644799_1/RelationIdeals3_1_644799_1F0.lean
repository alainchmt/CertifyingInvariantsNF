import IdealArithmetic.Examples.NF3_1_644799_1.PrimesBelow3_1_644799_1F0
import IdealArithmetic.Examples.NF3_1_644799_1.ClassGroupData3_1_644799_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 3125 ![![3, 0, 0], ![0, 0, 1]]
  ![-84, 23, 29] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![9375, 0, 0], ![0, 0, 3125]]
    hsu := by decide
    w := ![![-262500, 71875, 90625], ![-4893750, -128125, 293750]]
    hw := by decide
    g := ![![![688, -965, -4], ![2809, 0, 0]], ![![-305, 206, -12], ![-541, 0, 0]]]
    h := ![![![76, 7, -24], ![95, 2, 0]], ![![154, -18, 130], ![-335, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3125} * I3N0 =  Ideal.span {B.equivFun.symm ![-84, 23, 29]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 25 ![![3, 0, 0], ![-1, 1, 0]]
  ![-11, -1, 0] ![![25, 0, 0], ![-12, 4, 1]] where
    su := ![![75, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![-275, -25, 0], ![300, -25, -50]]
    hw := by decide
    g := ![![![9, -2, 0], ![9, 0, 0]], ![![-13, 0, -2], ![14, 0, 0]]]
    h := ![![![-73418, -6876, 1036], ![22181, 0, -1554]], ![![87403, 8184, -1234], ![-26403, 0, 1850]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {25} * I3N1 =  Ideal.span {B.equivFun.symm ![-11, -1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 34375 ![![5, 0, 0], ![0, 1, 0]]
  ![-16667, 1946, -1234] ![![34375, 0, 0], ![-13312, 1079, 1]] where
    su := ![![171875, 0, 0], ![0, 34375, 0]]
    hsu := by decide
    w := ![![-572928125, 66893750, -42418750], ![423087500, -49396875, 31315625]]
    hw := by decide
    g := ![![![2920293, 14483915, -9082547], ![-651125, 32140540, 0]], ![![1543630, 7668150, -4808407], ![-350927, 17015580, 0]]]
    h := ![![![16667, 13195, -60248], ![2639, 33334, 0]], ![![-12308, -9745, 44491], ![-1944, -24616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {34375} * I5N0 =  Ideal.span {B.equivFun.symm ![-16667, 1946, -1234]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3125 ![![5, 0, 0], ![1, 1, 0]]
  ![19, 2, 1] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![15625, 0, 0], ![3125, 3125, 0]]
    hsu := by decide
    w := ![![59375, 6250, 3125], ![-190625, 15625, 21875]]
    hw := by decide
    g := ![![![7, -9, 0], ![26, 0, 0]], ![![784, -1042, -1], ![3018, 0, 0]]]
    h := ![![![-151482, -45249, 478064], ![-39344, -265591, 0]], ![![588107, 175673, -1856011], ![152758, 1031118, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3125} * I5N1 =  Ideal.span {B.equivFun.symm ![19, 2, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 275 ![![5, 0, 0], ![-2, 1, 0]]
  ![-20, 1, 2] ![![275, 0, 0], ![113, 4, 1]] where
    su := ![![1375, 0, 0], ![-550, 275, 0]]
    hsu := by decide
    w := ![![-5500, 275, 550], ![-3850, 0, 275]]
    hw := by decide
    g := ![![![404681, -299603, -109954], ![161676, 771171, 0]], ![![-111142, 82242, 30183], ![-44251, -211694, 0]]]
    h := ![![![32273, 45784, -101327], ![-3747, 56293, 0]], ![![22040, 31267, -69199], ![-2559, 38444, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {275} * I5N2 =  Ideal.span {B.equivFun.symm ![-20, 1, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 6875 ![![7, 0, 0], ![-1, 1, 1]]
  ![-1423, 163, -103] ![![6875, 0, 0], ![1688, 454, 1]] where
    su := ![![48125, 0, 0], ![-6875, 6875, 6875]]
    hsu := by decide
    w := ![![-9783125, 1120625, -708125], ![4654375, -563750, 350625]]
    hw := by decide
    g := ![![![1111720, -616733, -3148546], ![232696, 5293720, 0]], ![![-112121, 61418, 314854], ![-19404, -529372, 0]]]
    h := ![![![-199, 19, -19], ![30, 0, 0]], ![![95, -10, 9], ![-12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {6875} * I7N0 =  Ideal.span {B.equivFun.symm ![-1423, 163, -103]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 275 ![![7, 0, 0], ![2, 1, 0]]
  ![-47, 4, -3] ![![275, 0, 0], ![113, 4, 1]] where
    su := ![![1925, 0, 0], ![550, 275, 0]]
    hsu := by decide
    w := ![![-12925, 1100, -825], ![-3850, 275, -275]]
    hw := by decide
    g := ![![![-97, 21, 8], ![146, -60, 0]], ![![-112, 7, 3], ![231, -27, 0]]]
    h := ![![![-146445, 5858, 474459], ![-41002, -369024, 0]], ![![-43476, 1739, 140855], ![-12172, -109554, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {275} * I7N1 =  Ideal.span {B.equivFun.symm ![-47, 4, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 11 ![![11, 0, 0], ![1, -5, 1]]
  ![3041, -355, 225] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![121, 0, 0], ![11, -55, 11]]
    hsu := by decide
    w := ![![33451, -3905, 2475], ![-40117, 4686, -2970]]
    hw := by decide
    g := ![![![-48, -72, 162], ![5, -198, 0]], ![![-8, -8, 11], ![8, -15, 0]]]
    h := ![![![273, -15, 17], ![38, 0, 0]], ![![-328, 21, -21], ![-39, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {11} * I11N0 =  Ideal.span {B.equivFun.symm ![3041, -355, 225]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![11, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 625 ![![17, 0, 0], ![-3, 1, 0]]
  ![202, -3, -20] ![![625, 0, 0], ![-187, -171, 1]] where
    su := ![![10625, 0, 0], ![-1875, 625, 0]]
    hsu := by decide
    w := ![![126250, -1875, -12500], ![-570625, -31250, 18750]]
    hw := by decide
    g := ![![![168, 64, 6], ![271, 0, 0]], ![![45, 116, -6], ![393, 0, 0]]]
    h := ![![![1175, 1968, -3535], ![-84, 6675, 0]], ![![-5270, -8845, 15873], ![420, -29979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {625} * I17N1 =  Ideal.span {B.equivFun.symm ![202, -3, -20]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E17RS1 


noncomputable def E29RS0 : RelationCertificate Table 1375 ![![29, 0, 0], ![4, 1, 0]]
  ![-13982, 1633, -1035] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![39875, 0, 0], ![5500, 1375, 0]]
    hsu := by decide
    w := ![![-19225250, 2245375, -1423125], ![16566000, -1934625, 1226500]]
    hw := by decide
    g := ![![![15859037, 19741643, -29835267], ![-2485110, 57459351, 0]], ![![2663374, 3315385, -5010503], ![-417250, 9649662, 0]]]
    h := ![![![-1255685738, 855293176, 3826519929], ![-143705143, -12329897664, 0]], ![![1081997908, -736988090, -3297231508], ![123827731, 10624412736, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {1375} * I29N0 =  Ideal.span {B.equivFun.symm ![-13982, 1633, -1035]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 1375 ![![29, 0, 0], ![5, 1, 0]]
  ![631, -75, 48] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![39875, 0, 0], ![6875, 1375, 0]]
    hsu := by decide
    w := ![![867625, -103125, 66000], ![-763125, 88000, -56375]]
    hw := by decide
    g := ![![![-29780599, -37072115, 56026402], ![4668533, -107900520, 0]], ![![-5568529, -6932235, 10476481], ![873863, -20176520, 0]]]
    h := ![![![-15554919, 15995687, 47766696], ![-2130286, -153914904, 0]], ![![13673497, -14060960, -41989165], ![1872656, 135298416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {1375} * I29N1 =  Ideal.span {B.equivFun.symm ![631, -75, 48]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 1375 ![![31, 0, 0], ![0, 1, 0]]
  ![-383, -32, 2] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![42625, 0, 0], ![0, 1375, 0]]
    hsu := by decide
    w := ![![-526625, -44000, 2750], ![107250, -15125, -23375]]
    hw := by decide
    g := ![![![37, -276, 332], ![1010, -642, 0]], ![![144, -41, 6], ![636, -12, 0]]]
    h := ![![![1579492, 1051907, -4738513], ![33941, 16321545, 0]], ![![-321672, -214228, 965023], ![-6883, -3323970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {1375} * I31N0 =  Ideal.span {B.equivFun.symm ![-383, -32, 2]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 11 ![![31, 0, 0], ![3, 1, 0]]
  ![214, -25, 16] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![341, 0, 0], ![33, 11, 0]]
    hsu := by decide
    w := ![![2354, -275, 176], ![-2849, 330, -209]]
    hw := by decide
    g := ![![![-5923, -8014, 17957], ![355, -21948, 0]], ![![-538, -733, 1641], ![38, -2006, 0]]]
    h := ![![![6511, -2206, -19679], ![576, 67785, 0]], ![![-7882, 2669, 23816], ![-674, -82035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {11} * I31N1 =  Ideal.span {B.equivFun.symm ![214, -25, 16]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 125 ![![31, 0, 0], ![-4, 1, 0]]
  ![1027, -120, 76] ![![125, 0, 0], ![-62, -46, 1]] where
    su := ![![3875, 0, 0], ![-500, 125, 0]]
    hsu := by decide
    w := ![![128375, -15000, 9500], ![477250, -55750, 35375]]
    hw := by decide
    g := ![![![15, 18, 1], ![47, 0, 0]], ![![4, 7, 0], ![20, 0, 0]]]
    h := ![![![8827807, 17819352, -26701730], ![-564228, 91972634, 0]], ![![32818414, 66245570, -99266867], ![-2097676, 341919240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {125} * I31N2 =  Ideal.span {B.equivFun.symm ![1027, -120, 76]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E31RS2 
