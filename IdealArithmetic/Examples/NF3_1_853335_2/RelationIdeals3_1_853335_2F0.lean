import IdealArithmetic.Examples.NF3_1_853335_2.PrimesBelow3_1_853335_2F0
import IdealArithmetic.Examples.NF3_1_853335_2.ClassGroupData3_1_853335_2

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 4225 ![![3, 0, 0], ![1, 1, 0]]
  ![937, 147, 71] ![![4225, 0, 0], ![-74, 1, 0]] where
    su := ![![12675, 0, 0], ![4225, 4225, 0]]
    hsu := by decide
    w := ![![3958825, 621075, 299975], ![-54925, -8450, -4225]]
    hw := by decide
    g := ![![![46672, 11245638505, -1063776675], ![2664717, 642065207410, 0]], ![![21355, 5140729328, -486285234], ![1219259, 293507873379, 0]]]
    h := ![![![510, 248, 33], ![-593, -4, 0]], ![![-8, -5, -5], ![11, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4225} * I3N0 =  Ideal.span {B.equivFun.symm ![937, 147, 71]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![5, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![2, 1, 0]]
  ![12, 2, 1] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![25, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![60, 10, 5], ![215, 35, 15]]
    hw := by decide
    g := ![![![-8, 286, 2083], ![59, -1488, 0]], ![![-14, 191, 1389], ![37, -992, 0]]]
    h := ![![![68, 34, 3], ![-164, -2, 0]], ![![249, 130, 30], ![-601, -21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![12, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 169 ![![7, 0, 0], ![-14, -1, 1]]
  ![-21, -6, 4] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![1183, 0, 0], ![-2366, -169, 169]]
    hsu := by decide
    w := ![![-3549, -1014, 676], ![2366, 507, -338]]
    hw := by decide
    g := ![![![1, 0, 0], ![2, 0, 0]], ![![36, -3563, 337], ![82, -8136, 0]]]
    h := ![![![241, -112, 26], ![-458, 0, 40]], ![![-106, 57, -14], ![236, 0, -20]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {169} * I7N0 =  Ideal.span {B.equivFun.symm ![-21, -6, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 169 ![![13, 0, 0], ![-15, 5, 1]]
  ![-1821, -303, -136] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![2197, 0, 0], ![-2535, 845, 169]]
    hsu := by decide
    w := ![![-307749, -51207, -22984], ![107146, 17745, 7943]]
    hw := by decide
    g := ![![![-7728, -3576284, 338307], ![-17649, -8167698, 0]], ![![4304, 1950699, -184531], ![9831, 4455108, 0]]]
    h := ![![![-57, -51, -16], ![72, 0, 0]], ![![28, 15, 5], ![-18, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {169} * I13N0 =  Ideal.span {B.equivFun.symm ![-1821, -303, -136]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 1 ![![13, 0, 0], ![4, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![13, 0, 0], ![4, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![4, 1, 0]]
    hw := by decide
    g := ![![![17, 4, 0], ![-52, 0, 0]], ![![4, 1, 0], ![-12, 0, 0]]]
    h := ![![![17, 4, 0], ![-52, 0, 0]], ![![4, 1, 0], ![-12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {1} * I13N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 325 ![![17, 0, 0], ![1, 1, 0]]
  ![-157, -17, -6] ![![325, 0, 0], ![-74, 1, 0]] where
    su := ![![5525, 0, 0], ![325, 325, 0]]
    hsu := by decide
    w := ![![-51025, -5525, -1950], ![10400, 975, 325]]
    hw := by decide
    g := ![![![62, -11788, 1115], ![273, -51768, 0]], ![![25, -3066, 290], ![110, -13464, 0]]]
    h := ![![![-10, -10, -58], ![13, 140, 0]], ![![2, 0, -2], ![-2, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {325} * I17N1 =  Ideal.span {B.equivFun.symm ![-157, -17, -6]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 845 ![![19, 0, 0], ![3, 1, 0]]
  ![9259, 1559, 707] ![![845, 0, 0], ![-74, 1, 0]] where
    su := ![![16055, 0, 0], ![2535, 845, 0]]
    hsu := by decide
    w := ![![7823855, 1317355, 597415], ![-541645, -91260, -41405]]
    hw := by decide
    g := ![![![48, 128093, -12117], ![547, 1462690, 0]], ![![17, 24494, -2317], ![199, 279698, 0]]]
    h := ![![![18594268, 6365996, 392007], ![-117760611, -1063918, 0]], ![![-1287284, -440719, -27139], ![8152585, 73656, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {845} * I19N1 =  Ideal.span {B.equivFun.symm ![9259, 1559, 707]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![4, 1, 0]]
  ![12, -3, 1] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![115, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![60, -15, 5], ![215, 30, -20]]
    hw := by decide
    g := ![![![87, -2651, -19254], ![-510, 13752, 0]], ![![8, -554, -4012], ![-106, 2865, 0]]]
    h := ![![![4, -1, -3], ![-20, 10, 0]], ![![37, 8, -2], ![-202, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![12, -3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 169 ![![29, 0, 0], ![0, 1, 0]]
  ![-116, -9, 6] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![4901, 0, 0], ![0, 169, 0]]
    hsu := by decide
    w := ![![-19604, -1521, 1014], ![9802, 676, -507]]
    hw := by decide
    g := ![![![2259, 1036223, -98024], ![5159, 2366579, 0]], ![![73, -1, 0], ![167, 0, 0]]]
    h := ![![![-4, -2, -1], ![49, 5, 0]], ![![2, 0, -3], ![4, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {169} * I29N0 =  Ideal.span {B.equivFun.symm ![-116, -9, 6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E29RS0 


noncomputable def E31RS0 : RelationCertificate Table 4225 ![![31, 0, 0], ![-12, 1, 0]]
  ![23616, 3971, 1803] ![![4225, 0, 0], ![-74, 1, 0]] where
    su := ![![130975, 0, 0], ![-50700, 4225, 0]]
    hsu := by decide
    w := ![![99777600, 16777475, 7617675], ![-1381575, -232375, -105625]]
    hw := by decide
    g := ![![![35, 2450541, -231808], ![1972, 139912670, 0]], ![![22, -864669, 81793], ![1276, -49367908, 0]]]
    h := ![![![165408, -14835, 783], ![425336, -3210, 0]], ![![-2277, 208, -13], ![-5855, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {4225} * I31N0 =  Ideal.span {B.equivFun.symm ![23616, 3971, 1803]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 4225 ![![31, 0, 0], ![-10, 1, 0]]
  ![22679, 3824, 1732] ![![4225, 0, 0], ![-74, 1, 0]] where
    su := ![![130975, 0, 0], ![-42250, 4225, 0]]
    hsu := by decide
    w := ![![95818775, 16156400, 7317700], ![-1326650, -223925, -101400]]
    hw := by decide
    g := ![![![3599745, 868607872644, -82165614176], ![205526004, 49592817127660, 0]], ![![-1003820, -242225484860, 22913222824], ![-57312705, -13829766633056, 0]]]
    h := ![![![1009257509, -109557686, 6042548], ![3128696010, -26759608, 0]], ![![-13973534, 1516871, -83665], ![-43317924, 370513, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4225} * I31N1 =  Ideal.span {B.equivFun.symm ![22679, 3824, 1732]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 4225 ![![31, 0, 0], ![-9, 1, 0]]
  ![-746, 149, -43] ![![4225, 0, 0], ![-74, 1, 0]] where
    su := ![![130975, 0, 0], ![-38025, 4225, 0]]
    hsu := by decide
    w := ![![-3151850, 629525, -181675], ![46475, -12675, 4225]]
    hw := by decide
    g := ![![![-1633535, -394179349440, 37287237846], ![-93266021, -22505511414190, 0]], ![![450777, 108765199395, -10288600519], ![25736929, 6209905313254, 0]]]
    h := ![![![-2162, 256, -12], ![-7364, 47, 0]], ![![50, -3, -2], ![171, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {4225} * I31N2 =  Ideal.span {B.equivFun.symm ![-746, 149, -43]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS2 
