import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F0
import IdealArithmetic.Examples.NF3_1_271660_2.ClassGroupData3_1_271660_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 5 ![![2, 0, 0], ![0, 1, 0]]
  ![-85258, -6475, 1592] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![10, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![-426290, -32375, 7960], ![-441970, 62510, -1725]]
    hw := by decide
    g := ![![![564312, -5963328, -1672283], ![3048606, 0, 0]], ![![2716697, -28710383, -8051178], ![14677449, 0, 0]]]
    h := ![![![-42629, -2590, 0], ![-1295, 1592, 0]], ![![-44197, 5000, 0], ![2502, -345, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {5} * I2N0 =  Ideal.span {B.equivFun.symm ![-85258, -6475, 1592]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 5 ![![5, 0, 0], ![2, 1, 0]]
  ![422489, 164588, 17093] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![25, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![2112445, 822940, 85465], ![3645645, 1420225, 147495]]
    hw := by decide
    g := ![![![-2195, -658, 439], ![308, -1968, 0]], ![![1207, -85, 199], ![-257, -1107, 0]]]
    h := ![![![2591607, 1540981, 130673], ![-6267773, -636272, 0]], ![![4472583, 2659418, 225515], ![-10816893, -1098076, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {5} * I5N0 =  Ideal.span {B.equivFun.symm ![422489, 164588, 17093]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![5, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![4, -3, 0], ![15, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, -3, 0], ![15, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 5 ![![7, 0, 0], ![0, 1, 0]]
  ![4795, 1868, 194] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![35, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![23975, 9340, 970], ![-89600, -34905, -3625]]
    hw := by decide
    g := ![![![21, 0, -2], ![-44, 0, 0]], ![![20, 15, 0], ![44, 0, 0]]]
    h := ![![![685, 261, 0], ![41, 194, 0]], ![![-2560, -978, 0], ![-135, -725, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {5} * I7N0 =  Ideal.span {B.equivFun.symm ![4795, 1868, 194]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 5 ![![7, 0, 0], ![-47, -7, 1]]
  ![-69, -28, -3] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![35, 0, 0], ![-235, -35, 5]]
    hsu := by decide
    w := ![![-345, -140, -15], ![-645, -245, -25]]
    hw := by decide
    g := ![![![-6, 5, -7], ![5, 36, 0]], ![![-41, -53, 50], ![2, -246, 0]]]
    h := ![![![17, 0, -1], ![4, 0, 0]], ![![42, 2, -2], ![9, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {5} * I7N1 =  Ideal.span {B.equivFun.symm ![-69, -28, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E17RS0 : RelationCertificate Table 5 ![![17, 0, 0], ![0, 1, 0]]
  ![-153, -13, 3] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![85, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![-765, -65, 15], ![-1360, 45, 10]]
    hw := by decide
    g := ![![![45, -11, -6], ![14, 0, 0]], ![![8, -9, -3], ![6, 0, 0]]]
    h := ![![![-9, -1, 0], ![4, 3, 0]], ![![-16, 0, 0], ![9, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {5} * I17N0 =  Ideal.span {B.equivFun.symm ![-153, -13, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![6, 1, 0]]
  ![-1319, -123, 27] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![115, 0, 0], ![30, 5, 0]]
    hsu := by decide
    w := ![![-6595, -615, 135], ![7745, 640, -150]]
    hw := by decide
    g := ![![![-1130, -468, -56], ![133, 46, 0]], ![![-768, -322, -34], ![90, 11, 0]]]
    h := ![![![-1321, -235, -2], ![4844, 73, 0]], ![![1535, 264, 1], ![-5626, -53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![-1319, -123, 27]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 5 ![![23, 0, 0], ![-11, 1, 0]]
  ![-284025379, -110647070, -11491059] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![115, 0, 0], ![-55, 5, 0]]
    hsu := by decide
    w := ![![-1420126895, -553235350, -57455295], ![5307218310, 2067520015, 214718695]]
    hw := by decide
    g := ![![![-6717, 22329, -1126], ![27799, 0, 0]], ![![4619, -15574, 828], ![-18349, 0, 0]]]
    h := ![![![-16193021460, 1726410674, -24158810], ![-33832315291, 544161571, 0]], ![![60515648516, -6451844780, 90284942], ![126436224746, -2033609927, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {5} * I23N2 =  Ideal.span {B.equivFun.symm ![-284025379, -110647070, -11491059]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 5 ![![29, 0, 0], ![14, 1, 0]]
  ![-277, -29, 6] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![145, 0, 0], ![70, 5, 0]]
    hsu := by decide
    w := ![![-1385, -145, 30], ![1705, 160, -35]]
    hw := by decide
    g := ![![![55, 45, -21], ![-2, 116, 0]], ![![45, 28, -9], ![1, 54, 0]]]
    h := ![![![-5275, -646, -19], ![10907, 557, 0]], ![![6459, 773, 22], ![-13355, -645, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {5} * I29N1 =  Ideal.span {B.equivFun.symm ![-277, -29, 6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![10, 1, 0]]
  ![-2077, -809, -84] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![155, 0, 0], ![50, 5, 0]]
    hsu := by decide
    w := ![![-10385, -4045, -420], ![-17915, -6980, -725]]
    hw := by decide
    g := ![![![377, 75, -33], ![-58, 124, 0]], ![![61, 16, -9], ![-7, 38, 0]]]
    h := ![![![-48947, -5877, -99], ![151528, 2985, 0]], ![![-84433, -10130, -170], ![261384, 5125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![-2077, -809, -84]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
