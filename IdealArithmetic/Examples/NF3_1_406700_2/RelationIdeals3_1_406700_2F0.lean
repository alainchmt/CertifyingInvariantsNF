import IdealArithmetic.Examples.NF3_1_406700_2.PrimesBelow3_1_406700_2F0
import IdealArithmetic.Examples.NF3_1_406700_2.ClassGroupData3_1_406700_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3211 ![![2, 0, 0], ![1, 1, 0]]
  ![-1071, 40, -37] ![![3211, 0, 0], ![-1038, 1, 0]] where
    su := ![![6422, 0, 0], ![3211, 3211, 0]]
    hsu := by decide
    w := ![![-3438981, 128440, -118807], ![1114217, -41743, 38532]]
    hw := by decide
    g := ![![![-929, 1249709, -6014], ![847, 3862191, 0]], ![![-1413, 1905733, -9171], ![1303, 5889615, 0]]]
    h := ![![![26, 500, 389], ![-960, -163, 0]], ![![-10, -163, -129], ![313, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3211} * I2N0 =  Ideal.span {B.equivFun.symm ![-1071, 40, -37]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 3211 ![![5, 0, 0], ![16, -1, 1]]
  ![319, 126, 44] ![![3211, 0, 0], ![-1038, 1, 0]] where
    su := ![![16055, 0, 0], ![51376, -3211, 3211]]
    hsu := by decide
    w := ![![1024309, 404586, 141284], ![-333944, -131651, -44954]]
    hw := by decide
    g := ![![![622, -23895, 115], ![1852, -73845, 0]], ![![1096, -73760, 355], ![3167, -227950, 0]]]
    h := ![![![1227, 1045, -4691], ![2799, 0, -2300]], ![![-412, -340, 1529], ![-909, 0, 750]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3211} * I5N0 =  Ideal.span {B.equivFun.symm ![319, 126, 44]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 169 ![![7, 0, 0], ![2, 1, 0]]
  ![-70, -25, 2] ![![169, 0, 0], ![-24, 1, 0]] where
    su := ![![1183, 0, 0], ![338, 169, 0]]
    hsu := by decide
    w := ![![-11830, -4225, 338], ![1521, 507, -169]]
    hw := by decide
    g := ![![![1162496, -30282309, 6056869], ![-344161, -204722176, 0]], ![![473409, -12331761, 2466518], ![-140093, -83368308, 0]]]
    h := ![![![38231, 40628, 215111], ![16734, -301155, 0]], ![![-4948, -5258, -27838], ![-2164, 38973, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {169} * I7N0 =  Ideal.span {B.equivFun.symm ![-70, -25, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 169 ![![13, 0, 0], ![17, -6, 1]]
  ![17, -6, 14] ![![169, 0, 0], ![-24, 1, 0]] where
    su := ![![2197, 0, 0], ![2873, -1014, 169]]
    hsu := by decide
    w := ![![2873, -1014, 2366], ![-1352, -169, -338]]
    hw := by decide
    g := ![![![2281221, -59424693, 11885738], ![-675485, -401737944, 0]], ![![2852585, -74308327, 14862665], ![-844639, -502358076, 0]]]
    h := ![![![0, 0, 1], ![1, 0, 0]], ![![-15, 5, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {169} * I13N0 =  Ideal.span {B.equivFun.symm ![17, -6, 14]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 1 ![![13, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![2, 1, 0]] where
    su := ![![13, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![-74, -76, -385], ![-13, 1001, 0]], ![![-11, -11, -55], ![1, 143, 0]]]
    h := ![![![-74, -76, -385], ![-13, 1001, 0]], ![![-11, -11, -55], ![1, 143, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {1} * I13N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 1 ![![19, 0, 0], ![7, 1, 0]]
  ![1, 0, 0] ![![19, 0, 0], ![7, 1, 0]] where
    su := ![![19, 0, 0], ![7, 1, 0]]
    hsu := by decide
    w := ![![19, 0, 0], ![7, 1, 0]]
    hw := by decide
    g := ![![![-36, -263, -220], ![-19, 836, 0]], ![![-16, -96, -80], ![1, 304, 0]]]
    h := ![![![-36, -263, -220], ![-19, 836, 0]], ![![-16, -96, -80], ![1, 304, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {1} * I19N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 247 ![![23, 0, 0], ![7, 1, 0]]
  ![-3456, 127, -136] ![![247, 0, 0], ![-50, 1, 0]] where
    su := ![![5681, 0, 0], ![1729, 247, 0]]
    hsu := by decide
    w := ![![-853632, 31369, -33592], ![182039, -6669, 7163]]
    hw := by decide
    g := ![![![-26705743, 1479601642, -145063508], ![11396375, 7166137293, 0]], ![![-9396912, 520627403, -51043494], ![4010226, 2521548603, 0]]]
    h := ![![![7483, 54096, 45238], ![4651, -208122, 0]], ![![-1603, -11537, -9647], ![-968, 44382, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {247} * I23N0 =  Ideal.span {B.equivFun.symm ![-3456, 127, -136]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 19 ![![23, 0, 0], ![-6, 1, 0]]
  ![12, 2, 1] ![![19, 0, 0], ![7, 1, 0]] where
    su := ![![437, 0, 0], ![-114, 19, 0]]
    hsu := by decide
    w := ![![228, 38, 19], ![19, 0, 19]]
    hw := by decide
    g := ![![![0, -3, -2], ![6, 8, 0]], ![![-7, -23, -19], ![6, 72, 0]]]
    h := ![![![3636, -29411, 21077], ![-2223, -96954, 0]], ![![308, -2473, 1772], ![-178, -8151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {19} * I23N1 =  Ideal.span {B.equivFun.symm ![12, 2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 3211 ![![23, 0, 0], ![-2, 1, 0]]
  ![14619, -537, 577] ![![3211, 0, 0], ![-1038, 1, 0]] where
    su := ![![73853, 0, 0], ![-6422, 3211, 0]]
    hsu := by decide
    w := ![![46941609, -1724307, 1852747], ![-15213718, 558714, -600457]]
    hw := by decide
    g := ![![![4001625586, -5128617870989, 24680552316], ![-2890781253, -15849850697331, 0]], ![![-238706315, 305935327013, -1472258810], ![172445694, 945484607781, 0]]]
    h := ![![![-33787, 104876, -175351], ![7505, 806730, 0]], ![![10952, -33991, 56831], ![-2413, -261460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {3211} * I23N2 =  Ideal.span {B.equivFun.symm ![14619, -537, 577]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS2 


noncomputable def E29RS0 : RelationCertificate Table 169 ![![29, 0, 0], ![-13, 1, 0]]
  ![-93, 3, -7] ![![169, 0, 0], ![-24, 1, 0]] where
    su := ![![4901, 0, 0], ![-2197, 169, 0]]
    hsu := by decide
    w := ![![-15717, 507, -1183], ![2704, 0, 169]]
    hw := by decide
    g := ![![![-293, 7884, -1577], ![159, 53302, 0]], ![![115, -2840, 568], ![9, -19198, 0]]]
    h := ![![![-205280, 4394063, -1572308], ![243566, 9119385, 0]], ![![35267, -754751, 270069], ![-41821, -1566400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {169} * I29N0 =  Ideal.span {B.equivFun.symm ![-93, 3, -7]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 13 ![![29, 0, 0], ![-10, 1, 0]]
  ![-462, 17, -18] ![![13, 0, 0], ![2, 1, 0]] where
    su := ![![377, 0, 0], ![-130, 13, 0]]
    hsu := by decide
    w := ![![-6006, 221, -234], ![299, -13, 13]]
    hw := by decide
    g := ![![![-56014, -57012, -290053], ![-12992, 754138, 0]], ![![17457, 17769, 90406], ![4061, -235056, 0]]]
    h := ![![![-117984, 1666573, -759072], ![98154, 4402614, 0]], ![![5883, -82990, 37799], ![-4865, -219234, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {13} * I29N1 =  Ideal.span {B.equivFun.symm ![-462, 17, -18]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS1 
