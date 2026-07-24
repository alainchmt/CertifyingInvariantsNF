import IdealArithmetic.Examples.NF3_1_203987_1.PrimesBelow3_1_203987_1F0
import IdealArithmetic.Examples.NF3_1_203987_1.ClassGroupData3_1_203987_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![-7, -1, 1]]
  ![-1, -17, 7] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![8, 0, 0], ![-28, -4, 4]]
    hsu := by decide
    w := ![![-4, -68, 28], ![616, 96, -64]]
    hw := by decide
    g := ![![![-112, -18, -13], ![-3, 0, 0]], ![![-433, -69, -49], ![-16, -1, 0]]]
    h := ![![![3, -8, 3], ![1, 0, 0]], ![![7, 2, 2], ![-20, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![-1, -17, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![0, 1, 0]]
  ![2025, 339, 235] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![4050, 678, 470], ![20680, 3462, 2400]]
    hw := by decide
    g := ![![![-39, -27, 55], ![-13, -19, 0]], ![![132, 9, -10], ![5, 0, 0]]]
    h := ![![![285525, 28103, 9767], ![5624, 0, -16200]], ![![1457940, 143502, 49872], ![28701, 0, -82720]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![2025, 339, 235]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4 ![![5, 0, 0], ![2, 1, 0]]
  ![95259, 15947, 11055] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![20, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![381036, 63788, 44220], ![972840, 162860, 112900]]
    hw := by decide
    g := ![![![105, -204, 580], ![-51, -474, 0]], ![![-178, -113, 304], ![-28, -237, 0]]]
    h := ![![![16297, 1812, 2211], ![6887, 0, 0]], ![![41612, 4628, 5645], ![17575, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4} * I5N1 =  Ideal.span {B.equivFun.symm ![95259, 15947, 11055]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![0, 1, 0]]
  ![-77, -13, -9] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![44, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-308, -52, -36], ![-792, -132, -92]]
    hw := by decide
    g := ![![![15, 0, -3], ![3, 2, 0]], ![![-4, 2, -4], ![2, 3, 0]]]
    h := ![![![-7, -70, 171], ![1, -378, 0]], ![![-18, -178, 437], ![-7, -966, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![-77, -13, -9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-8, -5, 1]]
  ![271, -283, 105] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![-16, -10, 2]]
    hsu := by decide
    w := ![![542, -566, 210], ![9240, 1782, -1100]]
    hw := by decide
    g := ![![![24321, 3773, 1210], ![1887, 645, 0]], ![![-75436, -10482, -7572], ![-5239, -473, 0]]]
    h := ![![![29, -23, 9], ![6, 0, 0]], ![![276, -9, -32], ![-198, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![271, -283, 105]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E17RS0 : RelationCertificate Table 4 ![![17, 0, 0], ![1, 1, 0]]
  ![-2535, 109, 57] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![68, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![-10140, 436, 228], ![5016, -2240, 716]]
    hw := by decide
    g := ![![![110793, -203537315, 540705219], ![-50884328, -432553889, 0]], ![![73075, 11386, 8818], ![2849, -270, 0]]]
    h := ![![![-298, -142, 1], ![2531, 8, 0]], ![![146, 40, 7], ![-1228, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {4} * I17N0 =  Ideal.span {B.equivFun.symm ![-2535, 109, 57]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![3, 1, 0]]
  ![35, -1, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![68, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![140, -4, -4], ![-88, 28, -8]]
    hw := by decide
    g := ![![![-19, 2675, -7116], ![669, 5691, 0]], ![![-15, 890, -2373], ![224, 1897, 0]]]
    h := ![![![37, 11, -3], ![-198, 10, 0]], ![![-26, -8, -1], ![140, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![35, -1, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 4 ![![17, 0, 0], ![-5, 1, 0]]
  ![-5, -1, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![68, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![-20, -4, -4], ![-88, -12, -8]]
    hw := by decide
    g := ![![![1, 12, -36], ![7, 29, 0]], ![![1, -2, 6], ![0, -5, 0]]]
    h := ![![![-10, 6, -3], ![-33, 10, 0]], ![![-56, 12, -1], ![-186, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {4} * I17N2 =  Ideal.span {B.equivFun.symm ![-5, -1, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![3, 1, 0]]
  ![-15, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![-30, -2, 2], ![88, -4, -2]]
    hw := by decide
    g := ![![![-13, 44, -144], ![22, 57, 0]], ![![-9, 3, -16], ![3, 6, 0]]]
    h := ![![![-3, -11, -51], ![14, 194, 0]], ![![2, 30, 151], ![2, -574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![-15, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![7, 1, 0]]
  ![6971, 1167, 809] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![13942, 2334, 1618], ![71192, 11918, 8262]]
    hw := by decide
    g := ![![![-395, -494, 1523], ![-247, -600, 0]], ![![-39, -192, 570], ![-95, -225, 0]]]
    h := ![![![74617, 11327, 701], ![-201536, -2502, 0]], ![![381006, 57857, 3599], ![-1029074, -12850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![6971, 1167, 809]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![8, 1, 0]]
  ![-392057, -65633, -45499] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-784114, -131266, -90998], ![-4003912, -670282, -464662]]
    hw := by decide
    g := ![![![2745, 1625, -5332], ![813, 2100, 0]], ![![776, 847, -2503], ![424, 975, 0]]]
    h := ![![![-3205915, -455724, -47486], ![7565041, 171347, 0]], ![![-16370284, -2327031, -242459], ![38629180, 874878, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![-392057, -65633, -45499]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![1, 1, 0]]
  ![-233, -39, -27] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-466, -78, -54], ![-2376, -398, -276]]
    hw := by decide
    g := ![![![5, 372, -1142], ![187, 455, 0]], ![![-17, 71, -226], ![36, 91, 0]]]
    h := ![![![-11, -11, 41], ![20, -194, 0]], ![![-52, -52, 209], ![8, -989, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![-233, -39, -27]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-3, 1, 0]]
  ![2921, 489, 339] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![5842, 978, 678], ![29832, 4994, 3462]]
    hw := by decide
    g := ![![![-53, -2739, 8633], ![-1369, -3458, 0]], ![![-39, 206, -675], ![105, 273, 0]]]
    h := ![![![7051, -2330, 58], ![53084, -199, 0]], ![![36006, -11899, 297], ![271074, -1020, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![2921, 489, 339]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![14, 1, 0]]
  ![5, -3, 1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![124, 0, 0], ![56, 4, 0]]
    hsu := by decide
    w := ![![20, -12, 4], ![88, 20, -12]]
    hw := by decide
    g := ![![![-7, 14907, -39601], ![3727, 31680, 0]], ![![-6, 7220, -19182], ![1806, 15345, 0]]]
    h := ![![![221, 18, 1], ![-489, -6, 0]], ![![1062, 81, 2], ![-2350, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![5, -3, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
