import IdealArithmetic.Examples.NF3_1_213716_1.PrimesBelow3_1_213716_1F2
import IdealArithmetic.Examples.NF3_1_213716_1.ClassGroupData3_1_213716_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 8 ![![83, 0, 0], ![30, 1, 0]]
  ![-10, 2, 1] ![![8, 0, 0], ![-3, 1, 0]] where
    su := ![![664, 0, 0], ![240, 8, 0]]
    hsu := by decide
    w := ![![-80, 16, 8], ![-56, -24, 0]]
    hw := by decide
    g := ![![![2574, 62805, -21222], ![6889, 169773, 0]], ![![1047, 25516, -8622], ![2800, 68975, 0]]]
    h := ![![![-110, -34, -1], ![304, 84, 0]], ![![-89, -33, -1], ![246, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {8} * I83N0 =  Ideal.span {B.equivFun.symm ![-10, 2, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E83RS0 


noncomputable def E83RS2 : RelationCertificate Table 16 ![![83, 0, 0], ![-4, 1, 0]]
  ![-50, 18, 9] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![1328, 0, 0], ![-64, 16, 0]]
    hsu := by decide
    w := ![![-800, 288, 144], ![-624, -176, 0]]
    hw := by decide
    g := ![![![-169, -2366, 794], ![-103, -12803, 0]], ![![17, 142, -48], ![18, 777, 0]]]
    h := ![![![-54, 14, 0], ![-1108, 9, 0]], ![![-41, 14, -1], ![-841, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {16} * I83N2 =  Ideal.span {B.equivFun.symm ![-50, 18, 9]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![41, 1, 0]]
  ![24, -4, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![178, 0, 0], ![82, 2, 0]]
    hsu := by decide
    w := ![![48, -8, 2], ![-62, 12, -2]]
    hw := by decide
    g := ![![![5, -3, -1], ![1, 0, 0]], ![![3, -3, -2], ![1, 3, 0]]]
    h := ![![![636, 15, 0], ![-1380, 1, 0]], ![![-842, -61, -1], ![1827, 88, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![24, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![17, 1, 0]]
  ![20, 2, -1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![202, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![40, 4, -2], ![106, 30, 0]]
    hw := by decide
    g := ![![![31, -208, -14], ![305, 43, 0]], ![![0, -33, -3], ![49, 8, 0]]]
    h := ![![![14, -16, -1], ![-82, 100, 0]], ![![49, 3, 0], ![-288, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![20, 2, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 32 ![![101, 0, 0], ![-35, 1, 0]]
  ![110, 34, 1] ![![32, 0, 0], ![-3, 1, 0]] where
    su := ![![3232, 0, 0], ![-1120, 32, 0]]
    hsu := by decide
    w := ![![3520, 1088, 32], ![-416, 0, 32]]
    hw := by decide
    g := ![![![30, 693, -232], ![41, 7458, 0]], ![![115, 42625, -14222], ![1333, 455091, 0]]]
    h := ![![![1460, -41, 0], ![4210, 1, 0]], ![![-163, 40, -1], ![-470, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {32} * I101N1 =  Ideal.span {B.equivFun.symm ![110, 34, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 16 ![![107, 0, 0], ![6, 1, 0]]
  ![-650, 122, -27] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![1712, 0, 0], ![96, 16, 0]]
    hsu := by decide
    w := ![![-10400, 1952, -432], ![4272, -800, 176]]
    hw := by decide
    g := ![![![13, 599, -199], ![43, 3192, 0]], ![![-1589, -140560, 47030], ![-8474, -752479, 0]]]
    h := ![![![-658, -112, -1], ![11626, 80, 0]], ![![261, 42, 0], ![-4610, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {16} * I107N1 =  Ideal.span {B.equivFun.symm ![-650, 122, -27]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 32 ![![109, 0, 0], ![-7, 1, 0]]
  ![46, 2, 1] ![![32, 0, 0], ![-3, 1, 0]] where
    su := ![![3488, 0, 0], ![-224, 32, 0]]
    hsu := by decide
    w := ![![1472, 64, 32], ![-224, 32, 0]]
    hw := by decide
    g := ![![![4, 119, -40], ![23, 1279, 0]], ![![0, -6, 2], ![1, -64, 0]]]
    h := ![![![10592, -1513, 0], ![164926, 1, 0]], ![![-1610, 237, -1], ![-25069, 109, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {32} * I109N1 =  Ideal.span {B.equivFun.symm ![46, 2, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 64 ![![113, 0, 0], ![-5, 1, 0]]
  ![78, 2, 1] ![![64, 0, 0], ![-3, 1, 0]] where
    su := ![![7232, 0, 0], ![-320, 64, 0]]
    hsu := by decide
    w := ![![4992, 128, 64], ![-320, 64, 0]]
    hw := by decide
    g := ![![![3772366, 5161848850, -1721035435], ![80477113, 110146267839, 0]], ![![-178008, -243574492, 81211276], ![-3797503, -5197521664, 0]]]
    h := ![![![25686, -5142, 1], ![580488, -112, 0]], ![![-1640, 333, -1], ![-37063, 113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {64} * I113N1 =  Ideal.span {B.equivFun.symm ![78, 2, 1]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E113RS1 
