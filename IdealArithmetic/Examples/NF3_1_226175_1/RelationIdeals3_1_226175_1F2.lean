import IdealArithmetic.Examples.NF3_1_226175_1.PrimesBelow3_1_226175_1F2
import IdealArithmetic.Examples.NF3_1_226175_1.ClassGroupData3_1_226175_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 3 ![![83, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![249, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![12, 3, 0], ![141, -3, 6]]
    hw := by decide
    g := ![![![-15, -4, -1], ![4, 0, 0]], ![![-23, -2, -1], ![3, 0, 0]]]
    h := ![![![-4, -1, 0], ![84, 0, 0]], ![![41, 10, 0], ![-839, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {3} * I83N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS0 


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![-35, 1, 0]]
  ![-7, 2, 3] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![267, 0, 0], ![-105, 3, 0]]
    hsu := by decide
    w := ![![-21, 6, 9], ![192, -111, -36]]
    hw := by decide
    g := ![![![74, -199, -56], ![508, 0, 0]], ![![-34, 75, 21], ![-192, 0, 0]]]
    h := ![![![-63, 3, 0], ![-160, 3, 0]], ![![1046, 0, -1], ![2658, 77, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![-7, 2, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E89RS1 


noncomputable def E107RS1 : RelationCertificate Table 9 ![![107, 0, 0], ![-29, 1, 0]]
  ![22, -24, 5] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![963, 0, 0], ![-261, 9, 0]]
    hsu := by decide
    w := ![![198, -216, 45], ![675, -459, -72]]
    hw := by decide
    g := ![![![5441, 165, 149], ![56, 0, 0]], ![![-1412, -43, -30], ![-14, -26, 0]]]
    h := ![![![410, -13, 0], ![1512, 5, 0]], ![![1287, -47, 0], ![4746, -8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {9} * I107N1 =  Ideal.span {B.equivFun.symm ![22, -24, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 9 ![![107, 0, 0], ![-21, 1, 0]]
  ![622, 21, 17] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![963, 0, 0], ![-189, 9, 0]]
    hsu := by decide
    w := ![![5598, 189, 153], ![2295, 81, 63]]
    hw := by decide
    g := ![![![11, -6, -2], ![-1, 0, 0]], ![![-3, 1, 9], ![3, -26, 0]]]
    h := ![![![7472, -352, 0], ![38042, 17, 0]], ![![3078, -145, 0], ![15671, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {9} * I107N2 =  Ideal.span {B.equivFun.symm ![622, 21, 17]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![37, 1, 0]]
  ![-7, 7, -1] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![327, 0, 0], ![111, 3, 0]]
    hsu := by decide
    w := ![![-21, 21, -3], ![57, -66, 18]]
    hw := by decide
    g := ![![![10, -46, -13], ![116, 0, 0]], ![![-7, -17, -5], ![42, 0, 0]]]
    h := ![![![-459, -49, -1], ![1352, 108, 0]], ![![1193, 30, 0], ![-3514, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![-7, 7, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 9 ![![127, 0, 0], ![-6, 1, 0]]
  ![-23737, -801, -650] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![1143, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![-213633, -7209, -5850], ![-87750, -2961, -2403]]
    hw := by decide
    g := ![![![-106, 83, -221683], ![30, 665032, 0]], ![![3, -4, 10285], ![1, -30852, 0]]]
    h := ![![![-1278007, 213431, -83], ![-27047192, 9891, 0]], ![![-524946, 87673, -35], ![-11109732, 4178, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {9} * I127N1 =  Ideal.span {B.equivFun.symm ![-23737, -801, -650]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS1 
