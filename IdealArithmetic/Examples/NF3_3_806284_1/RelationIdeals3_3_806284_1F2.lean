import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F2
import IdealArithmetic.Examples.NF3_3_806284_1.ClassGroupData3_3_806284_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![21, 1, 0]]
  ![-6023, -3880, -645] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![166, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![-12046, -7760, -1290], ![-61988, -39932, -6638]]
    hw := by decide
    g := ![![![86, -342, 167], ![-1079, 0, 0]], ![![51, -96, 37], ![-235, 3, 0]]]
    h := ![![![-5149, -324, -11], ![20064, 134, 0]], ![![-26336, -1576, -49], ![102614, 374, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![-6023, -3880, -645]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 2 ![![97, 0, 0], ![-39, 1, 0]]
  ![-6165, -68, 125] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![194, 0, 0], ![-78, 2, 0]]
    hsu := by decide
    w := ![![-12330, -136, 250], ![176856, 1952, -3586]]
    hw := by decide
    g := ![![![31, 37, 1], ![-3, 0, 0]], ![![33, -32, -1], ![13, 3, 0]]]
    h := ![![![-48900, 1295, -1], ![-121465, 111, 0]], ![![701424, -18550, 13], ![1742300, -1527, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {2} * I97N1 =  Ideal.span {B.equivFun.symm ![-6165, -68, 125]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![11, 1, 0]]
  ![-9, -4, 1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![202, 0, 0], ![22, 2, 0]]
    hsu := by decide
    w := ![![-18, -8, 2], ![-312, -80, 22]]
    hw := by decide
    g := ![![![29, 2, 0], ![-1, 0, 0]], ![![6, 20, 0], ![-9, -3, 0]]]
    h := ![![![-43, -10, -1], ![394, 51, 0]], ![![-496, -52, -1], ![4540, 56, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![-9, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-9, 1, 0]]
  ![11, 6, 1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![202, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![22, 12, 2], ![38, 60, 12]]
    hw := by decide
    g := ![![![5, -4, 1], ![-3, 0, 0]], ![![30, 21, -1], ![-7, -3, 0]]]
    h := ![![![64, -3, -1], ![717, 51, 0]], ![![86, -9, 0], ![963, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![11, 6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 2 ![![101, 0, 0], ![-2, 1, 0]]
  ![11, -6, 1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![202, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![22, -12, 2], ![-1198, -132, 48]]
    hw := by decide
    g := ![![![5, 32, 7], ![-3, 0, 0]], ![![23, 23, 0], ![-8, -3, 0]]]
    h := ![![![1, 5, -11], ![45, 556, 0]], ![![-5, -297, 592], ![47, -29884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {2} * I101N2 =  Ideal.span {B.equivFun.symm ![11, -6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS2 


noncomputable def E103RS0 : RelationCertificate Table 2 ![![103, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![206, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![0, 2, 0], ![0, 2, 2]]
    hw := by decide
    g := ![![![-43, 8, 0], ![-17, 1, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, -2, -3], ![52, 155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {2} * I103N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS0 


noncomputable def E109RS1 : RelationCertificate Table 2 ![![109, 0, 0], ![-23, 1, 0]]
  ![-2251, -1450, -241] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![218, 0, 0], ![-46, 2, 0]]
    hsu := by decide
    w := ![![-4502, -2900, -482], ![-23170, -14924, -2480]]
    hw := by decide
    g := ![![![79, -336, 165], ![-1069, 0, 0]], ![![14, 59, -39], ![257, 3, 0]]]
    h := ![![![-9764, 441, -5], ![-46175, 152, 0]], ![![-50398, 2213, -20], ![-238339, 470, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {2} * I109N1 =  Ideal.span {B.equivFun.symm ![-2251, -1450, -241]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![-37, 1, 0]]
  ![-39, -14, 3] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![262, 0, 0], ![-74, 2, 0]]
    hsu := by decide
    w := ![![-78, -28, 6], ![-734, -260, 60]]
    hw := by decide
    g := ![![![-5, 30, -15], ![97, 0, 0]], ![![19, 11, 4], ![-37, -3, 0]]]
    h := ![![![-2801, 94, -1], ![-9916, 67, 0]], ![![-26453, 790, -4], ![-93648, 277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![-39, -14, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 
