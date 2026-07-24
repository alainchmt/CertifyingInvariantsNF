import IdealArithmetic.Examples.NF3_1_203987_1.PrimesBelow3_1_203987_1F2
import IdealArithmetic.Examples.NF3_1_203987_1.ClassGroupData3_1_203987_1

set_option linter.all false

noncomputable section


noncomputable def E103RS0 : RelationCertificate Table 2 ![![103, 0, 0], ![10, 1, 0]]
  ![192543, 32233, 22345] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![385086, 64466, 44690], ![1966360, 329182, 228200]]
    hw := by decide
    g := ![![![4781, -14590, 45940], ![-7293, -18495, 0]], ![![210, -1941, 6140], ![-969, -2466, 0]]]
    h := ![![![570131, 57480, 430], ![-5853095, -4389, 0]], ![![2911280, 293527, 2205], ![-29887866, -22603, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {2} * I103N0 =  Ideal.span {B.equivFun.symm ![192543, 32233, 22345]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![36, 1, 0]]
  ![-13, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![72, 2, 0]]
    hsu := by decide
    w := ![![-26, -2, 2], ![88, -2, -2]]
    hw := by decide
    g := ![![![9, 36827, -115079], ![18415, 46032, 0]], ![![4, 13481, -42127], ![6742, 16851, 0]]]
    h := ![![![-451, -33, -3], ![1290, 62, 0]], ![![1316, 23, -2], ![-3764, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-13, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 2 ![![103, 0, 0], ![-47, 1, 0]]
  ![-11917, -1995, -1383] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![-94, 2, 0]]
    hsu := by decide
    w := ![![-23834, -3990, -2766], ![-121704, -20374, -14124]]
    hw := by decide
    g := ![![![1121, 3596, -11337], ![1799, 4521, 0]], ![![-541, -1628, 5151], ![-814, -2055, 0]]]
    h := ![![![-1222593, 29446, -366], ![-2679046, 7263, 0]], ![![-6243066, 150168, -1849], ![-13680318, 36677, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {2} * I103N2 =  Ideal.span {B.equivFun.symm ![-11917, -1995, -1383]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 2 ![![107, 0, 0], ![-51, 1, 0]]
  ![43, 7, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![-102, 2, 0]]
    hsu := by decide
    w := ![![86, 14, 10], ![440, 74, 50]]
    hw := by decide
    g := ![![![69, -71732, 224170], ![-35865, -89670, 0]], ![![-37, 33816, -105680], ![16909, 42273, 0]]]
    h := ![![![3344, -65, 0], ![7015, 1, 0]], ![![16670, -324, 0], ![34970, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {2} * I107N0 =  Ideal.span {B.equivFun.symm ![43, 7, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![-40, 1, 0]]
  ![-85, 1, 3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![-80, 2, 0]]
    hsu := by decide
    w := ![![-170, 2, 6], ![264, -60, 14]]
    hw := by decide
    g := ![![![417, -201, 851], ![-100, -321, 0]], ![![-116, 82, -321], ![43, 123, 0]]]
    h := ![![![-6815, 221, -6], ![-18228, 129, 0]], ![![10716, -276, 1], ![28662, -20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![-85, 1, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 2 ![![107, 0, 0], ![-17, 1, 0]]
  ![67, -9, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![-34, 2, 0]]
    hsu := by decide
    w := ![![134, -18, 2], ![88, 94, -42]]
    hw := by decide
    g := ![![![613, 54054, -168594], ![27029, 67466, 0]], ![![-39, -8546, 26683], ![-4271, -10675, 0]]]
    h := ![![![2101, -116, -2], ![13220, 43, 0]], ![![1362, -69, -3], ![8570, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {2} * I107N2 =  Ideal.span {B.equivFun.symm ![67, -9, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS2 
