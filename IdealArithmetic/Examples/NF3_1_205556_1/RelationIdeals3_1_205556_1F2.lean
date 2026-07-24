import IdealArithmetic.Examples.NF3_1_205556_1.PrimesBelow3_1_205556_1F2
import IdealArithmetic.Examples.NF3_1_205556_1.ClassGroupData3_1_205556_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-27, 1, 0]]
  ![2335, 393, -60] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![178, 0, 0], ![-54, 2, 0]]
    hsu := by decide
    w := ![![4670, 786, -120], ![75392, 5596, -1250]]
    hw := by decide
    g := ![![![-3337, 38625, 7824], ![-5499, 0, 0]], ![![663, -7235, -1467], ![1032, 0, 0]]]
    h := ![![![31568, -1236, 2], ![103971, -238, 0]], ![![509504, -19985, 36], ![1678080, -3829, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![2335, 393, -60]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 2 ![![89, 0, 0], ![-11, 1, 0]]
  ![-11, 1, 0] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![178, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![-22, 2, 0], ![856, 82, -16]]
    hw := by decide
    g := ![![![5, -3, -1], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-231, 32, -1], ![-1868, 89, 0]], ![![9206, -848, 1], ![74446, -97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {2} * I89N2 =  Ideal.span {B.equivFun.symm ![-11, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS2 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![47, 1, 0]]
  ![-24415, -3125, 532] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![202, 0, 0], ![94, 2, 0]]
    hsu := by decide
    w := ![![-48830, -6250, 1064], ![-373360, -21352, 5574]]
    hw := by decide
    g := ![![![130649, -1505168, -304915], ![214321, 0, 0]], ![![74147, -854231, -173049], ![121634, 0, 0]]]
    h := ![![![-330064, -8894, -34], ![708767, 3966, 0]], ![![-2521724, -67848, -273], ![5415052, 30360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![-24415, -3125, 532]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-39, 1, 0]]
  ![-9533, -707, 158] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![202, 0, 0], ![-78, 2, 0]]
    hsu := by decide
    w := ![![-19066, -1414, 316], ![70568, 11038, -1732]]
    hw := by decide
    g := ![![![-11181, 129040, 26140], ![-18373, 0, 0]], ![![3199, -36639, -7423], ![5218, 0, 0]]]
    h := ![![![-751585, 21234, -49], ![-1946168, 5107, 0]], ![![2780942, -78402, 175], ![7201022, -18541, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-9533, -707, 158]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 2 ![![103, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![206, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![232, 22, -4]]
    hw := by decide
    g := ![![![39, 7, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![1, 1, 1], ![13, -105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {2} * I103N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![50, 1, 0]]
  ![-3182109, -227881, 51954] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![206, 0, 0], ![100, 2, 0]]
    hsu := by decide
    w := ![![-6364218, -455762, 103908], ![26976784, 3990864, -639946]]
    hw := by decide
    g := ![![![1325934549, -15278980465, -3095185290], ![2175560597, 0, 0]], ![![776517878, -8947953713, -1812658560], ![1274091265, 0, 0]]]
    h := ![![![-127300053, -3554616, -19636], ![262174467, 2074462, 0]], ![![540253664, 15088404, 82225], ![-1112652780, -8789148, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-3182109, -227881, 51954]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![49, 1, 0]]
  ![109, 41, 4] ![![2, 0, 0], ![-52, -5, 1]] where
    su := ![![214, 0, 0], ![98, 2, 0]]
    hsu := by decide
    w := ![![218, 82, 8], ![296, 118, 12]]
    hw := by decide
    g := ![![![27, -20, 2], ![-23, 0, 0]], ![![53, -4, 0], ![-8, 0, 0]]]
    h := ![![![3845, 77, 0], ![-8394, 4, 0]], ![![5352, 107, 0], ![-11684, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![109, 41, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 
