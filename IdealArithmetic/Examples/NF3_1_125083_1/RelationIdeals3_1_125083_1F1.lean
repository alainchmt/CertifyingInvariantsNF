import IdealArithmetic.Examples.NF3_1_125083_1.PrimesBelow3_1_125083_1F1
import IdealArithmetic.Examples.NF3_1_125083_1.ClassGroupData3_1_125083_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 4 ![![37, 0, 0], ![14, 1, 0]]
  ![-493, 23, 27] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![148, 0, 0], ![56, 4, 0]]
    hsu := by decide
    w := ![![-1972, 92, 108], ![904, -636, 104]]
    hw := by decide
    g := ![![![-20985, 32819, 16655], ![-2283, -71511, 0]], ![![-9784, 12350, 6206], ![-1803, -27186, 0]]]
    h := ![![![-1293, -115, -1], ![3382, 64, 0]], ![![582, 41, 1], ![-1522, -11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {4} * I37N1 =  Ideal.span {B.equivFun.symm ![-493, 23, 27]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 2 ![![41, 0, 0], ![9, 1, 0]]
  ![-824601, -130707, -45569] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![82, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![-1649202, -261414, -91138], ![-3189830, -505618, -176276]]
    hw := by decide
    g := ![![![-1161, 619, -184], ![310, 123, 0]], ![![-464, 130, -23], ![65, 24, 0]]]
    h := ![![![-8936214, -1061173, -8590], ![40617797, 306621, 0]], ![![-17284118, -2052480, -16614], ![78561547, 593036, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2} * I41N0 =  Ideal.span {B.equivFun.symm ![-824601, -130707, -45569]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 8 ![![41, 0, 0], ![11, 1, 0]]
  ![199, 31, 11] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![328, 0, 0], ![88, 8, 0]]
    hsu := by decide
    w := ![![1592, 248, 88], ![1168, 184, 64]]
    hw := by decide
    g := ![![![-3, 78, 38], ![13, -309, 0]], ![![-3, 26, 13], ![8, -105, 0]]]
    h := ![![![656, 57, 0], ![-2427, 11, 0]], ![![472, 41, 0], ![-1746, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {8} * I41N1 =  Ideal.span {B.equivFun.symm ![199, 31, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![-25, 1, 0]]
  ![1173, -75, -59] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![212, 0, 0], ![-100, 4, 0]]
    hsu := by decide
    w := ![![4692, -300, -236], ![-1784, 1436, -252]]
    hw := by decide
    g := ![![![-93101, -6570, -6497], ![-48191, 82, 0]], ![![37119, 2620, 2591], ![19217, -35, 0]]]
    h := ![![![14366, -628, 1], ![30409, -112, 0]], ![![-5482, 271, -3], ![-11604, 96, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![1173, -75, -59]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![-20, 1, 0]]
  ![-209, 143, -23] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![-40, 2, 0]]
    hsu := by decide
    w := ![![-418, 286, -46], ![-1610, -48, 120]]
    hw := by decide
    g := ![![![-72636, -9211, 1861], ![-4605, -11750, 0]], ![![19860, 2518, -665], ![1260, 3525, 0]]]
    h := ![![![-311, 30, -1], ![-907, 36, 0]], ![![-1275, 83, 0], ![-3721, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![-209, 143, -23]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E73RS1 : RelationCertificate Table 8 ![![73, 0, 0], ![7, 1, 0]]
  ![3937, -511, -131] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![584, 0, 0], ![56, 8, 0]]
    hsu := by decide
    w := ![![31496, -4088, -1048], ![-1296, 3832, -904]]
    hw := by decide
    g := ![![![272689, -549945, -281547], ![-565, 2372868, 0]], ![![39831, -55832, -28703], ![2985, 247563, 0]]]
    h := ![![![7540, 1068, -1], ![-78069, -58, 0]], ![![-320, -42, -2], ![3314, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {8} * I73N1 =  Ideal.span {B.equivFun.symm ![3937, -511, -131]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E73RS1 
