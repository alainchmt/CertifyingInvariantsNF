import IdealArithmetic.Examples.NF3_1_30251_1.PrimesBelow3_1_30251_1F1
import IdealArithmetic.Examples.NF3_1_30251_1.ClassGroupData3_1_30251_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-2, 1, 0]]
  ![-31, 19, -9] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-62, 38, -18], ![-306, -42, 68]]
    hw := by decide
    g := ![![![-1461, -174, 49], ![-86, -111, 0]], ![![-131, -1, -43], ![1, 9, 0]]]
    h := ![![![-103, 53, -2], ![-1890, 13, 0]], ![![-521, 261, -3], ![-9562, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-31, 19, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![-10, 1, 0]]
  ![7, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![82, 0, 0], ![-20, 2, 0]]
    hsu := by decide
    w := ![![14, 2, 2], ![34, 2, 8]]
    hw := by decide
    g := ![![![1, -100, 309], ![-50, -123, 0]], ![![1, 26, -83], ![15, 33, 0]]]
    h := ![![![147, -5, -4], ![602, 33, 0]], ![![357, -33, -1], ![1462, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![7, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 4 ![![43, 0, 0], ![12, 1, 0]]
  ![7, -1, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![172, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![28, -4, 4], ![48, 4, 0]]
    hw := by decide
    g := ![![![1, 0, 139976], ![3, -111981, 0]], ![![0, 0, 41220], ![1, -32976, 0]]]
    h := ![![![13, -5, -3], ![-46, 26, 0]], ![![36, 3, 0], ![-128, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {4} * I43N0 =  Ideal.span {B.equivFun.symm ![7, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 4 ![![43, 0, 0], ![-9, 1, 0]]
  ![1, 13, -9] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![172, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![4, 52, -36], ![-304, 28, 20]]
    hw := by decide
    g := ![![![163, -6, 30947], ![83, -24732, 0]], ![![-15, 0, -6014], ![-5, 4809, 0]]]
    h := ![![![4, 6, -3], ![19, 24, 0]], ![![-7, -1484, 675], ![-25, -5804, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {4} * I43N1 =  Ideal.span {B.equivFun.symm ![1, 13, -9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 4 ![![43, 0, 0], ![-4, 1, 0]]
  ![-2027, -147, -317] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![172, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![-8108, -588, -1268], ![-14832, -1076, -2320]]
    hw := by decide
    g := ![![![-63, 15, -109058], ![-23, 87249, 0]], ![![8, -4, 6871], ![3, -5496, 0]]]
    h := ![![![-8501, 2124, -19], ![-90879, 100, 0]], ![![-15564, 3883, -30], ![-166386, 142, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {4} * I43N2 =  Ideal.span {B.equivFun.symm ![-2027, -147, -317]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS2 
