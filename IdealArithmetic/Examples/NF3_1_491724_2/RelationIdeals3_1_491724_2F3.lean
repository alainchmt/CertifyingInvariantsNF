import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F3
import IdealArithmetic.Examples.NF3_1_491724_2.ClassGroupData3_1_491724_2

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 7 ![![151, 0, 0], ![-12, 1, 0]]
  ![-367, -18, 3] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![1057, 0, 0], ![-84, 7, 0]]
    hsu := by decide
    w := ![![-2569, -126, 21], ![2653, 119, -21]]
    hw := by decide
    g := ![![![-11, 236, -247], ![38, 1726, 0]], ![![-1, -18, 18], ![-1, -126, 0]]]
    h := ![![![-2005, 179, -1], ![-25199, 154, 0]], ![![2089, -174, 0], ![26255, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {7} * I151N1 =  Ideal.span {B.equivFun.symm ![-367, -18, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E151RS1 


noncomputable def E157RS0 : RelationCertificate Table 49 ![![157, 0, 0], ![-69, 1, 0]]
  ![-2687, -204, 27] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![7693, 0, 0], ![-3381, 49, 0]]
    hsu := by decide
    w := ![![-131663, -9996, 1323], ![-14357, -1127, 147]]
    hw := by decide
    g := ![![![-22, 5211, 401], ![131, -19640, 0]], ![![-1, -2171, -167], ![-14, 8180, 0]]]
    h := ![![![-111137, 1828, -3], ![-252838, 498, 0]], ![![-12065, 245, -1], ![-27448, 160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {49} * I157N0 =  Ideal.span {B.equivFun.symm ![-2687, -204, 27]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 49 ![![157, 0, 0], ![-44, 1, 0]]
  ![1811, 149, -19] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![7693, 0, 0], ![-2156, 49, 0]]
    hsu := by decide
    w := ![![88739, 7301, -931], ![9065, 784, -98]]
    hw := by decide
    g := ![![![2938947, -581010817, -44710530], ![-11077606, 2190815964, 0]], ![![-820209, 162147202, 12477715], ![3091565, -611408034, 0]]]
    h := ![![![18299, -420, 0], ![65253, -19, 0]], ![![1873, -43, 0], ![6679, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {49} * I157N1 =  Ideal.span {B.equivFun.symm ![1811, 149, -19]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E167RS1 : RelationCertificate Table 49 ![![167, 0, 0], ![63, 1, 0]]
  ![-15347, -4204, -291] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![8183, 0, 0], ![3087, 49, 0]]
    hsu := by decide
    w := ![![-752003, -205996, -14259], ![-421253, -115395, -7987]]
    hw := by decide
    g := ![![![-145, -5579, -428], ![-120, 21025, 0]], ![![-57, -2138, -164], ![-18, 8055, 0]]]
    h := ![![![-25898737, -504245, -1480], ![68651964, 246869, 0]], ![![-14507779, -282461, -829], ![38456992, 138280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {49} * I167N1 =  Ideal.span {B.equivFun.symm ![-15347, -4204, -291]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E167RS1 


noncomputable def E191RS1 : RelationCertificate Table 49 ![![191, 0, 0], ![34, 1, 0]]
  ![13921, 828, -124] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![9359, 0, 0], ![1666, 49, 0]]
    hsu := by decide
    w := ![![682129, 40572, -6076], ![86485, 5341, -784]]
    hw := by decide
    g := ![![![-263, -3477, -267], ![-98, 12815, 0]], ![![-73, -665, -51], ![-1, 2431, 0]]]
    h := ![![![18108187, 553358, 610], ![-101724994, -116634, 0]], ![![2295879, 70147, 77], ![-12897386, -14723, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {49} * I191N1 =  Ideal.span {B.equivFun.symm ![13921, 828, -124]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E191RS1 
