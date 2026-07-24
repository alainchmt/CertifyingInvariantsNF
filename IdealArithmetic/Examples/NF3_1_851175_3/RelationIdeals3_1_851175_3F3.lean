import IdealArithmetic.Examples.NF3_1_851175_3.PrimesBelow3_1_851175_3F3
import IdealArithmetic.Examples.NF3_1_851175_3.ClassGroupData3_1_851175_3

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 7 ![![139, 0, 0], ![-49, 1, 0]]
  ![21, -14, 9] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![973, 0, 0], ![-343, 7, 0]]
    hsu := by decide
    w := ![![147, -98, 63], ![1043, -322, -42]]
    hw := by decide
    g := ![![![-2517, -236, -369], ![-393, 695, 0]], ![![831, 82, 129], ![135, -246, 0]]]
    h := ![![![70, 1152, -72], ![130, 3339, 0]], ![![216, 8014, -501], ![136, 23211, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {7} * I139N1 =  Ideal.span {B.equivFun.symm ![21, -14, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 49 ![![151, 0, 0], ![15, 1, 0]]
  ![27986, 980, 745] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![7399, 0, 0], ![735, 49, 0]]
    hsu := by decide
    w := ![![1371314, 48020, 36505], ![110446, 3871, 2940]]
    hw := by decide
    g := ![![![-163468606, 326733219, 490201826], ![3331960, -8006629843, 0]], ![![-16238607, 32456948, 48695554], ![330996, -795360717, 0]]]
    h := ![![![653751, -10450419, -1959455], ![-4151, 98626150, 0]], ![![52644, -841680, -157815], ![-241, 7943375, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {49} * I151N1 =  Ideal.span {B.equivFun.symm ![27986, 980, 745]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 49 ![![157, 0, 0], ![7, 1, 0]]
  ![-119, 0, -2] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![7693, 0, 0], ![343, 49, 0]]
    hsu := by decide
    w := ![![-5831, 0, -98], ![-343, -49, 0]]
    hw := by decide
    g := ![![![814, -1631, -2446], ![11, 39952, 0]], ![![36, -75, -111], ![48, 1813, 0]]]
    h := ![![![259840, -2078139, -779306], ![-1617, 40783680, 0]], ![![15232, -121856, -45696], ![-1, 2391424, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {49} * I157N1 =  Ideal.span {B.equivFun.symm ![-119, 0, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 7 ![![163, 0, 0], ![44, 1, 0]]
  ![-409304, -14336, -10897] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![1141, 0, 0], ![308, 7, 0]]
    hsu := by decide
    w := ![![-2865128, -100352, -76279], ![-1615432, -56581, -43008]]
    hw := by decide
    g := ![![![358, -249, -200], ![22, 489, 0]], ![![103, -69, -56], ![12, 132, 0]]]
    h := ![![![12665908, -569193123, -37946299], ![-72887, 2061745280, 0]], ![![7141364, -320925552, -21395088], ![-41107, 1162464400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {7} * I163N1 =  Ideal.span {B.equivFun.symm ![-409304, -14336, -10897]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS1 


noncomputable def E181RS1 : RelationCertificate Table 49 ![![181, 0, 0], ![-48, 1, 0]]
  ![21, 0, -5] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![8869, 0, 0], ![-2352, 49, 0]]
    hsu := by decide
    w := ![![1029, 0, -245], ![-539, 196, 0]]
    hw := by decide
    g := ![![![3171, -6308, -9463], ![-21, 154569, 0]], ![![-844, 1678, 2518], ![30, -41129, 0]]]
    h := ![![![-49818, -2345741, 149728], ![344, -9033591, 0]], ![![26338, 1237839, -79011], ![4, 4766997, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {49} * I181N1 =  Ideal.span {B.equivFun.symm ![21, 0, -5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 7 ![![191, 0, 0], ![-52, 1, 0]]
  ![7, 0, 1] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![1337, 0, 0], ![-364, 7, 0]]
    hsu := by decide
    w := ![![49, 0, 7], ![119, -28, 0]]
    hw := by decide
    g := ![![![99, -162, -245], ![-5, 573, 0]], ![![-28, 44, 68], ![8, -159, 0]]]
    h := ![![![22, 884, -52], ![17, 3311, 0]], ![![94, 2192, -129], ![187, 8213, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {7} * I191N1 =  Ideal.span {B.equivFun.symm ![7, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 7 ![![193, 0, 0], ![87, 1, 0]]
  ![21, 0, 1] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![1351, 0, 0], ![609, 7, 0]]
    hsu := by decide
    w := ![![147, 0, 7], ![133, -14, 0]]
    hw := by decide
    g := ![![![1353, -2621, -3970], ![-174, 9264, 0]], ![![603, -1168, -1769], ![-77, 4128, 0]]]
    h := ![![![-147, 11557, 394], ![35, -25347, 0]], ![![-205, 10471, 357], ![191, -22967, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {7} * I193N1 =  Ideal.span {B.equivFun.symm ![21, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E193RS1 
