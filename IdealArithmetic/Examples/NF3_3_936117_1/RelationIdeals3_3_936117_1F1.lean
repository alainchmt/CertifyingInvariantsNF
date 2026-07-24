import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F1
import IdealArithmetic.Examples.NF3_3_936117_1.ClassGroupData3_3_936117_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 4 ![![41, 0, 0], ![3, 1, 0]]
  ![-543, -463, -53] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![164, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![-2172, -1852, -212], ![-5260, -4504, -516]]
    hw := by decide
    g := ![![![676, -14148, -14889], ![-3365, 59605, 0]], ![![95, -1384, -1475], ![-322, 5895, 0]]]
    h := ![![![-549, -192, -2], ![7322, 29, 0]], ![![-1319, -459, -4], ![17588, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {4} * I41N0 =  Ideal.span {B.equivFun.symm ![-543, -463, -53]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 4 ![![41, 0, 0], ![12, 1, 0]]
  ![1987, 43, -31] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![164, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![7948, 172, -124], ![-772, -16, 12]]
    hw := by decide
    g := ![![![-1097, 18717, 19815], ![4409, -79255, 0]], ![![-342, 5880, 6223], ![1385, -24890, 0]]]
    h := ![![![58583, 5440, 46], ![-199993, -1917, 0]], ![![-5693, -535, -5], ![19435, 208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {4} * I41N1 =  Ideal.span {B.equivFun.symm ![1987, 43, -31]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 4 ![![41, 0, 0], ![-15, 1, 0]]
  ![2335, 1999, 229] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![164, 0, 0], ![-60, 4, 0]]
    hsu := by decide
    w := ![![9340, 7996, 916], ![22716, 19448, 2228]]
    hw := by decide
    g := ![![![202, 6639, 7030], ![1713, -28165, 0]], ![![-122, -2008, -2124], ![-532, 8515, 0]]]
    h := ![![![13760, -931, 10], ![37455, -181, 0]], ![![33444, -2288, 26], ![91035, -509, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {4} * I41N2 =  Ideal.span {B.equivFun.symm ![2335, 1999, 229]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![-11, 1, 0]]
  ![-67, -1, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![86, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![-134, -2, 2], ![22, -2, 0]]
    hw := by decide
    g := ![![![14, -51, -64], ![-16, 129, 0]], ![![-4, 14, 18], ![7, -36, 0]]]
    h := ![![![-87, 19, -1], ![-334, 44, 0]], ![![33, -3, 0], ![128, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![-67, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![23, 1, 0]]
  ![-7147, -6119, -701] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![236, 0, 0], ![92, 4, 0]]
    hsu := by decide
    w := ![![-28588, -24476, -2804], ![-69536, -59532, -6820]]
    hw := by decide
    g := ![![![2382, -32850, -34913], ![-7615, 139564, 0]], ![![941, -13556, -14387], ![-3151, 57523, 0]]]
    h := ![![![-40407, -2134, -24], ![103342, 715, 0]], ![![-98238, -5180, -58], ![251246, 1717, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-7147, -6119, -701]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-27, 1, 0]]
  ![85, -1, -1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![122, 0, 0], ![-54, 2, 0]]
    hsu := by decide
    w := ![![170, -2, -2], ![-4, 18, -2]]
    hw := by decide
    g := ![![![2101, -10300, -12388], ![-4099, 24786, 0]], ![![-922, 4548, 5466], ![1813, -10935, 0]]]
    h := ![![![4768, -177, 0], ![10769, -1, 0]], ![![-116, 31, -1], ![-262, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![85, -1, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 
