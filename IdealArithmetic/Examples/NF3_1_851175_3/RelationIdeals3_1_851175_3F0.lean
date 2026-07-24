import IdealArithmetic.Examples.NF3_1_851175_3.PrimesBelow3_1_851175_3F0
import IdealArithmetic.Examples.NF3_1_851175_3.ClassGroupData3_1_851175_3

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 49 ![![3, 0, 0], ![24, 1, 1]]
  ![35, 0, 1] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![147, 0, 0], ![1176, 49, 49]]
    hsu := by decide
    w := ![![1715, 0, 49], ![147, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![29, -16, 0]]]
    h := ![![![1355, 20425, -22158], ![10265, 0, -5110]], ![![99, 1750, -1900], ![882, 0, -438]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {49} * I3N0 =  Ideal.span {B.equivFun.symm ![35, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![7, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![-5, 9, 15], ![7, -35, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-5, 9, 15], ![7, -35, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 49 ![![7, 0, 0], ![2, 1, 0]]
  ![448, -245, 122] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![343, 0, 0], ![98, 49, 0]]
    hsu := by decide
    w := ![![21952, -12005, 5978], ![14357, -4312, -735]]
    hw := by decide
    g := ![![![-10947, -574, -581], ![-205, 4686, 0]], ![![-7776, -325, -290], ![-157, 1342, 0]]]
    h := ![![![6222, -17757, -17812], ![-752, 41602, 0]], ![![-720, 2164, 2190], ![109, -5115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {49} * I7N1 =  Ideal.span {B.equivFun.symm ![448, -245, 122]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 49 ![![13, 0, 0], ![4, 1, 0]]
  ![-1393, -49, -37] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![637, 0, 0], ![196, 49, 0]]
    hsu := by decide
    w := ![![-68257, -2401, -1813], ![-5488, -196, -147]]
    hw := by decide
    g := ![![![2399599, -4796205, -7195805], ![-48907, 117531482, 0]], ![![738730, -1476539, -2215269], ![-15046, 36182728, 0]]]
    h := ![![![-6643, 31997, 19217], ![420, -83286, 0]], ![![-536, 2572, 1545], ![40, -6696, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {49} * I13N0 =  Ideal.span {B.equivFun.symm ![-1393, -49, -37]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 49 ![![13, 0, 0], ![-2, 1, 0]]
  ![14, 0, -1] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![637, 0, 0], ![-98, 49, 0]]
    hsu := by decide
    w := ![![686, 0, -49], ![-98, 49, 0]]
    hw := by decide
    g := ![![![-14472376, 28926692, 43399069], ![295013, -708851460, 0]], ![![2598340, -5193440, -7791780], ![-52919, 127265740, 0]]]
    h := ![![![-4034, -4108, 12251], ![316, -53088, 0]], ![![626, 635, -1896], ![-38, 8216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {49} * I13N1 =  Ideal.span {B.equivFun.symm ![14, 0, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E31RS1 : RelationCertificate Table 7 ![![31, 0, 0], ![11, 1, 0]]
  ![308, -119, 19] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![217, 0, 0], ![77, 7, 0]]
    hsu := by decide
    w := ![![2156, -833, 133], ![2555, -595, -357]]
    hw := by decide
    g := ![![![-39095, -3134, -4924], ![-6027, 8928, 0]], ![![-17719, -1156, -1831], ![-2696, 3120, 0]]]
    h := ![![![-2611, 31087, 7774], ![84, -80325, 0]], ![![-3074, 36516, 9129], ![119, -94350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {7} * I31N1 =  Ideal.span {B.equivFun.symm ![308, -119, 19]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
