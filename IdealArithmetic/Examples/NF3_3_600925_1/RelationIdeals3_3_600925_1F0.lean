import IdealArithmetic.Examples.NF3_3_600925_1.PrimesBelow3_3_600925_1F0
import IdealArithmetic.Examples.NF3_3_600925_1.ClassGroupData3_3_600925_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![601, 25, -14] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![1803, 75, -42], ![-12336, -531, 291]]
    hw := by decide
    g := ![![![79, 577, 54], ![-881, -182, 0]], ![![16, 45, 18], ![-13, 0, 0]]]
    h := ![![![29449, 8481, 396], ![2829, 0, -601]], ![![-201488, -58033, -2709], ![-19342, 0, 4112]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![601, 25, -14]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-30, -2, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![3, 0, 0], ![-30, -2, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-30, -2, 1]]
    hw := by decide
    g := ![![![27, 11, 0], ![-12, -3, 0]], ![![10, -92, -9], ![148, 30, 0]]]
    h := ![![![27, 11, 0], ![-12, -3, 0]], ![![10, -92, -9], ![148, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 3 ![![3, 0, 0], ![-31, -1, 1]]
  ![23, 8, 2] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![9, 0, 0], ![-93, -3, 3]]
    hsu := by decide
    w := ![![69, 24, 6], ![186, 78, 21]]
    hw := by decide
    g := ![![![25, 15, 1], ![-21, -5, 0]], ![![-3, -166, -15], ![262, 53, 0]]]
    h := ![![![41, 184, 54], ![-204, -44, 0]], ![![52, 489, 146], ![-548, -117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {3} * I3N2 =  Ideal.span {B.equivFun.symm ![23, 8, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![-2, 1, 0]]
  ![121, 49, 13] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![15, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![363, 147, 39], ![1626, 507, 120]]
    hw := by decide
    g := ![![![23, -83, 24], ![14, -12, 0]], ![![20, 264, -50], ![-137, 4, 0]]]
    h := ![![![39, 234, -229], ![37, 386, 0]], ![![170, 1101, -1090], ![154, 1830, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![121, 49, 13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![-29, -5, 1]]
  ![41735, 15356, 3926] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![21, 0, 0], ![-87, -15, 3]]
    hsu := by decide
    w := ![![125205, 46068, 11778], ![416730, 153330, 39201]]
    hw := by decide
    g := ![![![23, -25, 16], ![-22, -15, 0]], ![![3, -656, 63], ![564, 63, 0]]]
    h := ![![![187, 1198, 760], ![-1394, 0, 0]], ![![551, 3975, 2532], ![-4657, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![41735, 15356, 3926]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0, 0], ![-1, 1, 0]]
  ![8641, 2077, -551] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![63, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![77769, 18693, -4959], ![150381, 36126, -9585]]
    hw := by decide
    g := ![![![-76, -63, 1], ![281, 60, 0]], ![![41, 39, 13], ![-44, -4, 0]]]
    h := ![![![35892, -34466, 79], ![242603, -368, 0]], ![![69404, -66649, 156], ![469119, -719, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![8641, 2077, -551]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 9 ![![13, 0, 0], ![-5, 1, 0]]
  ![37, 7, -2] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![117, 0, 0], ![-45, 9, 0]]
    hsu := by decide
    w := ![![333, 63, -18], ![315, 108, -27]]
    hw := by decide
    g := ![![![-250, -235, -18], ![857, 174, 0]], ![![108, 80, 5], ![-277, -58, 0]]]
    h := ![![![2089, -467, 25], ![5424, -109, 0]], ![![1955, -438, 24], ![5076, -105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {9} * I13N0 =  Ideal.span {B.equivFun.symm ![37, 7, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0], ![-4, 1, 0]]
  ![-499, -181, -46] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![117, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![-4491, -1629, -414], ![-6237, -2340, -603]]
    hw := by decide
    g := ![![![-161, -161, -5], ![532, 98, 0]], ![![74, 67, -3], ![-178, -27, 0]]]
    h := ![![![-19967, 5509, -328], ![-64768, 1406, 0]], ![![-27721, 7650, -457], ![-89920, 1958, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![-499, -181, -46]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![7, 1, 0]]
  ![721, 31, -17] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![57, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![2163, 93, -51], ![-14622, -615, 342]]
    hw := by decide
    g := ![![![1147, 12163, 1095], ![-18917, -3910, 0]], ![![515, 5295, 478], ![-8225, -1700, 0]]]
    h := ![![![8442, 1362, 79], ![-22811, -506, 0]], ![![-57168, -9257, -552], ![154474, 3534, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![721, 31, -17]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![-6, 1, 0]]
  ![-8215, -502, 224] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![93, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![-24645, -1506, 672], ![140454, 3756, -2847]]
    hw := by decide
    g := ![![![695, -35375, -14991], ![11869, 11, 0]], ![![174, -8814, -3739], ![2943, -1, 0]]]
    h := ![![![-751, -82390, 35345], ![-2511, -365157, 0]], ![![4302, 472762, -202825], ![14424, 2095542, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![-8215, -502, 224]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
