import IdealArithmetic.Examples.NF3_1_703404_2.PrimesBelow3_1_703404_2F0
import IdealArithmetic.Examples.NF3_1_703404_2.ClassGroupData3_1_703404_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 14 ![![3, 0, 0], ![-1, 1, 0]]
  ![-64, -3, 1] ![![14, 0, 0], ![-42, -4, 1]] where
    su := ![![42, 0, 0], ![-14, 14, 0]]
    hsu := by decide
    w := ![![-896, -42, 14], ![854, 182, -28]]
    hw := by decide
    g := ![![![-7567, -443, -471], ![22891, 4074, 0]], ![![2202, 132, 134], ![-6529, -1164, 0]]]
    h := ![![![-46, 26, -2], ![-74, 7, 0]], ![![46, -23, 1], ![77, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {14} * I3N0 =  Ideal.span {B.equivFun.symm ![-64, -3, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-43, -3, 1]]
  ![55, 11, 1] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![343, 0, 0], ![-2107, -147, 49]]
    hsu := by decide
    w := ![![2695, 539, 49], ![-343, 0, 0]]
    hw := by decide
    g := ![![![0, -242, 22], ![-1, -1078, 0]], ![![12, 1495, -136], ![63, 6666, 0]]]
    h := ![![![14, 2, 0], ![1, 0, 0]], ![![42, 3, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![55, 11, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![7, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![4, 1, 0], ![-7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, 1, 0], ![-7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 49 ![![11, 0, 0], ![-39, -7, 1]]
  ![577, 37, -10] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![539, 0, 0], ![-1911, -343, 49]]
    hsu := by decide
    w := ![![28273, 1813, -490], ![-8967, -490, 147]]
    hw := by decide
    g := ![![![-579266, -132810652, 12078483], ![-2580369, -591845666, 0]], ![![1931198, 442769323, -40267717], ![8602613, 1973118132, 0]]]
    h := ![![![17, -3, 0], ![-10, 0, 0]], ![![33, 8, -1], ![14, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {49} * I11N0 =  Ideal.span {B.equivFun.symm ![577, 37, -10]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 7 ![![11, 0, 0], ![-4, 1, 0]]
  ![-135, -48, -5] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![77, 0, 0], ![-28, 7, 0]]
    hsu := by decide
    w := ![![-945, -336, -35], ![-1715, -609, -63]]
    hw := by decide
    g := ![![![516, -10427, -3535], ![-1265, 24748, 0]], ![![-126, 2719, 922], ![340, -6456, 0]]]
    h := ![![![-217, 53, -2], ![-563, 17, 0]], ![![-403, 96, -3], ![-1047, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {7} * I11N1 =  Ideal.span {B.equivFun.symm ![-135, -48, -5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 49 ![![13, 0, 0], ![3, 1, 0]]
  ![61, 22, 2] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![637, 0, 0], ![147, 49, 0]]
    hsu := by decide
    w := ![![2989, 1078, 98], ![-147, -49, 0]]
    hw := by decide
    g := ![![![3884, 889393, -80886], ![17313, 3963416, 0]], ![![1507, 343151, -31208], ![6712, 1529192, 0]]]
    h := ![![![6334, 2258, 49], ![-27427, -635, 0]], ![![-312, -113, -3], ![1351, 39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {49} * I13N0 =  Ideal.span {B.equivFun.symm ![61, 22, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 49 ![![13, 0, 0], ![-6, 1, 0]]
  ![129, 16, -3] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![637, 0, 0], ![-294, 49, 0]]
    hsu := by decide
    w := ![![6321, 784, -147], ![-2205, -245, 49]]
    hw := by decide
    g := ![![![-18916, -4339419, 394649], ![-84263, -19337800, 0]], ![![7481, 1714770, -155950], ![33323, 7641550, 0]]]
    h := ![![![41955, -8089, 183], ![90881, -2382, 0]], ![![-14631, 2822, -64], ![-31693, 833, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {49} * I13N1 =  Ideal.span {B.equivFun.symm ![129, 16, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 14 ![![17, 0, 0], ![-6, 1, 0]]
  ![34, 11, 1] ![![14, 0, 0], ![-42, -4, 1]] where
    su := ![![238, 0, 0], ![-84, 14, 0]]
    hsu := by decide
    w := ![![476, 154, 14], ![406, 126, 14]]
    hw := by decide
    g := ![![![341313, 20054, 21135], ![-1028047, -183040, 0]], ![![-105481, -6197, -6533], ![317764, 56576, 0]]]
    h := ![![![62, -9, 0], ![170, 1, 0]], ![![55, -8, 0], ![151, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {14} * I17N1 =  Ideal.span {B.equivFun.symm ![34, 11, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 98 ![![19, 0, 0], ![5, 1, 0]]
  ![-422, 92, -5] ![![98, 0, 0], ![38, 1, 0]] where
    su := ![![1862, 0, 0], ![490, 98, 0]]
    hsu := by decide
    w := ![![-41356, 9016, -490], ![-17346, 2744, -98]]
    hw := by decide
    g := ![![![9, -926, -24], ![11, 2400, 0]], ![![54643, -15889831, -418191], ![-140895, 40982755, 0]]]
    h := ![![![-418, -83, -2], ![1504, 33, 0]], ![![-183, -38, -1], ![660, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {98} * I19N1 =  Ideal.span {B.equivFun.symm ![-422, 92, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 49 ![![23, 0, 0], ![2, 1, 0]]
  ![1951, 694, 72] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![1127, 0, 0], ![98, 49, 0]]
    hsu := by decide
    w := ![![95599, 34006, 3528], ![-2597, -931, -98]]
    hw := by decide
    g := ![![![2205178956, 505587386551, -45980714306], ![9823069801, 2253055000974, 0]], ![![159795659, 36636784918, -3331937436], ![711817039, 163264934366, 0]]]
    h := ![![![172901, 87146, 357], ![-1987386, -8139, 0]], ![![-4699, -2369, -10], ![54012, 228, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {49} * I23N1 =  Ideal.span {B.equivFun.symm ![1951, 694, 72]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![62, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![8, 2, 0], ![86, 6, 0]]
    hw := by decide
    g := ![![![41, 4, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-4, -1, 0], ![32, 0, 0]], ![![37, 9, 0], ![-276, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E31RS1 
