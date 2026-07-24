import IdealArithmetic.Examples.NF3_1_172019_1.PrimesBelow3_1_172019_1F0
import IdealArithmetic.Examples.NF3_1_172019_1.ClassGroupData3_1_172019_1

set_option linter.all false

noncomputable section


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-25, -2, 1]]
  ![-65, -22, 4] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![343, 0, 0], ![-1225, -98, 49]]
    hsu := by decide
    w := ![![-3185, -1078, 196], ![1764, 539, -98]]
    hw := by decide
    g := ![![![1, 0, 0], ![2, 0, 0]], ![![-431, -61678, 3085], ![-1056, -151164, 0]]]
    h := ![![![5, -2, 0], ![4, 0, 0]], ![![23, 3, -1], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![-65, -22, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![7, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 49 ![![11, 0, 0], ![1, 1, 0]]
  ![57, 11, -2] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![539, 0, 0], ![49, 49, 0]]
    hsu := by decide
    w := ![![2793, 539, -98], ![-1372, -245, 49]]
    hw := by decide
    g := ![![![7, -1540, 77], ![18, -3772, 0]], ![![1, -460, 23], ![2, -1127, 0]]]
    h := ![![![5, 5, 4], ![2, -46, 0]], ![![-3, -3, -2], ![5, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {49} * I11N1 =  Ideal.span {B.equivFun.symm ![57, 11, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 49 ![![13, 0, 0], ![-6, 1, 0]]
  ![-191067, -91505, -13128] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![637, 0, 0], ![-294, 49, 0]]
    hsu := by decide
    w := ![![-9362283, -4483745, -643272], ![2298492, 1100785, 157927]]
    hw := by decide
    g := ![![![-1987, -280098, 14011], ![-4890, -686444, 0]], ![![834, 114593, -5733], ![2011, 280818, 0]]]
    h := ![![![-60969045, 11784212, -273042], ![-132067753, 3536418, 0]], ![![14968236, -2893087, 67033], ![32423360, -868206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {49} * I13N0 =  Ideal.span {B.equivFun.symm ![-191067, -91505, -13128]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 49 ![![13, 0, 0], ![-5, 1, 0]]
  ![115, 54, 8] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![637, 0, 0], ![-245, 49, 0]]
    hsu := by decide
    w := ![![5635, 2646, 392], ![-1372, -637, -98]]
    hw := by decide
    g := ![![![27275, 3818555, -190996], ![66815, 9358800, 0]], ![![-9167, -1285581, 64302], ![-22454, -3150796, 0]]]
    h := ![![![34465, -7604, 144], ![89586, -1864, 0]], ![![-8386, 1855, -36], ![-21798, 466, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {49} * I13N1 =  Ideal.span {B.equivFun.symm ![115, 54, 8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 49 ![![13, 0, 0], ![-3, 1, 0]]
  ![-883, -424, -61] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![637, 0, 0], ![-147, 49, 0]]
    hsu := by decide
    w := ![![-43267, -20776, -2989], ![10584, 5096, 735]]
    hw := by decide
    g := ![![![9, -556, 28], ![39, -1356, 0]], ![![9, 117, -6], ![11, 285, 0]]]
    h := ![![![-144262, 50196, -726], ![-624841, 9377, 0]], ![![35292, -12278, 177], ![152860, -2286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {49} * I13N2 =  Ideal.span {B.equivFun.symm ![-883, -424, -61]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS2 


noncomputable def E17RS0 : RelationCertificate Table 7 ![![17, 0, 0], ![7, 1, 0]]
  ![-78185, -37444, -5372] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![119, 0, 0], ![49, 7, 0]]
    hsu := by decide
    w := ![![-547295, -262108, -37604], ![-701337, -335881, -48188]]
    hw := by decide
    g := ![![![-827, -106, 0], ![-130, 180, 0]], ![![-169, -38, -7], ![-26, 93, 0]]]
    h := ![![![-134102, -23706, -745], ![314507, 7293, 0]], ![![-171836, -30372, -954], ![403003, 9334, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {7} * I17N0 =  Ideal.span {B.equivFun.symm ![-78185, -37444, -5372]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 7 ![![17, 0, 0], ![-5, 1, 0]]
  ![-23, -29, 4] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![119, 0, 0], ![-35, 7, 0]]
    hsu := by decide
    w := ![![-161, -203, 28], ![441, 112, -21]]
    hw := by decide
    g := ![![![-46, -44, -26], ![-11, 159, 0]], ![![-9, 1, 5], ![4, -39, 0]]]
    h := ![![![-54, 10, 0], ![-179, 4, 0]], ![![174, -34, 0], ![579, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {7} * I17N1 =  Ideal.span {B.equivFun.symm ![-23, -29, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 7 ![![17, 0, 0], ![-3, 1, 0]]
  ![507, 40, -13] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![119, 0, 0], ![-21, 7, 0]]
    hsu := by decide
    w := ![![3549, 280, -91], ![-1001, 14, 14]]
    hw := by decide
    g := ![![![-215, -71, 14], ![-38, -204, 0]], ![![-63, -35, -10], ![-10, 39, 0]]]
    h := ![![![687, -222, 1], ![3724, -30, 0]], ![![-187, 63, -1], ![-1012, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {7} * I17N2 =  Ideal.span {B.equivFun.symm ![507, 40, -13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS2 


noncomputable def E31RS0 : RelationCertificate Table 7 ![![31, 0, 0], ![10, 1, 0]]
  ![-1499, -718, -103] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![217, 0, 0], ![70, 7, 0]]
    hsu := by decide
    w := ![![-10493, -5026, -721], ![-13447, -6440, -924]]
    hw := by decide
    g := ![![![212, -4674, -4770], ![-635, 33374, 0]], ![![85, -2761, -2818], ![-381, 19721, 0]]]
    h := ![![![-49889, -5984, -101], ![154506, 3028, 0]], ![![-63931, -7664, -129], ![197994, 3867, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {7} * I31N0 =  Ideal.span {B.equivFun.symm ![-1499, -718, -103]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS0 
