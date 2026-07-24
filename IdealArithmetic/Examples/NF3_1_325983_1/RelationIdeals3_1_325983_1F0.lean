import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F0
import IdealArithmetic.Examples.NF3_1_325983_1.ClassGroupData3_1_325983_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2187 ![![3, 0, 0], ![1, 1, 0]]
  ![55, 21, -28] ![![2187, 0, 0], ![-543, 1, 0]] where
    su := ![![6561, 0, 0], ![2187, 2187, 0]]
    hsu := by decide
    w := ![![120285, 45927, -61236], ![-32805, -10935, 15309]]
    hw := by decide
    g := ![![![516, -2277, 21], ![2078, -9184, 0]], ![![490, -4553, 42], ![1973, -18368, 0]]]
    h := ![![![-27004, -27012, -1], ![81067, -5, 0]], ![![7942, 7944, -1], ![-23841, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2187} * I3N1 =  Ideal.span {B.equivFun.symm ![55, 21, -28]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6561 ![![5, 0, 0], ![0, 1, 0]]
  ![6040, 318, 305] ![![6561, 0, 0], ![-543, 1, 0]] where
    su := ![![32805, 0, 0], ![0, 6561, 0]]
    hsu := by decide
    w := ![![39628440, 2086398, 2001105], ![-3247695, -170586, -164025]]
    hw := by decide
    g := ![![![237038, 18918132765, -174521524], ![2864100, 229007143792, 0]], ![![1402362, 111926358793, -1032531009], ![16944562, 1354887190010, 0]]]
    h := ![![![1208, 61, 61], ![13, 0, 0]], ![![-99, -5, -5], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6561} * I5N0 =  Ideal.span {B.equivFun.symm ![6040, 318, 305]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2187 ![![5, 0, 0], ![-1, 1, 0]]
  ![281, -12, 16] ![![2187, 0, 0], ![-543, 1, 0]] where
    su := ![![10935, 0, 0], ![-2187, 2187, 0]]
    hsu := by decide
    w := ![![614547, -26244, 34992], ![-150903, 6561, -8748]]
    hw := by decide
    g := ![![![462094, 4320613937, -39858070], ![1861141, 17433919818, 0]], ![![262679654284, 2456426290045578, -22660763595958], ![1057974961177, 9911817996872030, 0]]]
    h := ![![![22909, -2180, -224], ![-5016, 0, -1136]], ![![-5626, 535, 55], ![1234, 0, 279]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2187} * I5N1 =  Ideal.span {B.equivFun.symm ![281, -12, 16]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 729 ![![7, 0, 0], ![0, 1, 0]]
  ![-112, -3, 4] ![![729, 0, 0], ![186, 1, 0]] where
    su := ![![5103, 0, 0], ![0, 729, 0]]
    hsu := by decide
    w := ![![-81648, -2187, 2916], ![-20412, -729, 729]]
    hw := by decide
    g := ![![![-84, 6769, 181], ![329, -26390, 0]], ![![1, 0, 0], ![-4, 0, 0]]]
    h := ![![![-16, -3, -8], ![6, 12, 0]], ![![-4, -1, -2], ![3, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {729} * I7N0 =  Ideal.span {B.equivFun.symm ![-112, -3, 4]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 27 ![![7, 0, 0], ![-1, 1, 0]]
  ![205, 12, 11] ![![27, 0, 0], ![-3, 1, 0]] where
    su := ![![189, 0, 0], ![-27, 27, 0]]
    hsu := by decide
    w := ![![5535, 324, 297], ![540, 27, 27]]
    hw := by decide
    g := ![![![-7, -2047, 5123], ![-56, -27664, 0]], ![![2, 269, -674], ![12, 3640, 0]]]
    h := ![![![29, 2, -22], ![-2, 33, 0]], ![![3, 0, -2], ![1, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {27} * I7N1 =  Ideal.span {B.equivFun.symm ![205, 12, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 27 ![![11, 0, 0], ![13, 5, 1]]
  ![76, 3, 5] ![![27, 0, 0], ![-3, 1, 0]] where
    su := ![![297, 0, 0], ![351, 135, 27]]
    hsu := by decide
    w := ![![2052, 81, 135], ![297, 0, 0]]
    hw := by decide
    g := ![![![0, 20, -50], ![1, 270, 0]], ![![2, 23, -59], ![16, 319, 0]]]
    h := ![![![1, -2, 0], ![5, 0, 0]], ![![-12, -5, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {27} * I11N0 =  Ideal.span {B.equivFun.symm ![76, 3, 5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 531441 ![![11, 0, 0], ![-3, 1, 0]]
  ![-35075, -1662, -1429] ![![531441, 0, 0], ![-118641, 1, 0]] where
    su := ![![5845851, 0, 0], ![-1594323, 531441, 0]]
    hsu := by decide
    w := ![![-18640293075, -883254942, -759429189], ![4161183030, 197164611, 169529679]]
    hw := by decide
    g := ![![![-117520335103, -293704606878027637, 12377975677639], ![-526421088894, -1315632754420029556, 0]], ![![-103817357892, -259458407943905169, 10934693524308], ![-465039914494, -1162228892250353564, 0]]]
    h := ![![![-11871676351, 3957224572, -969], ![-43529468262, 1846, 0]], ![![2650185516, -883394975, 214], ![9717344282, -407, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {531441} * I11N1 =  Ideal.span {B.equivFun.symm ![-35075, -1662, -1429]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 243 ![![13, 0, 0], ![-1, 1, 0]]
  ![19, -6, 8] ![![243, 0, 0], ![-57, 1, 0]] where
    su := ![![3159, 0, 0], ![-243, 243, 0]]
    hsu := by decide
    w := ![![4617, -1458, 1944], ![-243, 243, -486]]
    hw := by decide
    g := ![![![35, 5342, -477], ![148, 23183, 0]], ![![17, -45, 4], ![72, -194, 0]]]
    h := ![![![4, -3, -4], ![33, 12, 0]], ![![0, 0, -4], ![1, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {243} * I13N1 =  Ideal.span {B.equivFun.symm ![19, -6, 8]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 59049 ![![19, 0, 0], ![6, 1, 0]]
  ![-869, 543, 5] ![![59049, 0, 0], ![-543, 1, 0]] where
    su := ![![1121931, 0, 0], ![354294, 59049, 0]]
    hsu := by decide
    w := ![![-51313581, 32063607, 295245], ![472392, -295245, 0]]
    hw := by decide
    g := ![![![25, -121616670, 1121925], ![2718, -13249709860, 0]], ![![10, -44806056, 413340], ![1087, -4881462730, 0]]]
    h := ![![![-127834763, -27085896, -4128670], ![404809938, 15688947, 0]], ![![1176824, 249344, 38005], ![-3726608, -144419, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {59049} * I19N0 =  Ideal.span {B.equivFun.symm ![-869, 543, 5]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E19RS0 


noncomputable def E23RS1 : RelationCertificate Table 243 ![![23, 0, 0], ![-8, 1, 0]]
  ![131, -3, 4] ![![243, 0, 0], ![-57, 1, 0]] where
    su := ![![5589, 0, 0], ![-1944, 243, 0]]
    hsu := by decide
    w := ![![31833, -729, 972], ![-7047, 243, -243]]
    hw := by decide
    g := ![![![1564044, 1709357743, -152623677], ![6667766, 7417510702, 0]], ![![-520259, -568638415, 50772102], ![-2217946, -2467524157, 0]]]
    h := ![![![365, -42, -2], ![1033, 10, 0]], ![![-67, 11, -2], ![-189, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {243} * I23N1 =  Ideal.span {B.equivFun.symm ![131, -3, 4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E23RS1 
