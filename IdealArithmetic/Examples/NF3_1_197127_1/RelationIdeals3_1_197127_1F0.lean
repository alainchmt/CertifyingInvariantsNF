import IdealArithmetic.Examples.NF3_1_197127_1.PrimesBelow3_1_197127_1F0
import IdealArithmetic.Examples.NF3_1_197127_1.ClassGroupData3_1_197127_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 25 ![![3, 0, 0], ![-6, -1, 1]]
  ![-6, -1, 1] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![75, 0, 0], ![-150, -25, 25]]
    hsu := by decide
    w := ![![-150, -25, 25], ![75, 0, 0]]
    hw := by decide
    g := ![![![-2, 2, 6], ![1, -50, 0]], ![![4, -6, -15], ![25, 125, 0]]]
    h := ![![![-1504, 4066, -366], ![1543, 0, -444]], ![![759, -2032, 182], ![-768, 0, 222]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {25} * I3N0 =  Ideal.span {B.equivFun.symm ![-6, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 3125 ![![5, 0, 0], ![-6, -1, 1]]
  ![1007, 22, -47] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![15625, 0, 0], ![-18750, -3125, 3125]]
    hsu := by decide
    w := ![![3146875, 68750, -146875], ![-606250, -12500, 28125]]
    hw := by decide
    g := ![![![225, -30749, 154], ![1444, -160416, 0]], ![![455, 38136, -191], ![2045, 198960, 0]]]
    h := ![![![85, -15, 10], ![-97, 0, 0]], ![![-16, 3, -2], ![19, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3125} * I5N0 =  Ideal.span {B.equivFun.symm ![1007, 22, -47]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![-11, 12, 36], ![0, -60, 0]], ![![-4, 4, 12], ![1, -20, 0]]]
    h := ![![![-11, 12, 36], ![0, -60, 0]], ![![-4, 4, 12], ![1, -20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![43, 3, -3] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![1075, 75, -75], ![-175, 25, 0]]
    hw := by decide
    g := ![![![60, -59, -177], ![5, 1476, 0]], ![![12, -11, -33], ![6, 276, 0]]]
    h := ![![![0, -6, 18], ![2, -43, 0]], ![![0, 1, -3], ![1, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![43, 3, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E13RS1 : RelationCertificate Table 125 ![![13, 0, 0], ![-6, 1, 0]]
  ![108, 18, 7] ![![125, 0, 0], ![27, 1, 0]] where
    su := ![![1625, 0, 0], ![-750, 125, 0]]
    hsu := by decide
    w := ![![13500, 2250, 875], ![3500, 625, 250]]
    hw := by decide
    g := ![![![-131, 3267, 377], ![26, -15708, 0]], ![![33, -1231, -142], ![66, 5916, 0]]]
    h := ![![![25404, 172598, -74021], ![1564, 320760, 0]], ![![6544, 44457, -19066], ![404, 82620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {125} * I13N1 =  Ideal.span {B.equivFun.symm ![108, 18, 7]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3125 ![![17, 0, 0], ![-8, 1, 0]]
  ![2547, 487, 238] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![53125, 0, 0], ![-25000, 3125, 0]]
    hsu := by decide
    w := ![![7959375, 1521875, 743750], ![-1503125, -287500, -140625]]
    hw := by decide
    g := ![![![989665129, 592774259657, -2968819331], ![306675, 3092520136452, 0]], ![![-439844653, -263451690773, 1319457550], ![-133098, -1374434947911, 0]]]
    h := ![![![1510, 12223, -4051], ![11, 23035, 0]], ![![-279, -2309, 765], ![11, -4350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3125} * I17N1 =  Ideal.span {B.equivFun.symm ![2547, 487, 238]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E17RS1 


noncomputable def E31RS0 : RelationCertificate Table 25 ![![31, 0, 0], ![5, 1, 0]]
  ![19, -1, 1] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![775, 0, 0], ![125, 25, 0]]
    hsu := by decide
    w := ![![475, -25, 25], ![125, 25, 0]]
    hw := by decide
    g := ![![![-174, 176, 527], ![-6, -4392, 0]], ![![-32, 32, 96], ![1, -800, 0]]]
    h := ![![![-231, 921, 691], ![8, -7140, 0]], ![![-60, 240, 180], ![1, -1860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {25} * I31N0 =  Ideal.span {B.equivFun.symm ![19, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 25 ![![31, 0, 0], ![-4, 1, 0]]
  ![37, 2, -2] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![775, 0, 0], ![-100, 25, 0]]
    hsu := by decide
    w := ![![925, 50, -50], ![-100, 25, 0]]
    hw := by decide
    g := ![![![3833, -3852, -11536], ![168, 96134, 0]], ![![-618, 621, 1860], ![-24, -15500, 0]]]
    h := ![![![-20978, -104461, 62689], ![-642, -647787, 0]], ![![2301, 11442, -6867], ![94, 70959, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {25} * I31N1 =  Ideal.span {B.equivFun.symm ![37, 2, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 25 ![![31, 0, 0], ![-1, 1, 0]]
  ![31, 1, -1] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![775, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![775, 25, -25], ![-25, 25, 0]]
    hw := by decide
    g := ![![![134, -134, -401], ![8, 3342, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-298, -600, 899], ![21, -9290, 0]], ![![10, 20, -30], ![1, 310, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {25} * I31N2 =  Ideal.span {B.equivFun.symm ![31, 1, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS2 
