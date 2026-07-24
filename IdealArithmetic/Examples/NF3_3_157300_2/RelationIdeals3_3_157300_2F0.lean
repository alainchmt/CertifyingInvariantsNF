import IdealArithmetic.Examples.NF3_3_157300_2.PrimesBelow3_3_157300_2F0
import IdealArithmetic.Examples.NF3_3_157300_2.ClassGroupData3_3_157300_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3 ![![2, 0, 0], ![1, 1, 0]]
  ![-11, 29, -9] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![6, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-33, 87, -27], ![-144, -198, 69]]
    hw := by decide
    g := ![![![-445, -629, -81], ![-357, 0, 85]], ![![-384, -525, -149], ![-300, 0, 34]]]
    h := ![![![-22, -2, -72], ![-12, 45, 0]], ![![46, 37, 22], ![-133, -7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3} * I2N0 =  Ideal.span {B.equivFun.symm ![-11, 29, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, -1], ![2, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, -1], ![2, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS2 : RelationCertificate Table 9 ![![3, 0, 0], ![-15, -1, 1]]
  ![40, 5, -3] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![27, 0, 0], ![-135, -9, 9]]
    hsu := by decide
    w := ![![360, 45, -27], ![-9, -27, 9]]
    hw := by decide
    g := ![![![593180, 593073, 1824402], ![131806, -5473314, 160]], ![![-3559035, -3558395, -10946254], ![-790822, 32839400, -960]]]
    h := ![![![5, 106, -12], ![-47, -40, 0]], ![![9, -3, 0], ![3, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {9} * I3N2 =  Ideal.span {B.equivFun.symm ![40, 5, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![-2, 1, 0]]
  ![-8, -1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![15, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-24, -3, 0], ![-9, -9, -3]]
    hw := by decide
    g := ![![![-48, -67, -7], ![-36, 0, 10]], ![![22, 31, 4], ![21, 0, -5]]]
    h := ![![![30, -79, 126], ![-26, -210, 0]], ![![7, -17, 25], ![-2, -42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-8, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![-4, 1, 0]]
  ![-20, -25, -9] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-60, -75, -27], ![-207, -261, -93]]
    hw := by decide
    g := ![![![-166, -143, -12], ![-102, 0, 22]], ![![68, 57, 5], ![45, 0, -9]]]
    h := ![![![-300, 1545, -1179], ![260, 4320, 0]], ![![-1043, 5324, -4061], ![869, 14880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-20, -25, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![3, 1, 0]]
  ![10, -1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![39, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![30, -3, 0], ![9, 9, -3]]
    hw := by decide
    g := ![![![985, 1400, 139], ![795, 0, -208]], ![![189, 269, 27], ![156, 0, -40]]]
    h := ![![![-234, -769, -777], ![-105, 3367, 0]], ![![-63, -203, -205], ![-22, 888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![10, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![-2, 1, 0]]
  ![-4, 7, 3] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![39, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-12, 21, 9], ![57, 75, 27]]
    hw := by decide
    g := ![![![6585, 9374, 924], ![5321, 0, -1392]], ![![-5, -8, 3], ![-2, 0, 0]]]
    h := ![![![13, -24, 36], ![9, -155, 0]], ![![-30, 69, -102], ![18, 445, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![-4, 7, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E31RS1 : RelationCertificate Table 9 ![![31, 0, 0], ![-9, 1, 0]]
  ![-341, -10, 15] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![279, 0, 0], ![-81, 9, 0]]
    hsu := by decide
    w := ![![-3069, -90, 135], ![-81, 9, 0]]
    hw := by decide
    g := ![![![555841, 555866, 1708483], ![123530, -5125420, -36]], ![![-139640, -139646, -429212], ![-31031, 1287630, 9]]]
    h := ![![![-3344, 35527, -11865], ![2143, 122610, 0]], ![![-87, 943, -315], ![63, 3255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {9} * I31N1 =  Ideal.span {B.equivFun.symm ![-341, -10, 15]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
