import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F3
import IdealArithmetic.Examples.NF3_3_806284_1.ClassGroupData3_3_806284_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![35, 1, 0]]
  ![498, 5, -10] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![278, 0, 0], ![70, 2, 0]]
    hsu := by decide
    w := ![![996, 10, -20], ![-532, -2, 10]]
    hw := by decide
    g := ![![![-105, -53, -15], ![-79, 0, 0]], ![![-35, -18, -5], ![-25, 0, 0]]]
    h := ![![![62, -33, -2], ![-232, 134, 0]], ![![-84, -21, -1], ![326, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![498, 5, -10]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 


noncomputable def E149RS0 : RelationCertificate Table 2 ![![149, 0, 0], ![63, 1, 0]]
  ![11301, 124, -229] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![298, 0, 0], ![126, 2, 0]]
    hsu := by decide
    w := ![![22602, 248, -458], ![-324288, -3592, 6578]]
    hw := by decide
    g := ![![![33, -1410, -314], ![137, 0, 0]], ![![17, -681, -156], ![59, -3, 0]]]
    h := ![![![1279605, 23464, 97], ![-3026188, -7341, 0]], ![![-18359766, -337534, -1419], ![43419730, 107360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N0 : Ideal.span {2} * I149N0 =  Ideal.span {B.equivFun.symm ![11301, 124, -229]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS0 


noncomputable def E149RS1 : RelationCertificate Table 2 ![![149, 0, 0], ![-58, 1, 0]]
  ![1521, 980, 163] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![298, 0, 0], ![-116, 2, 0]]
    hsu := by decide
    w := ![![3042, 1960, 326], ![15648, 10084, 1678]]
    hw := by decide
    g := ![![![116, -367, 180], ![-1171, 0, 0]], ![![-32, 168, -73], ![464, -3, 0]]]
    h := ![![![22413, -377, 1], ![57552, 7, 0]], ![![115056, -2045, 9], ![295440, -251, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![1521, 980, 163]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS1 


noncomputable def E149RS2 : RelationCertificate Table 2 ![![149, 0, 0], ![-5, 1, 0]]
  ![29, 18, 3] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![298, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![58, 36, 6], ![250, 184, 32]]
    hw := by decide
    g := ![![![14, -8, 2], ![-7, 0, 0]], ![![30, 21, -1], ![-7, -3, 0]]]
    h := ![![![41, -6, -1], ![1216, 76, 0]], ![![175, -34, 0], ![5190, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N2 : Ideal.span {2} * I149N2 =  Ideal.span {B.equivFun.symm ![29, 18, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS2 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![-13, 1, 0]]
  ![-7, -6, -1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![326, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-14, -12, -2], ![-174, -64, -8]]
    hw := by decide
    g := ![![![14, -5, 1], ![-3, 0, 0]], ![![27, -18, -1], ![11, 3, 0]]]
    h := ![![![-144, 17, -1], ![-1805, 81, 0]], ![![-2098, 173, -2], ![-26299, 161, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![-7, -6, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS1 


noncomputable def E173RS1 : RelationCertificate Table 2 ![![173, 0, 0], ![-73, 1, 0]]
  ![-63, -41, -7] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![346, 0, 0], ![-146, 2, 0]]
    hsu := by decide
    w := ![![-126, -82, -14], ![-784, -502, -82]]
    hw := by decide
    g := ![![![3105, -588, -76], ![1261, 0, 0]], ![![-1349, 254, 33], ![-545, 0, 0]]]
    h := ![![![-5599, 111, -1], ![-13268, 83, 0]], ![![-34968, 505, -1], ![-82864, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {2} * I173N1 =  Ideal.span {B.equivFun.symm ![-63, -41, -7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E173RS1 


noncomputable def E181RS1 : RelationCertificate Table 2 ![![181, 0, 0], ![47, 1, 0]]
  ![16127, 178, -327] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![362, 0, 0], ![94, 2, 0]]
    hsu := by decide
    w := ![![32254, 356, -654], ![-462622, -5104, 9380]]
    hw := by decide
    g := ![![![16, 134, 24], ![-13, 0, 0]], ![![5, 61, 8], ![-13, -3, 0]]]
    h := ![![![819330, 19083, 67], ![-3154949, -6227, 0]], ![![-11752736, -273995, -972], ![45255615, 90311, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {2} * I181N1 =  Ideal.span {B.equivFun.symm ![16127, 178, -327]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-43, 1, 0]]
  ![58, 37, 6] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![382, 0, 0], ![-86, 2, 0]]
    hsu := by decide
    w := ![![116, 74, 12], ![676, 438, 74]]
    hw := by decide
    g := ![![![2241, -423, -55], ![909, 0, 0]], ![![-530, 99, 13], ![-213, 0, 0]]]
    h := ![![![1972, -45, 0], ![8758, 3, 0]], ![![11406, -239, -1], ![50656, 114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![58, 37, 6]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E191RS1 
