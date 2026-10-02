import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.PrimesBelow2_2_8104_1F0
import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.ClassGroupData2_2_8104_1

namespace NF2_2_8104_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2187 ![![2, 0], ![0, 1]]
  ![80, 1] ![![2187, 0], ![2107, 1]] where
    su := ![![4374, 0], ![0, 2187]]
    hsu := by decide
    w := ![![174960, 2187], ![170586, 2187]]
    hw := by decide
    g := ![![![-2106, -1], ![2186, 0]], ![![-39, 0], ![40, 0]]]
    h := ![![![40, 0], ![1, 0]], ![![39, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2187} * I2N0 =  Ideal.span {B.equivFun.symm ![80, 1]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0], ![1, 1]]
  ![1, 0] ![![3, 0], ![1, 1]] where
    su := ![![3, 0], ![1, 1]]
    hsu := by decide
    w := ![![3, 0], ![1, 1]]
    hw := by decide
    g := ![![![0, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![0, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1594323 ![![3, 0], ![2, 1]]
  ![4213, 80] ![![1594323, 0], ![1414909, 1]] where
    su := ![![4782969, 0], ![3188646, 1594323]]
    hsu := by decide
    w := ![![6716882799, 127545840], ![5961173697, 113196933]]
    hw := by decide
    g := ![![![-1414838, -1], ![1594243, 0]], ![![-1199, 0], ![1351, 0]]]
    h := ![![![999, -176], ![608, 0]], ![![885, -157], ![542, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1594323} * I3N1 =  Ideal.span {B.equivFun.symm ![4213, 80]} * (J0 ^ 13) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 243 ![![5, 0], ![1, 1]]
  ![-83, 2] ![![243, 0], ![163, 1]] where
    su := ![![1215, 0], ![243, 243]]
    hsu := by decide
    w := ![![-20169, 486], ![-9477, 243]]
    hw := by decide
    g := ![![![-1, 0], ![2, 0]], ![![-8, 0], ![17, 0]]]
    h := ![![![-16, 1], ![-3, 0]], ![![-8, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {243} * I5N0 =  Ideal.span {B.equivFun.symm ![-83, 2]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 19683 ![![5, 0], ![4, 1]]
  ![-827, 17] ![![19683, 0], ![17416, 1]] where
    su := ![![98415, 0], ![78732, 19683]]
    hsu := by decide
    w := ![![-16277841, 334611], ![-14368590, 295245]]
    hw := by decide
    g := ![![![-17401, -1], ![19666, 0]], ![![-17258, -1], ![19504, 0]]]
    h := ![![![-103, 19], ![-78, 0]], ![![-94, 16], ![-65, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {19683} * I5N1 =  Ideal.span {B.equivFun.symm ![-827, 17]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E5RS1 


noncomputable def E23RS0 : RelationCertificate Table 81 ![![23, 0], ![5, 1]]
  ![-79, -2] ![![81, 0], ![1, 1]] where
    su := ![![1863, 0], ![405, 81]]
    hsu := by decide
    w := ![![-6399, -162], ![-4131, -81]]
    hw := by decide
    g := ![![![0, -1], ![79, 0]], ![![-2, 0], ![3, 0]]]
    h := ![![![-8, -1], ![21, 0]], ![![-7, -1], ![22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {81} * I23N0 =  Ideal.span {B.equivFun.symm ![-79, -2]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 59049 ![![23, 0], ![18, 1]]
  ![-107, 26] ![![59049, 0], ![56782, 1]] where
    su := ![![1358127, 0], ![1062882, 59049]]
    hsu := by decide
    w := ![![-6318243, 1535274], ![-6022998, 1476225]]
    hw := by decide
    g := ![![![-25, 0], ![26, 0]], ![![-24, 0], ![25, 0]]]
    h := ![![![-7, 1], ![3, 0]], ![![-6, 1], ![2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {59049} * I23N1 =  Ideal.span {B.equivFun.symm ![-107, 26]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 177147 ![![29, 0], ![5, 1]]
  ![2267, 1] ![![177147, 0], ![174880, 1]] where
    su := ![![5137263, 0], ![885735, 177147]]
    hsu := by decide
    w := ![![401592249, 177147], ![396454986, 177147]]
    hw := by decide
    g := ![![![-174879, -1], ![177146, 0]], ![![-77, 0], ![78, 0]]]
    h := ![![![73, -1], ![30, 0]], ![![72, -1], ![30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {177147} * I29N0 =  Ideal.span {B.equivFun.symm ![2267, 1]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 27 ![![29, 0], ![24, 1]]
  ![53, 1] ![![27, 0], ![1, 1]] where
    su := ![![783, 0], ![648, 27]]
    hsu := by decide
    w := ![![1431, 27], ![2079, 54]]
    hw := by decide
    g := ![![![1, -1], ![26, 0]], ![![-1, 0], ![1, 0]]]
    h := ![![![1, 0], ![1, 0]], ![![1, 0], ![2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {27} * I29N1 =  Ideal.span {B.equivFun.symm ![53, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E29RS1 


noncomputable def E37RS0 : RelationCertificate Table 177147 ![![37, 0], ![18, 1]]
  ![10031, -230] ![![177147, 0], ![174880, 1]] where
    su := ![![6554439, 0], ![3188646, 177147]]
    hsu := by decide
    w := ![![1776961557, -40743810], ![1753755300, -40212369]]
    hw := by decide
    g := ![![![-174653, -1], ![176917, 0]], ![![-174502, -1], ![176764, 0]]]
    h := ![![![203, -10], ![140, 0]], ![![216, -9], ![106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {177147} * I37N0 =  Ideal.span {B.equivFun.symm ![10031, -230]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 27 ![![37, 0], ![19, 1]]
  ![-55, 1] ![![27, 0], ![1, 1]] where
    su := ![![999, 0], ![513, 27]]
    hsu := by decide
    w := ![![-1485, 27], ![1971, -54]]
    hw := by decide
    g := ![![![-3, -1], ![26, 0]], ![![-4, -1], ![25, 0]]]
    h := ![![![-2, 0], ![1, 0]], ![![-16, -1], ![35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {27} * I37N1 =  Ideal.span {B.equivFun.symm ![-55, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E37RS1

end

end NF2_2_8104_1
