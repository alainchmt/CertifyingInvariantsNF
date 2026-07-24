import IdealArithmetic.Examples.NF3_1_32780_1.PrimesBelow3_1_32780_1F0
import IdealArithmetic.Examples.NF3_1_32780_1.ClassGroupData3_1_32780_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![-97, 4, 10] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-291, 12, 30], ![429, -129, 30]]
    hw := by decide
    g := ![![![922, 177, 160], ![-245, -2, 0]], ![![1569, 304, 270], ![-421, -2, 0]]]
    h := ![![![485, 466, -1290], ![158, 776, 0]], ![![-715, -700, 1910], ![-231, -1144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![-97, 4, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![1, 1, 0]]
  ![1373, 133, 214] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![27, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![12357, 1197, 1926], ![9756, 945, 1521]]
    hw := by decide
    g := ![![![1, -2, 3], ![3, -4, 0]], ![![1, 0, 18], ![8, -36, 0]]]
    h := ![![![-302, -302, 2138], ![-201, -1240, 0]], ![![-239, -239, 1688], ![-157, -979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![1373, 133, 214]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![-3, -6, 10], ![0, -6, 0]], ![![2, 3, -5], ![1, 3, 0]]]
    h := ![![![-3, -6, 10], ![0, -6, 0]], ![![2, 3, -5], ![1, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![0, 0, 1]]
  ![1931, 187, 301] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![15, 0, 0], ![0, 0, 3]]
    hsu := by decide
    w := ![![5793, 561, 903], ![7929, 768, 1236]]
    hw := by decide
    g := ![![![-4, -44, 76], ![-13, -48, 0]], ![![-17, 1, -7], ![7, 8, 0]]]
    h := ![![![-49, 63, 1600], ![-7827, 64, 0]], ![![-63, 86, 2190], ![-10712, 87, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![1931, 187, 301]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 9 ![![5, 0, 0], ![-1, 1, 0]]
  ![11, 1, 1] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![45, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![99, 9, 9], ![54, 9, 9]]
    hw := by decide
    g := ![![![-5, -1, 10], ![8, -18, 0]], ![![-1, 0, 1], ![2, -2, 0]]]
    h := ![![![12083, -247, 370], ![-2462, 0, -1849]], ![![6463, -132, 198], ![-1317, 0, -989]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![11, 1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 9 ![![11, 0, 0], ![2, 1, 0]]
  ![301, 29, 47] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![99, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![2709, 261, 423], ![2142, 207, 333]]
    hw := by decide
    g := ![![![-3355563, 81844, 8798118], ![-736583, -15836614, 0]], ![![-457786, 11165, 1200282], ![-100484, -2160507, 0]]]
    h := ![![![30683, -501, -79153], ![5540, 174146, 0]], ![![24260, -396, -62583], ![4379, 137690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {9} * I11N0 =  Ideal.span {B.equivFun.symm ![301, 29, 47]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![-1, 1, 0]]
  ![13, -1, -1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![39, -3, -3], ![-45, 18, -6]]
    hw := by decide
    g := ![![![32, 24, -34], ![-1, 22, 0]], ![![4, -2, 6], ![-1, -3, 0]]]
    h := ![![![743, 1104, -1846], ![38, 4061, 0]], ![![-884, -1315, 2198], ![-37, -4836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![13, -1, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 27 ![![13, 0, 0], ![-4, 1, 0]]
  ![143, 13, 22] ![![27, 0, 0], ![11, 1, 0]] where
    su := ![![351, 0, 0], ![-108, 27, 0]]
    hsu := by decide
    w := ![![3861, 351, 594], ![2295, 216, 351]]
    hw := by decide
    g := ![![![-2634061, 12962469, 7189169], ![-593032, -38821514, 0]], ![![817462, -4022844, -2231126], ![184060, 12048081, 0]]]
    h := ![![![1159, 3520, -2926], ![-75, 7612, 0]], ![![685, 2080, -1729], ![-44, 4498, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {27} * I13N1 =  Ideal.span {B.equivFun.symm ![143, 13, 22]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![-9, 1, 0]]
  ![5, 1, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![57, 0, 0], ![-27, 3, 0]]
    hsu := by decide
    w := ![![15, 3, 3], ![27, 0, 6]]
    hw := by decide
    g := ![![![-28, -38, 64], ![-1, -38, 0]], ![![16, 18, -32], ![3, 19, 0]]]
    h := ![![![50, 255, -116], ![7, 441, 0]], ![![90, 511, -232], ![-7, 882, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![5, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 27 ![![29, 0, 0], ![0, 1, 0]]
  ![-235, 13, 22] ![![27, 0, 0], ![11, 1, 0]] where
    su := ![![783, 0, 0], ![0, 27, 0]]
    hsu := by decide
    w := ![![-6345, 351, 594], ![-1863, -162, 351]]
    hw := by decide
    g := ![![![-5073224355, 24965860625, 13846420347], ![-1142207656, -74770669934, 0]], ![![87471813, -430457922, -238738069], ![19693803, 1289185562, 0]]]
    h := ![![![12455, 12448, -31157], ![451, 180715, 0]], ![![3657, 3654, -9148], ![150, 53061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {27} * I29N1 =  Ideal.span {B.equivFun.symm ![-235, 13, 22]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E29RS1 
