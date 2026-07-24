import IdealArithmetic.Examples.NF3_1_933907_1.PrimesBelow3_1_933907_1F3
import IdealArithmetic.Examples.NF3_1_933907_1.ClassGroupData3_1_933907_1

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 3 ![![139, 0, 0], ![60, 1, 0]]
  ![19, -2, 0] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![417, 0, 0], ![180, 3, 0]]
    hsu := by decide
    w := ![![57, -6, 0], ![-12, -6, 3]]
    hw := by decide
    g := ![![![9, 2, 0], ![8, 0, 0]], ![![4, 1, 0], ![4, 0, 0]]]
    h := ![![![1381, 23, 0], ![-3199, 0, 0]], ![![-436, -38, -1], ![1010, 70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {3} * I139N0 =  Ideal.span {B.equivFun.symm ![19, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 3 ![![139, 0, 0], ![-33, 1, 0]]
  ![-47, 9, -1] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![417, 0, 0], ![-99, 3, 0]]
    hsu := by decide
    w := ![![-141, 27, -3], ![-387, 90, -12]]
    hw := by decide
    g := ![![![0, -10, -1], ![-4, 0, 0]], ![![14, 1, 0], ![1, 0, 0]]]
    h := ![![![-1784, 70, -1], ![-7513, 69, 0]], ![![-4860, 179, -2], ![-20467, 137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {3} * I139N1 =  Ideal.span {B.equivFun.symm ![-47, 9, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 81 ![![139, 0, 0], ![-28, 1, 0]]
  ![38095, -2268, -484] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![11259, 0, 0], ![-2268, 81, 0]]
    hsu := by decide
    w := ![![3085695, -183708, -39204], ![11639781, -650673, -143289]]
    hw := by decide
    g := ![![![54011, 2790, 3430], ![-57866, 0, 0]], ![![-17611, -926, -1121], ![18937, 0, 0]]]
    h := ![![![31047505, -1108893, 0], ![154127325, -242, 0]], ![![117113411, -4182828, 1], ![581379301, -954, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {81} * I139N2 =  Ideal.span {B.equivFun.symm ![38095, -2268, -484]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E139RS2 


noncomputable def E151RS1 : RelationCertificate Table 27 ![![151, 0, 0], ![-61, 1, 0]]
  ![28450, -5720, 657] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![4077, 0, 0], ![-1647, 27, 0]]
    hsu := by decide
    w := ![![768150, -154440, 17739], ![-2925261, 588141, -67554]]
    hw := by decide
    g := ![![![21, 81, 9], ![14, 0, 0]], ![![78, -40, -4], ![35, 0, 0]]]
    h := ![![![974398, -17288, 47], ![2411568, -3220, 0]], ![![-3710361, 66041, -186], ![-9182888, 12792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {27} * I151N1 =  Ideal.span {B.equivFun.symm ![28450, -5720, 657]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E151RS1 


noncomputable def E167RS0 : RelationCertificate Table 81 ![![167, 0, 0], ![30, 1, 0]]
  ![81182, -4682, -1015] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![13527, 0, 0], ![2430, 81, 0]]
    hsu := by decide
    w := ![![6575742, -379242, -82215], ![24238845, -1311876, -293706]]
    hw := by decide
    g := ![![![233856, 12198, 14870], ![-251047, 0, 0]], ![![17700, 889, 1120], ![-18856, 0, 0]]]
    h := ![![![-15937874, -530701, 33], ![88723538, -3263, 0]], ![![-58742935, -1955934, 128], ![327012313, -12501, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {81} * I167N0 =  Ideal.span {B.equivFun.symm ![81182, -4682, -1015]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E167RS0 


noncomputable def E167RS1 : RelationCertificate Table 3 ![![167, 0, 0], ![35, 1, 0]]
  ![-59108, 11884, -1365] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![501, 0, 0], ![105, 3, 0]]
    hsu := by decide
    w := ![![-177324, 35652, -4095], ![-629661, 126597, -14541]]
    hw := by decide
    g := ![![![89, -69, 11], ![-860, 0, 0]], ![![43, -16, 3], ![-226, 0, 0]]]
    h := ![![![-3988404, -120800, -393], ![19028696, 32133, 0]], ![![-14162296, -428864, -1391], ![67568387, 113725, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {3} * I167N1 =  Ideal.span {B.equivFun.symm ![-59108, 11884, -1365]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 3 ![![167, 0, 0], ![-66, 1, 0]]
  ![35, 2, 0] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![501, 0, 0], ![-198, 3, 0]]
    hsu := by decide
    w := ![![105, 6, 0], ![-4308, 222, 51]]
    hw := by decide
    g := ![![![13, -18, 4], ![-4, 0, 0]], ![![74, 5, -3], ![5, 0, 0]]]
    h := ![![![6469, -98, 0], ![16368, 0, 0]], ![![-261616, 4520, -17], ![-661946, 1428, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {3} * I167N2 =  Ideal.span {B.equivFun.symm ![35, 2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS2 


noncomputable def E173RS1 : RelationCertificate Table 9 ![![173, 0, 0], ![73, 1, 0]]
  ![67205, -13512, 1552] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![1557, 0, 0], ![657, 9, 0]]
    hsu := by decide
    w := ![![604845, -121608, 13968], ![4226544, -849771, 97605]]
    hw := by decide
    g := ![![![249, -651, -3], ![-1589, 0, 0]], ![![101, -308, -1], ![-759, 0, 0]]]
    h := ![![![-10030101, -133670, 112], ![23770886, -8912, 0]], ![![-70088146, -933747, 791], ![166105738, -62999, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {9} * I173N1 =  Ideal.span {B.equivFun.symm ![67205, -13512, 1552]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 27 ![![179, 0, 0], ![-67, 1, 0]]
  ![-25073, 5041, -579] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![4833, 0, 0], ![-1809, 27, 0]]
    hsu := by decide
    w := ![![-676971, 136107, -15633], ![2577960, -518319, 59535]]
    hw := by decide
    g := ![![![522, 252, -9], ![-1394, 0, 0]], ![![-81, -91, 2], ![479, 0, 0]]]
    h := ![![![-2725, -1440457, 43649], ![-6906, -3906875, 0]], ![![10534, 5485377, -166219], ![26718, 14877703, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {27} * I179N1 =  Ideal.span {B.equivFun.symm ![-25073, 5041, -579]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E179RS1 


noncomputable def E181RS1 : RelationCertificate Table 3 ![![181, 0, 0], ![73, 1, 0]]
  ![4162, -1280, -165] ![![3, 0, 0], ![-80, 4, 1]] where
    su := ![![543, 0, 0], ![219, 3, 0]]
    hsu := by decide
    w := ![![12486, -3840, -495], ![1067595, -50847, -12183]]
    hw := by decide
    g := ![![![-46437, -1233955, 291885], ![-308650, 0, 0]], ![![-14271, -378964, 89642], ![-94791, 0, 0]]]
    h := ![![![-107700, -1338, 3], ![267094, -354, 0]], ![![-9127451, -107711, 449], ![22635952, -42665, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {3} * I181N1 =  Ideal.span {B.equivFun.symm ![4162, -1280, -165]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 27 ![![191, 0, 0], ![-50, 1, 0]]
  ![-726355, 146038, -16774] ![![27, 0, 0], ![-89, 10, 1]] where
    su := ![![5157, 0, 0], ![-1350, 27, 0]]
    hsu := by decide
    w := ![![-19611585, 3943026, -452898], ![74685105, -15015888, 1724733]]
    hw := by decide
    g := ![![![2610, 1336, -61], ![-7991, 0, 0]], ![![-523, -285, 13], ![1713, 0, 0]]]
    h := ![![![-396905, -306681340, 12517870], ![-1501650, -1195464972, 0]], ![![1511615, 1167908053, -47670723], ![5719047, 4552585986, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {27} * I191N1 =  Ideal.span {B.equivFun.symm ![-726355, 146038, -16774]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 243 ![![193, 0, 0], ![-39, 1, 0]]
  ![28111, -1976, -390] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![46899, 0, 0], ![-9477, 243, 0]]
    hsu := by decide
    w := ![![6830973, -480168, -94770], ![9721215, -629613, -129033]]
    hw := by decide
    g := ![![![32202, -5503, 899], ![-12355, 0, 0]], ![![-9303, 1563, -264], ![3910, 0, 0]]]
    h := ![![![314930464, -8329519, 13386], ![1558501319, -1291944, 0]], ![![448176012, -11853722, 19051], ![2217895649, -1838687, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {243} * I193N1 =  Ideal.span {B.equivFun.symm ![28111, -1976, -390]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E193RS1 
