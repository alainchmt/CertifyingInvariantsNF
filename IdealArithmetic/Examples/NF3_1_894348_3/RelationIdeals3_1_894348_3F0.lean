import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F0
import IdealArithmetic.Examples.NF3_1_894348_3.ClassGroupData3_1_894348_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 275 ![![2, 0, 0], ![0, 1, 0]]
  ![162, 13, 9] ![![275, 0, 0], ![51, 1, 0]] where
    su := ![![550, 0, 0], ![0, 275, 0]]
    hsu := by decide
    w := ![![44550, 3575, 2475], ![9900, 825, 550]]
    hw := by decide
    g := ![![![-1983, 2999803, 411743], ![10693, -16175618, 0]], ![![-2, 0, 0], ![9, 0, 0]]]
    h := ![![![81, 10, -6], ![-7, 3, 0]], ![![18, 2, -6], ![-1, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {275} * I2N0 =  Ideal.span {B.equivFun.symm ![162, 13, 9]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 11 ![![3, 0, 0], ![1, 1, 0]]
  ![1377, 127, 82] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![33, 0, 0], ![11, 11, 0]]
    hsu := by decide
    w := ![![15147, 1397, 902], ![9416, 869, 561]]
    hw := by decide
    g := ![![![-67, -2593, 4569], ![-202, -7180, 0]], ![![-35, -1165, 2055], ![-87, -3231, 0]]]
    h := ![![![750, 337, 53], ![-873, -11, 0]], ![![466, 209, 31], ![-542, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {11} * I3N0 =  Ideal.span {B.equivFun.symm ![1377, 127, 82]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-2, 2, 1]]
  ![389, 36, 23] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![125, 0, 0], ![-50, 50, 25]]
    hsu := by decide
    w := ![![9725, 900, 575], ![4575, 425, 275]]
    hw := by decide
    g := ![![![-8351, 5227840, 36653339], ![208780, -130904782, 0]], ![![3479, -2178267, -15272225], ![-86977, 54543660, 0]]]
    h := ![![![71, 14, 8], ![-17, 0, 0]], ![![33, 7, 4], ![-9, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![389, 36, 23]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![5, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 121 ![![7, 0, 0], ![0, 0, 1]]
  ![-5943, -548, -354] ![![121, 0, 0], ![-4, 1, 0]] where
    su := ![![847, 0, 0], ![0, 0, 121]]
    hsu := by decide
    w := ![![-719103, -66308, -42834], ![-40656, -3751, -2420]]
    hw := by decide
    g := ![![![3, 15, -28], ![117, 486, 0]], ![![0, -2, 3], ![78, -54, 0]]]
    h := ![![![-17, -1717980, -100], ![346, -32, 462512]], ![![-22, -97185, -6], ![22, -1, 26164]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {121} * I7N0 =  Ideal.span {B.equivFun.symm ![-5943, -548, -354]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![-4, -1, 1]]
  ![61, -15, 4] ![![121, 0, 0], ![-4, 1, 0]] where
    su := ![![1331, 0, 0], ![-484, -121, 121]]
    hsu := by decide
    w := ![![7381, -1815, 484], ![484, 121, -121]]
    hw := by decide
    g := ![![![65525, 240089405, -420185126], ![1982134, 7263200035, 0]], ![![-23760, -87066208, 152376259], ![-718741, -2633932477, 0]]]
    h := ![![![7, -1, 0], ![4, 0, 0]], ![![4, 1, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![61, -15, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-4, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![11, 0, 0], ![-4, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-4, 1, 0]]
    hw := by decide
    g := ![![![21, -5, 0], ![55, 0, 0]], ![![-4, 5, -7], ![-10, 11, 0]]]
    h := ![![![21, -5, 0], ![55, 0, 0]], ![![-4, 5, -7], ![-10, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 55 ![![13, 0, 0], ![0, 1, 0]]
  ![23621, 2179, 1407] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![715, 0, 0], ![0, 55, 0]]
    hsu := by decide
    w := ![![1299155, 119845, 77385], ![161590, 14905, 9625]]
    hw := by decide
    g := ![![![-9, -16, 28], ![29, -216, 0]], ![![8, -5, 7], ![12, -54, 0]]]
    h := ![![![1817, 332, 77], ![-2137, 58, 0]], ![![226, 40, 7], ![-249, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {55} * I13N0 =  Ideal.span {B.equivFun.symm ![23621, 2179, 1407]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 605 ![![17, 0, 0], ![1, 1, 0]]
  ![321, -71, 27] ![![605, 0, 0], ![-4, 1, 0]] where
    su := ![![10285, 0, 0], ![605, 605, 0]]
    hsu := by decide
    w := ![![194205, -42955, 16335], ![3630, 605, -605]]
    hw := by decide
    g := ![![![3, 6570, -11498], ![267, 993762, 0]], ![![3, 935, -1637], ![325, 141488, 0]]]
    h := ![![![36, 12, -5], ![-291, 16, 0]], ![![0, 0, 2], ![6, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {605} * I17N1 =  Ideal.span {B.equivFun.symm ![321, -71, 27]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 121 ![![19, 0, 0], ![8, 1, 0]]
  ![-302011, -27859, -17989] ![![121, 0, 0], ![-4, 1, 0]] where
    su := ![![2299, 0, 0], ![968, 121, 0]]
    hsu := by decide
    w := ![![-36543331, -3370939, -2176669], ![-2065954, -190575, -123057]]
    hw := by decide
    g := ![![![881, 3309883, -5792688], ![27340, 100130760, 0]], ![![432, 1590581, -2783708], ![13186, 48118393, 0]]]
    h := ![![![-161116681, -25057859, -4304892], ![382614366, 11682137, 0]], ![![-9108630, -1416631, -243375], ![21630862, 660444, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {121} * I19N0 =  Ideal.span {B.equivFun.symm ![-302011, -27859, -17989]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 121 ![![19, 0, 0], ![-7, 1, 0]]
  ![-3261, -301, -194] ![![121, 0, 0], ![-4, 1, 0]] where
    su := ![![2299, 0, 0], ![-847, 121, 0]]
    hsu := by decide
    w := ![![-394581, -36421, -23474], ![-22264, -2057, -1331]]
    hw := by decide
    g := ![![![5551, 20338190, -35594261], ![167931, 615272224, 0]], ![![-1865, -6840694, 11972030], ![-56390, -206945088, 0]]]
    h := ![![![-3493984, 541084, -41994], ![-9483205, 113956, 0]], ![![-197140, 30531, -2371], ![-535068, 6434, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {121} * I19N1 =  Ideal.span {B.equivFun.symm ![-3261, -301, -194]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 121 ![![19, 0, 0], ![-1, 1, 0]]
  ![-579, -54, -34] ![![121, 0, 0], ![-4, 1, 0]] where
    su := ![![2299, 0, 0], ![-121, 121, 0]]
    hsu := by decide
    w := ![![-70059, -6534, -4114], ![-3872, -363, -242]]
    hw := by decide
    g := ![![![3847, 14086500, -24653058], ![116374, 426145716, 0]], ![![-33, -119533, 209197], ![-984, -3616119, 0]]]
    h := ![![![-62, 29, -4], ![-599, 6, 0]], ![![-2, 1, -6], ![-6, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {121} * I19N2 =  Ideal.span {B.equivFun.symm ![-579, -54, -34]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 275 ![![23, 0, 0], ![-6, 1, 0]]
  ![1349, 351, -307] ![![275, 0, 0], ![51, 1, 0]] where
    su := ![![6325, 0, 0], ![-1650, 275, 0]]
    hsu := by decide
    w := ![![370975, 96525, -84425], ![12925, 19250, -13200]]
    hw := by decide
    g := ![![![-268, -60622, -8334], ![-83, 326744, 0]], ![![-101, 12092, 1657], ![223, -65236, 0]]]
    h := ![![![2023, -327, 4], ![7530, -57, 0]], ![![73, -8, -3], ![272, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {275} * I23N1 =  Ideal.span {B.equivFun.symm ![1349, 351, -307]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 55 ![![29, 0, 0], ![-3, 1, 0]]
  ![-129, 9, 2] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![1595, 0, 0], ![-165, 55, 0]]
    hsu := by decide
    w := ![![-7095, 495, 110], ![880, -165, 55]]
    hw := by decide
    g := ![![![5, -435, 762], ![8, -5985, 0]], ![![3, -10, 17], ![24, -133, 0]]]
    h := ![![![-153, 52, -5], ![-1436, 21, 0]], ![![20, -4, -6], ![188, 25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {55} * I29N1 =  Ideal.span {B.equivFun.symm ![-129, 9, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 
