import IdealArithmetic.Examples.NF3_1_236763_2.PrimesBelow3_1_236763_2F0
import IdealArithmetic.Examples.NF3_1_236763_2.ClassGroupData3_1_236763_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![48, -16, -3], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![48, -16, -3], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 0]]
  ![2525719, 94261, 134984] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![10102876, 377044, 539936], ![11584208, 432328, 619104]]
    hw := by decide
    g := ![![![35, -23, -19], ![15, 0, 0]], ![![-377, 197, -58], ![-135, 0, 0]]]
    h := ![![![1044527, -171202, 67492], ![436665, 0, 0]], ![![1197681, -196304, 77388], ![500690, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![2525719, 94261, 134984]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![-1, 1, 0]]
  ![187, 7, 10] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![374, 14, 20], ![484, 18, 26]]
    hw := by decide
    g := ![![![-1291, 417, 83], ![210, 0, 55]], ![![7, -3, -2], ![0, 0, 0]]]
    h := ![![![-1166, -1216, -4890], ![-15, 1835, 0]], ![![-1509, -1574, -6329], ![-19, 2375, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![187, 7, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![13, 3, 1]]
  ![-5217, 2233, 1456] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![20, 0, 0], ![52, 12, 4]]
    hsu := by decide
    w := ![![-20868, 8932, 5824], ![62464, -21716, 16408]]
    hw := by decide
    g := ![![![-12875015, 957473, -853022], ![-6198137, 0, 790]], ![![-52456938, 3895728, -3476474], ![-25254534, 0, 2133]]]
    h := ![![![-292, 620, 349], ![-289, 0, 0]], ![![687, -1648, 633], ![937, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![-5217, 2233, 1456]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![-1, 1, 0]]
  ![7, -3, -2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![14, -6, -4], ![-100, 36, -18]]
    hw := by decide
    g := ![![![942, -97, 9], ![-47, 0, -15]], ![![46, 51, 19], ![26, 0, 6]]]
    h := ![![![113, 111, 446], ![0, -279, 0]], ![![-794, -782, -3141], ![4, 1962, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![7, -3, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-6, 1, 0]]
  ![13, -5, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![52, -20, 0], ![16, -12, -40]]
    hw := by decide
    g := ![![![113602, -64241, -2833], ![40741, 0, -11382]], ![![-37844, 21411, 946], ![-13565, 0, 3794]]]
    h := ![![![119, -196, 528], ![-39, -1122, 0]], ![![38, -62, 166], ![-11, -354, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![13, -5, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 2 ![![17, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![34, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-6, 2, 0], ![2, 0, 8]]
    hw := by decide
    g := ![![![6260, -2038, -404], ![-1019, 0, -268]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-102, -2, -432], ![35, 918, 0]], ![![35, 0, 140], ![0, -297, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {2} * I17N2 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0], ![6, 1, 0]]
  ![1, -1, -4] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![76, 0, 0], ![24, 4, 0]]
    hsu := by decide
    w := ![![4, -4, -16], ![-188, 72, -4]]
    hw := by decide
    g := ![![![38974, -22207, -1003], ![13936, 0, -3939]], ![![14971, -8540, -387], ![5352, 0, -1515]]]
    h := ![![![105, 568, 508], ![70, -1207, 0]], ![![-4849, -25744, -23019], ![-2876, 54670, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![1, -1, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-2, 1, 0]]
  ![-370333, -13821, -19792] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-740666, -27642, -39584], ![-957866, -35748, -51192]]
    hw := by decide
    g := ![![![4061, -1323, -327], ![-661, 0, -182]], ![![-85, 30, 38], ![17, 0, 0]]]
    h := ![![![3845529, 1951911, 15532448], ![-249512, -44658262, 0]], ![![4973229, 2524308, 20087332], ![-322679, -57754279, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-370333, -13821, -19792]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-12, 1, 0]]
  ![2545, 95, 136] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![124, 0, 0], ![-48, 4, 0]]
    hsu := by decide
    w := ![![10180, 380, 544], ![11672, 436, 624]]
    hw := by decide
    g := ![![![-138093, 78203, 3464], ![-49495, 0, 13860]], ![![39451, -22343, -991], ![14143, 0, -3960]]]
    h := ![![![26717, -145506, 129776], ![-15004, -502865, 0]], ![![30628, -166831, 148796], ![-17215, -576565, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![2545, 95, 136]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
