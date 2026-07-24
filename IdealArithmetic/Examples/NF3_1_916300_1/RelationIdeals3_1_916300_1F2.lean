import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F2
import IdealArithmetic.Examples.NF3_1_916300_1.ClassGroupData3_1_916300_1

set_option linter.all false

noncomputable section


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![1, 1, 0]]
  ![-103, -4, -2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![303, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-309, -12, -6], ![-306, -9, -6]]
    hw := by decide
    g := ![![![1, 1, -270], ![1, 808, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    h := ![![![-2, -2, -1], ![99, 99, 0]], ![![-2, -2, -1], ![100, 99, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-103, -4, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 33 ![![103, 0, 0], ![28, 1, 0]]
  ![-259, -10, 34] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![3399, 0, 0], ![924, 33, 0]]
    hsu := by decide
    w := ![![-8547, -330, 1122], ![2871, -1947, 330]]
    hw := by decide
    g := ![![![-168091, 21484339, 2389141], ![605202, -78843559, 0]], ![![-49987, 6387235, 710285], ![179945, -23439977, 0]]]
    h := ![![![-130781, -5268, -21], ![481078, 2197, 0]], ![![43577, 1749, 7], ![-160298, -711, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {33} * I103N0 =  Ideal.span {B.equivFun.symm ![-259, -10, 34]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 11 ![![103, 0, 0], ![-23, 1, 0]]
  ![377, -179, 17] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![1133, 0, 0], ![-253, 11, 0]]
    hsu := by decide
    w := ![![4147, -1969, 187], ![-25388, 7249, 506]]
    hw := by decide
    g := ![![![29990, 28261, -2206], ![60438, 0, 0]], ![![-5856, -5511, 430], ![-11785, 0, 0]]]
    h := ![![![1086, -45, 0], ![4847, 17, 0]], ![![-6424, 295, 0], ![-28668, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {11} * I103N1 =  Ideal.span {B.equivFun.symm ![377, -179, 17]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 9 ![![103, 0, 0], ![-6, 1, 0]]
  ![61918, 2251, 1178] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![927, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![557262, 20259, 10602], ![180234, 6552, 3429]]
    hw := by decide
    g := ![![![13, -20, 99], ![3, -844, 0]], ![![7, -2, -5], ![8, 41, 0]]]
    h := ![![![3345622, -559327, 319], ![57422858, -31679, 0]], ![![1082074, -180902, 103], ![18572266, -10228, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {9} * I103N2 =  Ideal.span {B.equivFun.symm ![61918, 2251, 1178]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS2 


noncomputable def E113RS1 : RelationCertificate Table 33 ![![113, 0, 0], ![-13, 1, 0]]
  ![19501, 709, 371] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![3729, 0, 0], ![-429, 33, 0]]
    hsu := by decide
    w := ![![643533, 23397, 12243], ![855096, 31086, 16269]]
    hw := by decide
    g := ![![![494, -178, 21], ![219, -115, 0]], ![![-62, 15, -3], ![-2, 12, 0]]]
    h := ![![![8741216, -680724, 645], ![75979839, -72514, 0]], ![![11614898, -904512, 857], ![100958274, -96348, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {33} * I113N1 =  Ideal.span {B.equivFun.symm ![19501, 709, 371]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E137RS0 : RelationCertificate Table 99 ![![137, 0, 0], ![61, 1, 0]]
  ![-1031, 34, 110] ![![99, 0, 0], ![-18, 7, 1]] where
    su := ![![13563, 0, 0], ![6039, 99, 0]]
    hsu := by decide
    w := ![![-102069, 3366, 10890], ![158400, -33957, -7029]]
    hw := by decide
    g := ![![![-209312651, 89194162, -11810638], ![44244220, 140616576, 0]], ![![-93937012, 40028941, -5300449], ![19856273, 63106571, 0]]]
    h := ![![![-4050, -115, 0], ![9079, 110, 0]], ![![6044, 67, -1], ![-13548, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {99} * I137N0 =  Ideal.span {B.equivFun.symm ![-1031, 34, 110]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 3 ![![137, 0, 0], ![-34, 1, 0]]
  ![-185, 49, 5] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![411, 0, 0], ![-102, 3, 0]]
    hsu := by decide
    w := ![![-555, 147, 15], ![765, -420, 54]]
    hw := by decide
    g := ![![![-27718, -907, 161686], ![-302, -486640, 0]], ![![6290, 205, -39715], ![71, 119504, 0]]]
    h := ![![![-18919, 592, -1], ![-76227, 142, 0]], ![![26197, -801, 1], ![105551, -119, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3} * I137N1 =  Ideal.span {B.equivFun.symm ![-185, 49, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 11 ![![137, 0, 0], ![-28, 1, 0]]
  ![99658, 3623, 1896] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![1507, 0, 0], ![-308, 11, 0]]
    hsu := by decide
    w := ![![1096238, 39853, 20856], ![90772, 3300, 1727]]
    hw := by decide
    g := ![![![-51437, -3222768, 1624253], ![-283621, -17866772, 0]], ![![10069, 630802, -317920], ![55520, 3497114, 0]]]
    h := ![![![33550970, -1240845, 1537], ![164156544, -208673, 0]], ![![2778172, -102740, 127], ![13592904, -17242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {11} * I137N2 =  Ideal.span {B.equivFun.symm ![99658, 3623, 1896]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS2 
