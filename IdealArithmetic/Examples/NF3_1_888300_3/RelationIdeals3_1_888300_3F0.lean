import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F0
import IdealArithmetic.Examples.NF3_1_888300_3.ClassGroupData3_1_888300_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 21 ![![2, 0, 0], ![0, 1, 0]]
  ![102, 7, -1] ![![21, 0, 0], ![-104, -5, 1]] where
    su := ![![42, 0, 0], ![0, 21, 0]]
    hsu := by decide
    w := ![![2142, 147, -21], ![-1848, -168, 21]]
    hw := by decide
    g := ![![![96, 4, -1], ![20, 0, 0]], ![![47, -2, -1], ![13, 0, 0]]]
    h := ![![![51, 2, 0], ![3, -1, 0]], ![![-44, -4, 0], ![0, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {21} * I2N0 =  Ideal.span {B.equivFun.symm ![102, 7, -1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 49 ![![3, 0, 0], ![-1, 1, 0]]
  ![207, 57, 4] ![![147, 0, 0], ![-114, -1, 1]] where
    su := ![![147, 0, 0], ![-49, 49, 0]]
    hsu := by decide
    w := ![![30429, 8379, 588], ![15092, 4165, 294]]
    hw := by decide
    g := ![![![110282279, 8129286, 340178], ![-85577907, -35571750, 0]], ![![-55140961, -4064638, -170090], ![42789070, 17785860, 0]]]
    h := ![![![452, -211, 27], ![735, -69, 0]], ![![224, -104, 13], ![364, -33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {49} * I3N0 =  Ideal.span {B.equivFun.symm ![207, 57, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 21 ![![5, 0, 0], ![0, 1, 0]]
  ![5, 1, 0] ![![21, 0, 0], ![-104, -5, 1]] where
    su := ![![105, 0, 0], ![0, 21, 0]]
    hsu := by decide
    w := ![![105, 21, 0], ![210, 21, 0]]
    hw := by decide
    g := ![![![103, 5, -1], ![22, 0, 0]], ![![2, 0, 0], ![-1, 0, 0]]]
    h := ![![![1, 0, 0], ![1, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {21} * I5N0 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 7 ![![7, 0, 0], ![1, 1, 0]]
  ![207, 57, 4] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![49, 0, 0], ![7, 7, 0]]
    hsu := by decide
    w := ![![1449, 399, 28], ![2506, 693, 49]]
    hw := by decide
    g := ![![![-47, -28, 12], ![17, -81, 0]], ![![35, -6, 4], ![-8, -30, 0]]]
    h := ![![![28, 28, 22], ![11, -150, 0]], ![![49, 49, 38], ![15, -259, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {7} * I7N0 =  Ideal.span {B.equivFun.symm ![207, 57, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![7, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![13, -6, 0], ![42, 0, 0]], ![![-2, 3, -1], ![-6, 7, 0]]]
    h := ![![![13, -6, 0], ![42, 0, 0]], ![![-2, 3, -1], ![-6, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E23RS0 : RelationCertificate Table 21 ![![23, 0, 0], ![6, 1, 0]]
  ![107, 8, -1] ![![21, 0, 0], ![8, 1, 0]] where
    su := ![![483, 0, 0], ![126, 21, 0]]
    hsu := by decide
    w := ![![2247, 168, -21], ![126, 21, 0]]
    hw := by decide
    g := ![![![-21503, 1356904, 169949], ![56434, -3568928, 0]], ![![-6416, 404758, 50695], ![16843, -1064595, 0]]]
    h := ![![![97, 16, 0], ![-354, -1, 0]], ![![-6, -1, 0], ![24, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {21} * I23N0 =  Ideal.span {B.equivFun.symm ![107, 8, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS0 


noncomputable def E23RS2 : RelationCertificate Table 21 ![![23, 0, 0], ![10, 1, 0]]
  ![-987, -44, 8] ![![21, 0, 0], ![-104, -5, 1]] where
    su := ![![483, 0, 0], ![210, 21, 0]]
    hsu := by decide
    w := ![![-20727, -924, 168], ![41328, 2751, -399]]
    hw := by decide
    g := ![![![51, -127, -17], ![125, 0, 0]], ![![66, -133, -18], ![134, 0, 0]]]
    h := ![![![-2379, -289, -5], ![5373, 123, 0]], ![![4716, 557, 8], ![-10650, -203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {21} * I23N2 =  Ideal.span {B.equivFun.symm ![-987, -44, 8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS2 
