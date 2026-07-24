import IdealArithmetic.Examples.NF3_1_374220_1.PrimesBelow3_1_374220_1F3
import IdealArithmetic.Examples.NF3_1_374220_1.ClassGroupData3_1_374220_1

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 625 ![![151, 0, 0], ![54, 1, 0]]
  ![49, -15, 1] ![![625, 0, 0], ![-91, 246, 1]] where
    su := ![![94375, 0, 0], ![33750, 625, 0]]
    hsu := by decide
    w := ![![30625, -9375, 625], ![21875, 9375, -3750]]
    hw := by decide
    g := ![![![39, -75, 0], ![194, 0, 0]], ![![15, -29, 0], ![75, 0, 0]]]
    h := ![![![187, 3, 0], ![-522, 1, 0]], ![![149, -49, -1], ![-416, 145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {625} * I151N1 =  Ideal.span {B.equivFun.symm ![49, -15, 1]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 5 ![![163, 0, 0], ![-26, 1, 0]]
  ![-35, -4, -1] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![815, 0, 0], ![-130, 5, 0]]
    hsu := by decide
    w := ![![-175, -20, -5], ![-1060, -115, -35]]
    hw := by decide
    g := ![![![-13, 6, 1], ![-4, 0, 0]], ![![-10, -2, -1], ![5, 0, 0]]]
    h := ![![![-447, 43, -1], ![-2801, 162, 0]], ![![-2712, 129, -1], ![-16994, 156, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {5} * I163N1 =  Ideal.span {B.equivFun.symm ![-35, -4, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E163RS1 


noncomputable def E173RS0 : RelationCertificate Table 5 ![![173, 0, 0], ![16, 1, 0]]
  ![137, -23, -4] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![865, 0, 0], ![80, 5, 0]]
    hsu := by decide
    w := ![![685, -115, -20], ![-730, 255, -15]]
    hw := by decide
    g := ![![![1501, 382, 15], ![-519, 198, 0]], ![![172, 42, 2], ![-55, 21, 0]]]
    h := ![![![8957, 560, 0], ![-96839, -4, 0]], ![![-9594, -615, -1], ![103726, 170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N0 : Ideal.span {5} * I173N0 =  Ideal.span {B.equivFun.symm ![137, -23, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS0 


noncomputable def E173RS1 : RelationCertificate Table 5 ![![173, 0, 0], ![76, 1, 0]]
  ![17, -8, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![865, 0, 0], ![380, 5, 0]]
    hsu := by decide
    w := ![![85, -40, 5], ![80, 15, -10]]
    hw := by decide
    g := ![![![87, 203, -95], ![11, 488, 0]], ![![40, 90, -42], ![5, 216, 0]]]
    h := ![![![3153, 41, 0], ![-7177, 1, 0]], ![![3048, 41, 0], ![-6938, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {5} * I173N1 =  Ideal.span {B.equivFun.symm ![17, -8, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS1 


noncomputable def E173RS2 : RelationCertificate Table 625 ![![173, 0, 0], ![81, 1, 0]]
  ![-61, 4, -3] ![![625, 0, 0], ![159, 121, 1]] where
    su := ![![108125, 0, 0], ![50625, 625, 0]]
    hsu := by decide
    w := ![![-38125, 2500, -1875], ![-50625, -625, 0]]
    hw := by decide
    g := ![![![87208, 113273, 104560], ![44693, -540452, 0]], ![![40257, 52327, 48351], ![20944, -249920, 0]]]
    h := ![![![-1088, -93, -1], ![2323, 170, 0]], ![![-1458, -99, -1], ![3113, 173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N2 : Ideal.span {625} * I173N2 =  Ideal.span {B.equivFun.symm ![-61, 4, -3]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E173RS2 
