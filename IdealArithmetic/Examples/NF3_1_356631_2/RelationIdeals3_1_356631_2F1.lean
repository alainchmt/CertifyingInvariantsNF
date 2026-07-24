import IdealArithmetic.Examples.NF3_1_356631_2.PrimesBelow3_1_356631_2F1
import IdealArithmetic.Examples.NF3_1_356631_2.ClassGroupData3_1_356631_2

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![-8, 1, 0]]
  ![-15, -4, -1] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![123, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![-45, -12, -3], ![186, 45, 9]]
    hw := by decide
    g := ![![![1, 6, -1], ![7, 0, 0]], ![![9, -1, 0], ![-1, 0, 0]]]
    h := ![![![-359, 50, -2], ![-1838, 27, 0]], ![![1502, -187, 0], ![7690, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![-15, -4, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![28, 1, 0]]
  ![-363, -100, -24] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![177, 0, 0], ![84, 3, 0]]
    hsu := by decide
    w := ![![-1089, -300, -72], ![-753, -210, -51]]
    hw := by decide
    g := ![![![119146, -320164, 48697], ![-763003, 0, 51410]], ![![57728, -155133, 23596], ![-369704, 0, 24910]]]
    h := ![![![-2501, -115, -3], ![5257, 51, 0]], ![![-1717, -97, -4], ![3609, 73, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-363, -100, -24]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E71RS0 : RelationCertificate Table 3 ![![71, 0, 0], ![27, 1, 0]]
  ![-48, -13, -3] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![213, 0, 0], ![81, 3, 0]]
    hsu := by decide
    w := ![![-144, -39, -9], ![-123, -27, -6]]
    hw := by decide
    g := ![![![143422, -385423, 58625], ![-918517, 0, 61886]], ![![57659, -154964, 23571], ![-369300, 0, 24882]]]
    h := ![![![-1896, -97, -3], ![4984, 70, 0]], ![![-1651, -97, -4], ![4340, 94, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {3} * I71N0 =  Ideal.span {B.equivFun.symm ![-48, -13, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 3 ![![71, 0, 0], ![-25, 1, 0]]
  ![-15, -3, 1] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![213, 0, 0], ![-75, 3, 0]]
    hsu := by decide
    w := ![![-45, -9, 3], ![-759, -39, 24]]
    hw := by decide
    g := ![![![16, -2, -3], ![4, 0, 0]], ![![10, 2, 0], ![1, 0, 0]]]
    h := ![![![-1165, 55, -1], ![-3308, 24, 0]], ![![-20043, 894, -11], ![-56912, 263, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3} * I71N1 =  Ideal.span {B.equivFun.symm ![-15, -3, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![26, 1, 0]]
  ![-123, -11, 5] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![219, 0, 0], ![78, 3, 0]]
    hsu := by decide
    w := ![![-369, -33, 15], ![-1839, -3, 36]]
    hw := by decide
    g := ![![![11, 43, 28], ![-31, 0, 0]], ![![0, 22, 15], ![-17, 0, 0]]]
    h := ![![![-4437, -232, -7], ![12453, 172, 0]], ![![-21915, -1052, -24], ![61507, 588, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![-123, -11, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 3 ![![79, 0, 0], ![32, 1, 0]]
  ![5487, 1513, 363] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![237, 0, 0], ![96, 3, 0]]
    hsu := by decide
    w := ![![16461, 4539, 1089], ![11568, 3189, 765]]
    hw := by decide
    g := ![![![-373, 1031, -162], ![2485, 0, -159]], ![![-151, 423, -66], ![1022, 0, -66]]]
    h := ![![![281185, 10739, 186], ![-694004, -4777, 0]], ![![197552, 7527, 129], ![-487586, -3312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {3} * I79N1 =  Ideal.span {B.equivFun.symm ![5487, 1513, 363]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
