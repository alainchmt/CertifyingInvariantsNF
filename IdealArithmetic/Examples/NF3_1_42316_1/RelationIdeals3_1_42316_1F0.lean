import IdealArithmetic.Examples.NF3_1_42316_1.PrimesBelow3_1_42316_1F0
import IdealArithmetic.Examples.NF3_1_42316_1.ClassGroupData3_1_42316_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 10 ![![5, 0, 0], ![0, 1, 0]]
  ![-338, 536, -351] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![50, 0, 0], ![0, 10, 0]]
    hsu := by decide
    w := ![![-3380, 5360, -3510], ![-13140, 4410, 370]]
    hw := by decide
    g := ![![![-494745, -24420, -34327], ![-51909, -2988, 0]], ![![-268565, -13384, -18899], ![-28190, -249, 0]]]
    h := ![![![0, 103, 65], ![21, -338, 0]], ![![-255, 168, 23], ![-399, -39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {10} * I5N0 =  Ideal.span {B.equivFun.symm ![-338, 536, -351]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![1, 1, 0]]
  ![-71, 25, 1] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![10, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-710, 250, 10], ![-8, -58, 52]]
    hw := by decide
    g := ![![![9628, 484, 688], ![1020, -45, 0]], ![![7147, 357, 506], ![757, -9, 0]]]
    h := ![![![-77, 19, -15], ![-10, 40, 0]], ![![-40, -45, -78], ![-12, 208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![-71, 25, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 10 ![![7, 0, 0], ![8, 2, 1]]
  ![-27, 9, 1] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![70, 0, 0], ![80, 20, 10]]
    hsu := by decide
    w := ![![-270, 90, 10], ![20, -30, 20]]
    hw := by decide
    g := ![![![795, 787, 1606], ![162, -8027, 0]], ![![943, 924, 1886], ![195, -9423, 0]]]
    h := ![![![-5, 1, 0], ![1, 0, 0]], ![![-2, -1, 0], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {10} * I7N0 =  Ideal.span {B.equivFun.symm ![-27, 9, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 10 ![![7, 0, 0], ![2, 1, 0]]
  ![-51, 27, -7] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![70, 0, 0], ![20, 10, 0]]
    hsu := by decide
    w := ![![-510, 270, -70], ![-290, 60, 40]]
    hw := by decide
    g := ![![![427, 831, 1710], ![133, -8700, 0]], ![![123, 395, 815], ![53, -4176, 0]]]
    h := ![![![1876, 4262, 4421], ![1147, -15477, 0]], ![![989, 2249, 2336], ![611, -8174, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {10} * I7N1 =  Ideal.span {B.equivFun.symm ![-51, 27, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 10 ![![13, 0, 0], ![4, 1, 0]]
  ![44, 2, 3] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![130, 0, 0], ![40, 10, 0]]
    hsu := by decide
    w := ![![440, 20, 30], ![160, 10, 10]]
    hw := by decide
    g := ![![![6, 7, 15], ![11, -76, 0]], ![![2, 3, 6], ![3, -30, 0]]]
    h := ![![![-3568, -17065, -8625], ![-2409, 56064, 0]], ![![-1296, -6195, -3131], ![-872, 20352, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {10} * I13N0 =  Ideal.span {B.equivFun.symm ![44, 2, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 10 ![![13, 0, 0], ![-4, 1, 0]]
  ![3, -1, 1] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![130, 0, 0], ![-40, 10, 0]]
    hsu := by decide
    w := ![![30, -10, 10], ![40, -10, 0]]
    hw := by decide
    g := ![![![8, 6, 13], ![7, -64, 0]], ![![-2, -2, -3], ![4, 15, 0]]]
    h := ![![![-1, 6, -3], ![1, 20, 0]], ![![2, 7, -4], ![12, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {10} * I13N1 =  Ideal.span {B.equivFun.symm ![3, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![5, 1, 0]]
  ![44, -8, -7] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![170, 0, 0], ![50, 10, 0]]
    hsu := by decide
    w := ![![440, -80, -70], ![-230, 120, -30]]
    hw := by decide
    g := ![![![300, 9, 10], ![37, 58, 0]], ![![137, 5, 6], ![15, 19, 0]]]
    h := ![![![-2534, -14962, -6023], ![-1614, 51192, 0]], ![![1384, 8191, 3297], ![895, -28026, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![44, -8, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 10 ![![19, 0, 0], ![2, 1, 0]]
  ![1, 3, -3] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![190, 0, 0], ![20, 10, 0]]
    hsu := by decide
    w := ![![10, 30, -30], ![-110, 40, 0]]
    hw := by decide
    g := ![![![-48, -16, -30], ![1, 138, 0]], ![![-11, -3, -5], ![3, 22, 0]]]
    h := ![![![-66, -134, -135], ![-13, 1281, 0]], ![![1073, 2184, 2196], ![232, -20862, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {10} * I19N0 =  Ideal.span {B.equivFun.symm ![1, 3, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 10 ![![19, 0, 0], ![4, 1, 0]]
  ![1042, -254, -111] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![190, 0, 0], ![40, 10, 0]]
    hsu := by decide
    w := ![![10420, -2540, -1110], ![-3430, 2120, -730]]
    hw := by decide
    g := ![![![-119285, -5964, -8434], ![-12521, 96, 0]], ![![-42144, -2107, -2979], ![-4421, 30, 0]]]
    h := ![![![-214, -1159, -581], ![-89, 5464, 0]], ![![72, 414, 199], ![54, -1927, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {10} * I19N1 =  Ideal.span {B.equivFun.symm ![1042, -254, -111]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E31RS1 : RelationCertificate Table 10 ![![31, 0, 0], ![6, 1, 0]]
  ![-1589411, -95033, -110967] ![![10, 0, 0], ![1, 1, 0]] where
    su := ![![310, 0, 0], ![60, 10, 0]]
    hsu := by decide
    w := ![![-15894110, -950330, -1109670], ![-5901190, -352840, -412000]]
    hw := by decide
    g := ![![![467, -221, -50], ![31, 278, 0]], ![![90, -30, -23], ![11, 60, 0]]]
    h := ![![![17227121, 111492419, 37236107], ![6930830, -577215142, 0]], ![![6396109, 41395079, 13825080], ![2573307, -214309340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {10} * I31N1 =  Ideal.span {B.equivFun.symm ![-1589411, -95033, -110967]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
