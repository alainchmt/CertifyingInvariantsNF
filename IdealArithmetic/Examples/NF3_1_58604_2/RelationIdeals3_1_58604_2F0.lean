import IdealArithmetic.Examples.NF3_1_58604_2.PrimesBelow3_1_58604_2F0
import IdealArithmetic.Examples.NF3_1_58604_2.ClassGroupData3_1_58604_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 9 ![![2, 0, 0], ![0, 1, 0]]
  ![246, 29, 13] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![18, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![2214, 261, 117], ![1530, 180, 81]]
    hw := by decide
    g := ![![![0, 3, 1], ![1, -8, 0]], ![![1, 8, 2], ![3, -20, 0]]]
    h := ![![![123, 11, 0], ![7, 13, 0]], ![![85, 8, 0], ![4, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {9} * I2N0 =  Ideal.span {B.equivFun.symm ![246, 29, 13]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 9 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, -1, 0] ![![9, 0, 0], ![6, 1, 1]] where
    su := ![![27, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![9, -9, 0], ![-36, 9, 0]]
    hw := by decide
    g := ![![![-7, -1, -1], ![8, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 1, -1], ![-1, 3, 0]], ![![-2, 2, -1], ![-2, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {9} * I3N2 =  Ideal.span {B.equivFun.symm ![1, -1, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS2 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0], ![0, 1, 0]]
  ![-77, -9, -4] ![![9, 0, 0], ![33, 7, 4]] where
    su := ![![63, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![-693, -81, -36], ![-5229, -612, -279]]
    hw := by decide
    g := ![![![-137, 311, 61], ![-228, 52, 0]], ![![-25, -6, -3], ![7, 0, 0]]]
    h := ![![![-11, -2, 0], ![5, -4, 0]], ![![-83, -10, 0], ![2, -31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![-77, -9, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 9 ![![13, 0, 0], ![2, 1, 0]]
  ![-39, -4, -2] ![![9, 0, 0], ![-12, 2, -1]] where
    su := ![![117, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![-351, -36, -18], ![468, 54, 27]]
    hw := by decide
    g := ![![![-1, -2, 2], ![10, -3, 0]], ![![-2, -1, 1], ![5, -2, 0]]]
    h := ![![![-565, -289, -4], ![3653, 50, 0]], ![![748, 382, 5], ![-4836, -62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {9} * I13N0 =  Ideal.span {B.equivFun.symm ![-39, -4, -2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0], ![-4, 1, 0]]
  ![15, 2, 1] ![![9, 0, 0], ![-12, 2, -1]] where
    su := ![![117, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![135, 18, 9], ![-180, -36, -9]]
    hw := by decide
    g := ![![![15, 0, -1], ![-2, 4, 0]], ![![8, -1, 0], ![2, 1, 0]]]
    h := ![![![595, -156, 2], ![1930, -25, 0]], ![![-780, 210, -4], ![-2530, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![15, 2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-5, 1, 0]]
  ![-3, -1, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![51, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-9, -3, 3], ![39, -18, 0]]
    hw := by decide
    g := ![![![-409, -379, -6], ![1112, 12, 0]], ![![91, 86, 1], ![-254, -2, 0]]]
    h := ![![![-4, 1, 0], ![-13, 1, 0]], ![![44, -9, 0], ![147, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-3, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0], ![1, 1, 0]]
  ![-15, 5, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![171, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-135, 45, 9], ![-18, -9, 9]]
    hw := by decide
    g := ![![![-2083, 50711, 12809], ![4714, -115275, 0]], ![![-141, 3380, 854], ![322, -7685, 0]]]
    h := ![![![-1, -1, -1], ![4, 20, 0]], ![![0, 0, 0], ![-2, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-15, 5, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![6, 1, 0]]
  ![95, 11, 5] ![![3, 0, 0], ![9, 1, 1]] where
    su := ![![57, 0, 0], ![18, 3, 0]]
    hsu := by decide
    w := ![![285, 33, 15], ![1527, 180, 81]]
    hw := by decide
    g := ![![![-3, 1, -2], ![2, 0, 0]], ![![-8, 1, -1], ![2, 0, 0]]]
    h := ![![![845, 163, 4], ![-2660, -71, 0]], ![![4535, 884, 23], ![-14276, -410, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![95, 11, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 9 ![![19, 0, 0], ![-7, 1, 0]]
  ![-13, 3, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![-63, 9, 0]]
    hsu := by decide
    w := ![![-117, 27, 9], ![81, -36, 0]]
    hw := by decide
    g := ![![![-10, -110, 36], ![-3, -328, 0]], ![![4, 39, -13], ![5, 118, 0]]]
    h := ![![![-998, 157, -2], ![-2707, 39, 0]], ![![706, -108, 1], ![1915, -19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {9} * I19N2 =  Ideal.span {B.equivFun.symm ![-13, 3, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 3 ![![23, 0, 0], ![7, 1, 0]]
  ![11, -5, 0] ![![3, 0, 0], ![9, 1, 1]] where
    su := ![![69, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![33, -15, 0], ![-111, 36, 6]]
    hw := by decide
    g := ![![![-19, -3, 7], ![-46, 0, 0]], ![![-15, -2, 2], ![-16, 0, 0]]]
    h := ![![![23, 3, 0], ![-74, 0, 0]], ![![-99, -21, -1], ![320, 25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {3} * I23N0 =  Ideal.span {B.equivFun.symm ![11, -5, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![9, 1, 0]]
  ![5, -2, 0] ![![3, 0, 0], ![9, 1, 1]] where
    su := ![![69, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![15, -6, 0], ![-39, 15, 3]]
    hw := by decide
    g := ![![![-3, 0, -2], ![10, 0, 0]], ![![-2, 0, -1], ![5, 0, 0]]]
    h := ![![![55, 6, 0], ![-140, 0, 0]], ![![-161, -27, -1], ![410, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![5, -2, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![15, 1, 0]]
  ![-9, 2, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![93, 0, 0], ![45, 3, 0]]
    hsu := by decide
    w := ![![-27, 6, 3], ![33, -21, 3]]
    hw := by decide
    g := ![![![-178, 2275, 2505], ![701, -7506, 0]], ![![-91, 1179, 1299], ![366, -3892, 0]]]
    h := ![![![-114, -23, -1], ![235, 32, 0]], ![![116, 7, 0], ![-239, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![-9, 2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
