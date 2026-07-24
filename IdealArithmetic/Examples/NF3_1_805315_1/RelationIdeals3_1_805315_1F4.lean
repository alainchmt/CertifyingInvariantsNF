import IdealArithmetic.Examples.NF3_1_805315_1.PrimesBelow3_1_805315_1F4
import IdealArithmetic.Examples.NF3_1_805315_1.ClassGroupData3_1_805315_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 4 ![![199, 0, 0], ![-96, 1, 0]]
  ![7778242376769311, -1406409409964852, 498620671810011] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![796, 0, 0], ![-384, 4, 0]]
    hsu := by decide
    w := ![![31112969507077244, -5625637639859408, 1994482687240044], ![-109696547798202420, 19834591105674756, -7032047049824260]]
    hw := by decide
    g := ![![![850089798, -52189312, -37551406], ![-13047325, -652515, 0]], ![![-367677737, 24037047, 16729424], ![6009265, 305568, 0]]]
    h := ![![![392341415711002889, -4708529512521373, 34872975417439], ![813210036292841725, -1288220287252070, 0]], ![![-1383297690436346091, 16601097256630112, -122953388099935], ![-2867175169373784599, 4541942493886200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {4} * I199N1 =  Ideal.span {B.equivFun.symm ![7778242376769311, -1406409409964852, 498620671810011]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E199RS1 


noncomputable def E233RS1 : RelationCertificate Table 2 ![![233, 0, 0], ![48, 1, 0]]
  ![8131483, -1470280, 521265] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![466, 0, 0], ![96, 2, 0]]
    hsu := by decide
    w := ![![16262966, -2940560, 1042530], ![-114678300, 20735358, -7351400]]
    hw := by decide
    g := ![![![10101, 77920, 468860], ![38961, -187131, 0]], ![![1106, 16416, 98050], ![8209, -39102, 0]]]
    h := ![![![12667235, 307312, 7385], ![-61319464, -239888, 0]], ![![-89323230, -2167355, -52110], ![432395280, 1693186, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {2} * I233N1 =  Ideal.span {B.equivFun.symm ![8131483, -1470280, 521265]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E233RS1 
