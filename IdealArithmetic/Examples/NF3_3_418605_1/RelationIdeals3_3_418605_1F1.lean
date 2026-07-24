import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F1
import IdealArithmetic.Examples.NF3_3_418605_1.ClassGroupData3_3_418605_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-11, 1, 0]]
  ![-11, 1, 0] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![74, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![-22, 2, 0], ![336, 12, -10]]
    hw := by decide
    g := ![![![18, 5, 1], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-168, -2016, 504], ![1, -6216, 0]], ![![2567, 30401, -7601], ![97, 93744, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-11, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E43RS0 : RelationCertificate Table 2 ![![43, 0, 0], ![6, 1, 0]]
  ![-43, -24, -7] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![86, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![-86, -48, -14], ![-948, -540, -158]]
    hw := by decide
    g := ![![![17, 6, -4], ![9, 0, 0]], ![![0, -1, 0], ![1, 0, 0]]]
    h := ![![![737, -3723, -2233], ![45, 32004, 0]], ![![8160, -41020, -24607], ![220, 352674, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {2} * I43N0 =  Ideal.span {B.equivFun.symm ![-43, -24, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS0 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![-6, 1, 0]]
  ![530, 221, -65] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![118, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![1060, 442, -130], ![852, 312, -94]]
    hw := by decide
    g := ![![![15, -247, -91], ![39, 0, 0]], ![![23, -22, -9], ![5, 0, 0]]]
    h := ![![![-48515, -339084, 145328], ![-796, -2858139, 0]], ![![-39036, -272832, 116933], ![-642, -2299698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![530, 221, -65]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![17, 1, 0]]
  ![271, 112, -33] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![122, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![542, 224, -66], ![372, 156, -46]]
    hw := by decide
    g := ![![![9, 2, 1], ![-23, 0, 0]], ![![19, -1, -1], ![-4, 0, 0]]]
    h := ![![![-711, 11252, 2109], ![44, -42894, 0]], ![![-490, 7720, 1447], ![38, -29430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![271, 112, -33]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-5, 1, 0]]
  ![200, 113, 33] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![158, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![400, 226, 66], ![4524, 2544, 742]]
    hw := by decide
    g := ![![![15, -53, 6], ![27, 0, 0]], ![![-10, 9, -1], ![-4, 0, 0]]]
    h := ![![![-22140, -132769, 66387], ![-216, -1748180, 0]], ![![-250457, -1501673, 750869], ![-3121, -19772760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![200, 113, 33]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
