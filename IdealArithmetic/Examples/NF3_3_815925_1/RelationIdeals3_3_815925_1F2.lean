import IdealArithmetic.Examples.NF3_3_815925_1.PrimesBelow3_3_815925_1F2
import IdealArithmetic.Examples.NF3_3_815925_1.ClassGroupData3_3_815925_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-19, 1, 0]]
  ![3475, 39, -95] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![178, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![6950, 78, -190], ![1218, 16, -34]]
    hw := by decide
    g := ![![![53, -206, -97], ![-101, 0, 0]], ![![-4, 15, 7], ![8, 0, 0]]]
    h := ![![![-13210, 141960, -28403], ![4459, 631943, 0]], ![![-2308, 24875, -4977], ![813, 110734, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![3475, 39, -95]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![28, 1, 0]]
  ![35355, 395, -966] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![56, 2, 0]]
    hsu := by decide
    w := ![![70710, 790, -1932], ![12382, 184, -352]]
    hw := by decide
    g := ![![![10444, -40654, -19352], ![-20327, 0, 0]], ![![4107, -15987, -7610], ![-7993, 0, 0]]]
    h := ![![![10491735, 157676515, 23365778], ![4383025, -601669025, 0]], ![![1837125, 27609565, 4091408], ![767497, -105353800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![35355, 395, -966]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E113RS1 : RelationCertificate Table 2 ![![113, 0, 0], ![-55, 1, 0]]
  ![21, 5, -2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![226, 0, 0], ![-110, 2, 0]]
    hsu := by decide
    w := ![![42, 10, -4], ![34, -56, 16]]
    hw := by decide
    g := ![![![-4, 34, 16], ![17, 0, 0]], ![![1, -13, -6], ![-6, 0, 0]]]
    h := ![![![898, -34686, 2478], ![-701, -70004, 0]], ![![739, -28778, 2056], ![-594, -58080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {2} * I113N1 =  Ideal.span {B.equivFun.symm ![21, 5, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![-21, 1, 0]]
  ![-363, -11, 12] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![262, 0, 0], ![-42, 2, 0]]
    hsu := by decide
    w := ![![-726, -22, 24], ![-166, 80, -20]]
    hw := by decide
    g := ![![![-200, 777, 370], ![389, 0, 0]], ![![13, -51, -24], ![-24, 0, 0]]]
    h := ![![![-140075, 1601841, -291292], ![34770, 9539816, 0]], ![![-32185, 368032, -66926], ![7976, 2191824, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![-363, -11, 12]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 
