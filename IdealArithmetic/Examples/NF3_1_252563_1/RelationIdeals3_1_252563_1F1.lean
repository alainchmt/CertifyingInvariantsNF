import IdealArithmetic.Examples.NF3_1_252563_1.PrimesBelow3_1_252563_1F1
import IdealArithmetic.Examples.NF3_1_252563_1.ClassGroupData3_1_252563_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 2 ![![37, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![74, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![60, -12, 2]]
    hw := by decide
    g := ![![![-18, -2, -1], ![3, 0, 0]], ![![-24, -1, -1], ![2, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![30, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {2} * I37N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS2 : RelationCertificate Table 2 ![![37, 0, 0], ![-9, 1, 0]]
  ![33137, -29663, -7856] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![74, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![66274, -59326, -15712], ![-484740, 442324, 105602]]
    hw := by decide
    g := ![![![511867571, -1113640789, -942428180], ![5370310169, 0, 0]], ![![-112033212, 243744187, 206270633], ![-1175407636, 0, 0]]]
    h := ![![![599291, -70740, 171], ![2460070, -14183, 0]], ![![-4384062, 517640, -1381], ![-17996436, 103898, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {2} * I37N2 =  Ideal.span {B.equivFun.symm ![33137, -29663, -7856]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS2 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![-7, 1, 0]]
  ![99, -117, 8] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![82, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![198, -234, 16], ![-1340, 1596, -122]]
    hw := by decide
    g := ![![![-2271, 4897, 4144], ![-23617, 0, 0]], ![![322, -729, -617], ![3514, 0, 0]]]
    h := ![![![139, -21, 0], ![800, 8, 0]], ![![-898, 149, -2], ![-5164, 21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![99, -117, 8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 2 ![![53, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![106, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-6, 2, 0], ![-40, -16, -2]]
    hw := by decide
    g := ![![![-11, -1, 0], ![-1, 0, 0]], ![![-24, -1, -1], ![2, 0, 0]]]
    h := ![![![-3, 4, -1], ![-52, 53, 0]], ![![-22, 10, -1], ![-382, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {2} * I53N1 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-24, 1, 0]]
  ![-59555423, -1383666, -1534413] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![122, 0, 0], ![-48, 2, 0]]
    hsu := by decide
    w := ![![-119110846, -2767332, -3068826], ![-1591018340, -36964526, -40991720]]
    hw := by decide
    g := ![![![-232, 5563, -578], ![-323, 0, 0]], ![![43, -1783, 331], ![97, 0, 0]]]
    h := ![![![-898426811, 41037584, -177925], ![-2281020002, 9319012, 0]], ![![-12000700522, 548157683, -2376617], ![-30468634278, 124477777, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-59555423, -1383666, -1534413]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-30, 1, 0]]
  ![-2441, 4432, -1913] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![146, 0, 0], ![-60, 2, 0]]
    hsu := by decide
    w := ![![-4882, 8864, -3826], ![27140, -54318, 26860]]
    hw := by decide
    g := ![![![-22621553, 49216390, 41649797], ![-237336207, 0, 0]], ![![9017075, -19617953, -16601863], ![94603657, 0, 0]]]
    h := ![![![-152867, 5779, -47], ![-371895, 1518, 0]], ![![851230, -32131, 297], ![2070874, -8251, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-2441, 4432, -1913]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
