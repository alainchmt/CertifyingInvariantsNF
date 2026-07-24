import IdealArithmetic.Examples.NF3_3_262601_1.PrimesBelow3_3_262601_1F1
import IdealArithmetic.Examples.NF3_3_262601_1.ClassGroupData3_3_262601_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 2 ![![41, 0, 0], ![15, 1, 0]]
  ![-3, 34, -7] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![82, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![-6, 68, -14], ![7130, 736, -292]]
    hw := by decide
    g := ![![![-58, 1528, 430], ![-249, 0, 0]], ![![-41, 955, 269], ![-156, 0, 0]]]
    h := ![![![-18, -7, -1], ![49, 17, 0]], ![![10100, 801, 12], ![-27369, -319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2} * I41N0 =  Ideal.span {B.equivFun.symm ![-3, 34, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![-9, 1, 0]]
  ![1047, 506, 87] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![82, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![2094, 1012, 174], ![-50, -24, -4]]
    hw := by decide
    g := ![![![-8, 54, -11], ![119, 0, 0]], ![![5, -15, 3], ![-36, 0, 0]]]
    h := ![![![18186, -2073, 19], ![82731, -346, 0]], ![![-428, 55, -2], ![-1947, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![1047, 506, 87]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![-1, 1, 0]]
  ![6175, 2984, 513] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![86, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![12350, 5968, 1026], ![-290, -140, -24]]
    hw := by decide
    g := ![![![-28, 172, -35], ![353, 0, 0]], ![![5, -15, 3], ![-36, 0, 0]]]
    h := ![![![288, -75, 11], ![6209, 20, 0]], ![![-6, 1, -2], ![-113, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![6175, 2984, 513]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 2 ![![53, 0, 0], ![-25, 1, 0]]
  ![-111, -4, 3] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![106, 0, 0], ![-50, 2, 0]]
    hsu := by decide
    w := ![![-222, -8, 6], ![1666, 36, -40]]
    hw := by decide
    g := ![![![22, 18, 4], ![-1, 0, 0]], ![![-9, -5, -1], ![0, 0, 0]]]
    h := ![![![-3362, 147, -1], ![-7123, 28, 0]], ![![25486, -1047, 2], ![53997, -63, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {2} * I53N1 =  Ideal.span {B.equivFun.symm ![-111, -4, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E61RS0 : RelationCertificate Table 2 ![![61, 0, 0], ![10, 1, 0]]
  ![-351, -10, 9] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![122, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![-702, -20, 18], ![5794, 168, -148]]
    hw := by decide
    g := ![![![26, 28, -6], ![-13, 0, 0]], ![![25, 3, -1], ![1, 0, 0]]]
    h := ![![![-4671, -495, -5], ![28458, 157, 0]], ![![38437, 4012, 30], ![-234176, -952, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {2} * I61N0 =  Ideal.span {B.equivFun.symm ![-351, -10, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![16, 1, 0]]
  ![567, 96, -31] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![122, 0, 0], ![32, 2, 0]]
    hsu := by decide
    w := ![![1134, 192, -62], ![7182, 1444, -440]]
    hw := by decide
    g := ![![![54, -806, -228], ![133, 0, 0]], ![![37, -351, -100], ![59, 0, 0]]]
    h := ![![![14355, 962, 7], ![-54693, -229, 0]], ![![90979, 6116, 46], ![-346633, -1513, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![567, 96, -31]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![-7, 1, 0]]
  ![51, 22, 3] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![134, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![102, 44, 6], ![134, 24, -8]]
    hw := by decide
    g := ![![![52, -208, 42], ![-371, 0, 0]], ![![9, 33, -7], ![58, 0, 0]]]
    h := ![![![648, -89, -1], ![6195, 35, 0]], ![![862, -123, 0], ![8241, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![51, 22, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![-20, 1, 0]]
  ![-2183, -50, 53] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![142, 0, 0], ![-40, 2, 0]]
    hsu := by decide
    w := ![![-4366, -100, 106], ![38738, 1328, -1032]]
    hw := by decide
    g := ![![![-252, 6008, 1692], ![-981, 0, 0]], ![![57, -791, -224], ![131, 0, 0]]]
    h := ![![![-22193, 1181, -7], ![-78676, 275, 0]], ![![197119, -10415, 54], ![698804, -2175, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![-2183, -50, 53]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 2 ![![71, 0, 0], ![-2, 1, 0]]
  ![-275, -8, 7] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![142, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-550, -16, 14], ![4538, 132, -116]]
    hw := by decide
    g := ![![![22, 8, -3], ![-3, 0, 0]], ![![5, -1, 0], ![1, 0, 0]]]
    h := ![![![-3, -136, 271], ![31, -9617, 0]], ![![33, 1118, -2236], ![37, 79349, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![-275, -8, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS2 
