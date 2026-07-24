import IdealArithmetic.Examples.NF3_3_815925_1.PrimesBelow3_3_815925_1F1
import IdealArithmetic.Examples.NF3_3_815925_1.ClassGroupData3_3_815925_1

set_option linter.all false

noncomputable section


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![4, 1, 0]]
  ![-29, 19, -5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-58, 38, -10], ![98, -228, 66]]
    hw := by decide
    g := ![![![-33, 119, 57], ![61, 0, 0]], ![![-11, 42, 20], ![21, 0, 0]]]
    h := ![![![135, 210, 281], ![58, -3303, 0]], ![![-269, -406, -537], ![14, 6318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-29, 19, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-11, 1, 0]]
  ![10967, 87, -289] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![21934, 174, -578], ![3642, 476, -230]]
    hw := by decide
    g := ![![![31721, -123477, -58777], ![-61737, 0, 0]], ![![782, -3044, -1449], ![-1522, 0, 0]]]
    h := ![![![-33663, 213277, -71149], ![9590, 1084950, 0]], ![![-5522, 35021, -11683], ![1601, 178137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![10967, 87, -289]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![-33, 1, 0]]
  ![-159, 373, -108] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![134, 0, 0], ![-66, 2, 0]]
    hsu := by decide
    w := ![![-318, 746, -216], ![2042, -4420, 1276]]
    hw := by decide
    g := ![![![386, -1483, -706], ![-741, 0, 0]], ![![-119, 453, 216], ![228, 0, 0]]]
    h := ![![![447, -10509, 1236], ![-344, -20730, 0]], ![![-2639, 64664, -7606], ![2342, 127560, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![-159, 373, -108]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E79RS0 : RelationCertificate Table 2 ![![79, 0, 0], ![35, 1, 0]]
  ![3, -13, -5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![70, 2, 0]]
    hsu := by decide
    w := ![![6, -26, -10], ![34, -164, -62]]
    hw := by decide
    g := ![![![223, 4, -7], ![3, 0, 0]], ![![100, 1, -3], ![2, 0, 0]]]
    h := ![![![149, 3645, 429], ![148, -8474, 0]], ![![916, 20793, 2447], ![695, -48336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {2} * I79N0 =  Ideal.span {B.equivFun.symm ![3, -13, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS0 


noncomputable def E79RS2 : RelationCertificate Table 2 ![![79, 0, 0], ![-9, 1, 0]]
  ![947, 11, -26] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![1894, 22, -52], ![334, 0, -8]]
    hw := by decide
    g := ![![![-24, 93, 44], ![47, 0, 0]], ![![-1, 4, 2], ![2, 0, 0]]]
    h := ![![![129093, -658195, 263394], ![-22964, -5202038, 0]], ![![22774, -116109, 46464], ![-4039, -917665, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {2} * I79N2 =  Ideal.span {B.equivFun.symm ![947, 11, -26]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS2 
