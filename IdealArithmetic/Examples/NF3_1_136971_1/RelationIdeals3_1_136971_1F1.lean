import IdealArithmetic.Examples.NF3_1_136971_1.PrimesBelow3_1_136971_1F1
import IdealArithmetic.Examples.NF3_1_136971_1.ClassGroupData3_1_136971_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 196 ![![43, 0, 0], ![-10, 1, 0]]
  ![2453, 467, 127] ![![196, 0, 0], ![-33, 1, 0]] where
    su := ![![8428, 0, 0], ![-1960, 196, 0]]
    hsu := by decide
    w := ![![480788, 91532, 24892], ![-71932, -13720, -3724]]
    hw := by decide
    g := ![![![500175, 598760078, -18144704], ![2970743, 3556362001, 0]], ![![-109649, -131265563, 3977845], ![-651251, -779657624, 0]]]
    h := ![![![9741, -988, 6], ![41641, -131, 0]], ![![-1439, 157, -2], ![-6151, 67, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {196} * I43N1 =  Ideal.span {B.equivFun.symm ![2453, 467, 127]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 28 ![![53, 0, 0], ![4, 1, 0]]
  ![65, 15, 3] ![![28, 0, 0], ![-5, 1, 0]] where
    su := ![![1484, 0, 0], ![112, 28, 0]]
    hsu := by decide
    w := ![![1820, 420, 84], ![-112, -28, 0]]
    hw := by decide
    g := ![![![6, 794, -159], ![31, 4455, 0]], ![![5, 74, -15], ![27, 420, 0]]]
    h := ![![![6401, 1608, 2], ![-84797, -103, 0]], ![![-396, -103, -1], ![5246, 53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {28} * I53N1 =  Ideal.span {B.equivFun.symm ![65, 15, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 196 ![![61, 0, 0], ![9, 1, 0]]
  ![-13, -31, 5] ![![196, 0, 0], ![-33, 1, 0]] where
    su := ![![11956, 0, 0], ![1764, 196, 0]]
    hsu := by decide
    w := ![![-2548, -6076, 980], ![784, 980, -196]]
    hw := by decide
    g := ![![![64, 50322, -1525], ![383, 298894, 0]], ![![27, 8711, -264], ![161, 51743, 0]]]
    h := ![![![-19474, -2219, -6], ![131989, 371, 0]], ![![5938, 669, 1], ![-40246, -62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {196} * I61N1 =  Ideal.span {B.equivFun.symm ![-13, -31, 5]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 49 ![![67, 0, 0], ![32, 1, 0]]
  ![304, 54, 15] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![3283, 0, 0], ![1568, 49, 0]]
    hsu := by decide
    w := ![![14896, 2646, 735], ![5929, 1078, 294]]
    hw := by decide
    g := ![![![-22938, 3807048, 238030], ![70255, -11663476, 0]], ![![-10878, 1804089, 112798], ![33317, -5527105, 0]]]
    h := ![![![232528, 10012, 86], ![-486846, -5747, 0]], ![![92563, 3978, 34], ![-193800, -2272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {49} * I67N1 =  Ideal.span {B.equivFun.symm ![304, 54, 15]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E67RS1 


noncomputable def E79RS1 : RelationCertificate Table 196 ![![79, 0, 0], ![34, 1, 0]]
  ![-31, -89, 27] ![![196, 0, 0], ![-33, 1, 0]] where
    su := ![![15484, 0, 0], ![6664, 196, 0]]
    hsu := by decide
    w := ![![-6076, -17444, 5292], ![2940, 2744, -980]]
    hw := by decide
    g := ![![![58, 51887, -1572], ![305, 308179, 0]], ![![36, 23303, -706], ![195, 138408, 0]]]
    h := ![![![-111, -16, 0], ![257, 27, 0]], ![![23, -31, -1], ![-53, 74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {196} * I79N1 =  Ideal.span {B.equivFun.symm ![-31, -89, 27]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E79RS1 
