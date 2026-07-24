import IdealArithmetic.Examples.NF3_1_410267_1.PrimesBelow3_1_410267_1F1
import IdealArithmetic.Examples.NF3_1_410267_1.ClassGroupData3_1_410267_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 4096 ![![43, 0, 0], ![-21, 1, 0]]
  ![4461, 278, 217] ![![4096, 0, 0], ![995, 1, 0]] where
    su := ![![176128, 0, 0], ![-86016, 4096, 0]]
    hsu := by decide
    w := ![![18272256, 1138688, 888832], ![4464640, 278528, 217088]]
    hw := by decide
    g := ![![![1567719312681987399, 851956970531980999816, 4276893144019626348], ![588827560217422535, -3503630863580877904286, 0]], ![![-771706793460046842, -419374167669347528010, -2105292361613045022], ![-289849225381367939, 1724655502633406482025, 0]]]
    h := ![![![-2493, 36142, -9041], ![2092, 77796, 0]], ![![-596, 8830, -2209], ![538, 19008, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {4096} * I43N1 =  Ideal.span {B.equivFun.symm ![4461, 278, 217]} * (J0 ^ 12) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 1024 ![![47, 0, 0], ![6, 1, 0]]
  ![-243, -42, -7] ![![1024, 0, 0], ![-29, 1, 0]] where
    su := ![![48128, 0, 0], ![6144, 1024, 0]]
    hsu := by decide
    w := ![![-248832, -43008, -7168], ![6144, 1024, 0]]
    hw := by decide
    g := ![![![10594, -148411, 26502], ![-237, -5427611, 0]], ![![1624, -22736, 4060], ![1, -831488, 0]]]
    h := ![![![1647, 5940, 4249], ![372, -39942, 0]], ![![-42, -147, -105], ![1, 987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {1024} * I47N1 =  Ideal.span {B.equivFun.symm ![-243, -42, -7]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E47RS1 


noncomputable def E67RS1 : RelationCertificate Table 8388608 ![![67, 0, 0], ![-27, 1, 0]]
  ![253249, -32978, -6691] ![![8388608, 0, 0], ![525283, 1, 0]] where
    su := ![![562036736, 0, 0], ![-226492416, 8388608, 0]]
    hsu := by decide
    w := ![![2124406587392, -276639514624, -56128176128], ![133026545664, -17322475520, -3514826752]]
    hw := by decide
    g := ![![![-620772268477529739, -164001701568600767815711, -1561076499270944216], ![-58422424920930124, 2619051762079247363578439, 0]], ![![246013901484773798, 64994363475713007627537, 618659272657417394], ![23152981247997297, -1037938024777638562129564, 0]]]
    h := ![![![209352734313356, -3429712697599801, 659949215006127], ![-135555769015751, -8843319481083440, 0]], ![![13109293942810, -214762477498363, 41324839989368], ![-8488259909734, -553752855857615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {8388608} * I67N1 =  Ideal.span {B.equivFun.symm ![253249, -32978, -6691]} * (J0 ^ 23) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_23 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 128 ![![71, 0, 0], ![-34, 1, 0]]
  ![-535, -34, -27] ![![128, 0, 0], ![-29, 1, 0]] where
    su := ![![9088, 0, 0], ![-4352, 128, 0]]
    hsu := by decide
    w := ![![-68480, -4352, -3456], ![12288, 768, 640]]
    hw := by decide
    g := ![![![36888244, -556638291, 99417421], ![-12706095, -2545085976, 0]], ![![80391238388, -1213093171667, 216662411975], ![-27690930326, -5546557746561, 0]]]
    h := ![![![-5737, 131054, -19867], ![4630, 282106, 0]], ![![1038, -23517, 3565], ![-813, -50622, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {128} * I71N1 =  Ideal.span {B.equivFun.symm ![-535, -34, -27]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 65536 ![![73, 0, 0], ![5, 1, 0]]
  ![17499, 1242, 719] ![![65536, 0, 0], ![995, 1, 0]] where
    su := ![![4784128, 0, 0], ![327680, 65536, 0]]
    hsu := by decide
    w := ![![1146814464, 81395712, 47120384], ![17498112, 1245184, 720896]]
    hw := by decide
    g := ![![![35362343779120, 17616538960014031, 88436440624036], ![805695664645, -1159154114547364659, 0]], ![![2576079220497, 1283331225020679, 6442425832913], ![58693426958, -84442163877157275, 0]]]
    h := ![![![167461, 505220, 421223], ![18454, -6149712, 0]], ![![2552, 7708, 6427], ![327, -93832, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {65536} * I73N1 =  Ideal.span {B.equivFun.symm ![17499, 1242, 719]} * (J0 ^ 16) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_16 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 4 ![![79, 0, 0], ![-31, 1, 0]]
  ![21, 2, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![316, 0, 0], ![-124, 4, 0]]
    hsu := by decide
    w := ![![84, 8, 4], ![100, 8, 8]]
    hw := by decide
    g := ![![![79, 3, 198], ![-15, -158, 0]], ![![-30, -2, -79], ![9, 63, 0]]]
    h := ![![![3381, -62728, 10459], ![-2046, -165252, 0]], ![![3997, -74716, 12458], ![-2514, -196836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {4} * I79N1 =  Ideal.span {B.equivFun.symm ![21, 2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS1 
