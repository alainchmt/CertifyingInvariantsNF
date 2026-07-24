import IdealArithmetic.Examples.NF3_1_393835_1.PrimesBelow3_1_393835_1F1
import IdealArithmetic.Examples.NF3_1_393835_1.ClassGroupData3_1_393835_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![15, 1, 0]]
  ![5527, 304, -75] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![123, 0, 0], ![45, 3, 0]]
    hsu := by decide
    w := ![![16581, 912, -225], ![-118284, -15519, 2436]]
    hw := by decide
    g := ![![![5571, -69472, -14331], ![14477, 0, 0]], ![![3537, -43794, -9035], ![9128, 0, 0]]]
    h := ![![![18512, 1395, 9], ![-50231, -444, 0]], ![![-132298, -10124, -63], ![358986, 3395, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![5527, 304, -75]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 6 ![![43, 0, 0], ![-17, 1, 0]]
  ![-842, -20, 9] ![![6, 0, 0], ![-49, -5, 1]] where
    su := ![![258, 0, 0], ![-102, 6, 0]]
    hsu := by decide
    w := ![![-5052, -120, 54], ![25578, 3174, -510]]
    hw := by decide
    g := ![![![-60, 1481, 316], ![-659, 0, 0]], ![![47, -208, -46], ![99, 0, 0]]]
    h := ![![![-90866, 6027, -40], ![-229788, 1729, 0]], ![![459536, -30396, 197], ![1162105, -8556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {6} * I43N1 =  Ideal.span {B.equivFun.symm ![-842, -20, 9]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![-24, 1, 0]]
  ![-1320511, -183164, 28109] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![159, 0, 0], ![-72, 3, 0]]
    hsu := by decide
    w := ![![-3961533, -549492, 84327], ![-14101428, 54003, 114870]]
    hw := by decide
    g := ![![![296731469, -3701523059, -763563322], ![771338608, 0, 0]], ![![-73638968, 918596659, 189491379], ![-191420948, 0, 0]]]
    h := ![![![-102141827, 4879312, -25632], ![-225508180, 1386605, 0]], ![![-364219292, 17405275, -92312], ![-804121750, 4930826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![-1320511, -183164, 28109]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 6 ![![59, 0, 0], ![12, 1, 0]]
  ![-74, -4, 1] ![![6, 0, 0], ![-49, -5, 1]] where
    su := ![![354, 0, 0], ![72, 6, 0]]
    hsu := by decide
    w := ![![-444, -24, 6], ![1386, 198, -30]]
    hw := by decide
    g := ![![![15, 8, 1], ![-1, 0, 0]], ![![25, 5, 0], ![2, 0, 0]]]
    h := ![![![-94, -20, -1], ![456, 60, 0]], ![![225, 8, -1], ![-1087, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {6} * I59N0 =  Ideal.span {B.equivFun.symm ![-74, -4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![13, 1, 0]]
  ![-323, -57, 8] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![177, 0, 0], ![39, 3, 0]]
    hsu := by decide
    w := ![![-969, -171, 24], ![-8124, -390, 105]]
    hw := by decide
    g := ![![![39, -470, -97], ![98, 0, 0]], ![![57, -186, -40], ![42, 0, 0]]]
    h := ![![![-7731, -649, -4], ![35062, 244, 0]], ![![-64644, -5330, -27], ![293176, 1628, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-323, -57, 8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 2 ![![59, 0, 0], ![-26, 1, 0]]
  ![90682, 34593, 3513] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![118, 0, 0], ![-52, 2, 0]]
    hsu := by decide
    w := ![![181364, 69186, 7026], ![1126698, 429808, 43648]]
    hw := by decide
    g := ![![![-22, 430, -62], ![427, 0, 0]], ![![70, -231, 32], ![-214, 0, 0]]]
    h := ![![![1420134, -60305, 303], ![3219124, -14364, 0]], ![![8822269, -374701, 1885], ![19998097, -89391, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {2} * I59N2 =  Ideal.span {B.equivFun.symm ![90682, 34593, 3513]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS2 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![3, 0, 0], ![-52, -5, 1]] where
    su := ![![201, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![3, 3, 0], ![228, 24, -3]]
    hw := by decide
    g := ![![![43, 6, -1], ![4, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![1, 1, 1], ![9, -68, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 6 ![![73, 0, 0], ![-2, 1, 0]]
  ![-2, 1, 0] ![![6, 0, 0], ![-49, -5, 1]] where
    su := ![![438, 0, 0], ![-12, 6, 0]]
    hsu := by decide
    w := ![![-12, 6, 0], ![378, 42, -6]]
    hw := by decide
    g := ![![![44, 6, -1], ![7, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-22, 13, -1], ![-802, 73, 0]], ![![715, -357, 0], ![26066, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {6} * I73N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-7, 1, 0]]
  ![-12158, -4638, -471] ![![2, 0, 0], ![-51, -5, 1]] where
    su := ![![158, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![-24316, -9276, -942], ![-151062, -57626, -5852]]
    hw := by decide
    g := ![![![55, -275, 28], ![-59, 0, 0]], ![![35, 47, -5], ![7, 0, 0]]]
    h := ![![![-40414, 5735, -12], ![-454364, 477, 0]], ![![-251073, 35625, -74], ![-2822748, 2920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-12158, -4638, -471]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 
