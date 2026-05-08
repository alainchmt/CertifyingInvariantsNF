import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F4
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R181RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![-283, -138, -7, 2] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![-2547, -1242, -63, 18], ![1332, 657, 36, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E181RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I181N0) (Ideal.span {B.equivFun.symm ![-283, -138, -7, 2]} * (J0 ^ 0*J1^ 2))
      ![![1629, 0, 0, 0], ![333, 9, 0, 0]] ![![-2547, -1242, -63, 18], ![1332, 657, 36, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R181RS0]
      rfl
    g := ![![![227835, 9687402, -4900727, 8], ![1025753, 44106400, -67, 0]], ![![57804, 2457478, -1243204, 2], ![260214, 11188800, -17, 0]]]
    h := ![![![-64596, 10258, -11166202, -301798], ![315989, -58725, 54625440, 0]], ![![33744, -5423, 5876317, 158824], ![-165068, 30992, -28747145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {9} * I181N0 =  Ideal.span {B.equivFun.symm ![-283, -138, -7, 2]} * (J0 ^ 0*J1^ 2) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E181RS0


noncomputable def R181RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![-175, -74, -3, 1] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![-525, -222, -9, 3], ![558, 231, 9, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E181RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I181N1) (Ideal.span {B.equivFun.symm ![-175, -74, -3, 1]} * (J0 ^ 1*J1^ 0))
      ![![543, 0, 0, 0], ![192, 3, 0, 0]] ![![-525, -222, -9, 3], ![558, 231, 9, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R181RS1]
      rfl
    g := ![![![25028, 247361, -271862, -3], ![74111, 815628, 0, 0]], ![![8886, 87880, -96590, -1], ![26333, 289784, 0, 0]]]
    h := ![![![-42515, 2830591, 49102, 76], ![120235, -8007145, -13755, 0]], ![![44946, -3008857, -52272, -82], ![-127110, 8511411, 14841, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {3} * I181N1 =  Ideal.span {B.equivFun.symm ![-175, -74, -3, 1]} * (J0 ^ 1*J1^ 0) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E181RS1


noncomputable def R181RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![98, 60, 5, -1] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![294, 180, 15, -3], ![-285, -174, -15, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E181RS2 : IdealEqCertificateO timesTableO (Ideal.span {3} * I181N2) (Ideal.span {B.equivFun.symm ![98, 60, 5, -1]} * (J0 ^ 0*J1^ 1))
      ![![543, 0, 0, 0], ![-267, 3, 0, 0]] ![![294, 180, 15, -3], ![-285, -174, -15, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R181RS2]
      rfl
    g := ![![![-2730, 24959, 27525, -1], ![7410, -82592, 7, 0]], ![![838, -7207, -7963, 0], ![-2122, 23896, -2, 0]]]
    h := ![![![55806, -1391382, 18741, -35], ![113492, -2828390, 6334, 0]], ![![-53847, 1348996, -18087, 33], ![-109508, 2742234, -5972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N2 : Ideal.span {3} * I181N2 =  Ideal.span {B.equivFun.symm ![98, 60, 5, -1]} * (J0 ^ 0*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E181RS2


noncomputable def R181RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![599, 331, 21, -5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![5391, 2979, 189, -45], ![-4311, -2385, -153, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E181RS3 : IdealEqCertificateO timesTableO (Ideal.span {9} * I181N3) (Ideal.span {B.equivFun.symm ![599, 331, 21, -5]} * (J0 ^ 2*J1^ 0))
      ![![1629, 0, 0, 0], ![-117, 9, 0, 0]] ![![5391, 2979, 189, -45], ![-4311, -2385, -153, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R181RS3]
      rfl
    g := ![![![6037725, 146419504, -27736704, -2311392], ![13585402, 332840459, 20802540, 0]], ![![-416977, -10112127, 1915572, 159631], ![-938242, -22986865, -1436680, 0]]]
    h := ![![![1351, -100231, 7754, -4], ![18764, -1394106, 719, 0]], ![![-1042, 80174, -6187, 2], ![-14471, 1115176, -358, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N3 : Ideal.span {9} * I181N3 =  Ideal.span {B.equivFun.symm ![599, 331, 21, -5]} * (J0 ^ 2*J1^ 0) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E181RS3


noncomputable def R193RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![86, 63, 5, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![774, 567, 45, -9], ![15840, 8037, 450, -117]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E193RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I193N0) (Ideal.span {B.equivFun.symm ![86, 63, 5, -1]} * (J0 ^ 1*J1^ 2))
      ![![1737, 0, 0, 0], ![189, 9, 0, 0]] ![![774, 567, 45, -9], ![15840, 8037, 450, -117]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R193RS0]
      rfl
    g := ![![![30311708089073, -85168136013481, 22547345301049, 3719142142565], ![714215678961198, 262757725950739, -333440, 0]], ![![4262583909579, -11976769012932, 3170720402804, 523004358823], ![100436578898618, 36950304860370, -46890, 0]]]
    h := ![![![368, -6, 17492, 833], ![-3378, 219, -160770, 0]], ![![8336, 240, 267009, 12715], ![-76528, 1481, -2454008, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N0 : Ideal.span {9} * I193N0 =  Ideal.span {B.equivFun.symm ![86, 63, 5, -1]} * (J0 ^ 1*J1^ 2) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E193RS0


noncomputable def R193RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![893, 373, 15, -5] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![8037, 3357, 135, -45], ![38376, 16758, 792, -234]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E193RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I193N1) (Ideal.span {B.equivFun.symm ![893, 373, 15, -5]} * (J0 ^ 2*J1^ 1))
      ![![1737, 0, 0, 0], ![306, 9, 0, 0]] ![![8037, 3357, 135, -45], ![38376, 16758, 792, -234]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R193RS1]
      rfl
    g := ![![![-241227533777, 243707762850, 51374909445, -6484737972], ![169429238002, 28049582942, -105, 0]], ![![-43650519180, 44099320723, 9296374404, -1173424007], ![30658499419, 5075618190, -19, 0]]]
    h := ![![![186449, -35143, 46132556, 1356875], ![-1058346, 230627, -261876880, 0]], ![![890400, -171514, 224591322, 6605798], ![-5054204, 1122302, -1274919040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {9} * I193N1 =  Ideal.span {B.equivFun.symm ![893, 373, 15, -5]} * (J0 ^ 2*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E193RS1


noncomputable def R193RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-217, -117, -10, 2] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-1953, -1053, -90, 18], ![7488, 3402, 135, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E193RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I193N2) (Ideal.span {B.equivFun.symm ![-217, -117, -10, 2]} * (J0 ^ 1*J1^ 2))
      ![![1737, 0, 0, 0], ![531, 9, 0, 0]] ![![-1953, -1053, -90, 18], ![7488, 3402, 135, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R193RS2]
      rfl
    g := ![![![484, -172, 106, 13], ![3016, 1108, 0, 0]], ![![71257, -199060, 52726, 8692], ![1670396, 614460, -26, 0]]]
    h := ![![![-4516, 85040, 1560, 2], ![14769, -278434, -384, 0]], ![![16867, -327139, -6079, -9], ![-55161, 1071074, 1732, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {9} * I193N2 =  Ideal.span {B.equivFun.symm ![-217, -117, -10, 2]} * (J0 ^ 1*J1^ 2) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E193RS2


noncomputable def R193RS3 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![230, 130, 9, -2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![2070, 1170, 81, -18], ![3654, 1710, 18, -18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E193RS3 : IdealEqCertificateO timesTableO (Ideal.span {9} * I193N3) (Ideal.span {B.equivFun.symm ![230, 130, 9, -2]} * (J0 ^ 2*J1^ 1))
      ![![1737, 0, 0, 0], ![702, 9, 0, 0]] ![![2070, 1170, 81, -18], ![3654, 1710, 18, -18]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R193RS3]
      rfl
    g := ![![![-371411357872, 375229293171, 79100681663, -9984415492], ![260874589608, 43193833040, 1062840, 0]], ![![-154754731376, 156345537918, 32958617161, -4160173097], ![108697744992, 17997430320, 442850, 0]]]
    h := ![![![190634, -22950760, -335455, -528], ![-471694, 56794468, 101902, 0]], ![![336484, -40525797, -592312, -932], ![-832577, 100286046, 179874, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N3 : Ideal.span {9} * I193N3 =  Ideal.span {B.equivFun.symm ![230, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E193RS3


noncomputable def R229RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![212, 130, 9, -2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![1908, 1170, 81, -18], ![5706, 3582, 234, -54]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E229RS0 : IdealEqCertificateO timesTableO (Ideal.span {9} * I229N0) (Ideal.span {B.equivFun.symm ![212, 130, 9, -2]} * (J0 ^ 2*J1^ 1))
      ![![2061, 0, 0, 0], ![396, 9, 0, 0]] ![![1908, 1170, 81, -18], ![5706, 3582, 234, -54]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R229RS0]
      rfl
    g := ![![![-110861584383559697788, 112001429799318642603, 23610504854876647673, -2980208414545280496], ![77865049501006267511, 12890822327108880136, -352374, 0]], ![![-25284220499494842862, 25544185238296297710, 5384851877902831403, -679696642500693181], ![17758695148862419402, 2940012051521490334, -80366, 0]]]
    h := ![![![55708, -7772, 11226703, 255157], ![-289930, 47042, -58430955, 0]], ![![166674, -23810, 34306878, 779716], ![-867448, 143644, -178554970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N0 : Ideal.span {9} * I229N0 =  Ideal.span {B.equivFun.symm ![212, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E229RS0


noncomputable def R229RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![104, 63, 5, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![936, 567, 45, -9], ![5688, 2997, 180, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E229RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I229N1) (Ideal.span {B.equivFun.symm ![104, 63, 5, -1]} * (J0 ^ 1*J1^ 2))
      ![![2061, 0, 0, 0], ![630, 9, 0, 0]] ![![936, 567, 45, -9], ![5688, 2997, 180, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R229RS1]
      rfl
    g := ![![![233177788, -655168473, 173448607, 28610007], ![5494208206, 2021301476, -229, 0]], ![![71277770, -200270581, 53019482, 8745455], ![1679460119, 617867958, -70, 0]]]
    h := ![![![2006, -40804, -653, -1], ![-6561, 133582, 228, 0]], ![![12998, -248286, -3898, -5], ![-42513, 812862, 1140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {9} * I229N1 =  Ideal.span {B.equivFun.symm ![104, 63, 5, -1]} * (J0 ^ 1*J1^ 2) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E229RS1
