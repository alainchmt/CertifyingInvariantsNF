import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F1
import IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupSaturated4_0_76176_2_3

noncomputable section

def R2RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 5*J1^ 0) ![2, -1, -3, 5] ![![8, 0, 0, 0], ![3, 2, 3, -5]]
  ![![16, -8, -24, 40], ![16, -8, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_0
    hmul := by decide

def E2RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {8} * I2N0) (Ideal.span {B.equivFun.symm ![2, -1, -3, 5]} * (J0 ^ 5*J1^ 0))
      ![![16, 0, 0, 0], ![0, 8, 0, 0]] ![![16, -8, -24, 40], ![16, -8, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 8 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS0]
      rfl
    g := ![![![161734, -10335, -40810, 110190], ![-26098, -67527, 15, 0]], ![![-162614, 10388, 41027, -110780], ![26249, 67893, -15, 0]]]
    h := ![![![601, -902, -482, 1315], ![678, -239, -75, 0]], ![![1, 0, 0, 0], ![-1, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![2, -1, -3, 5]} * (J0 ^ 5*J1^ 0) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS0


def R2RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![1, 0, 0, 0] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![2, 0, 0, 0], ![3, -1, 0, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {1} * I2N1) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0))
      ![![2, 0, 0, 0], ![3, -1, 0, 1]] ![![2, 0, 0, 0], ![3, -1, 0, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS1]
      rfl
    g := ![![![-59, -67, -301, 503], ![200, -68, 2, 0]], ![![-60, -70, -310, 519], ![205, -70, 2, 0]]]
    h := ![![![-59, -67, -301, 503], ![200, -68, 2, 0]], ![![-60, -70, -310, 519], ![205, -70, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS1



def R3RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 4*J1^ 1) ![-2, 1, 0, -1] ![![12, 0, 0, 0], ![10, -4, -2, 8]]
  ![![-24, 12, 0, -12], ![60, 12, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_4J1_1
    hmul := by decide

def E3RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {12} * I3N0) (Ideal.span {B.equivFun.symm ![-2, 1, 0, -1]} * (J0 ^ 4*J1^ 1))
      ![![36, 0, 0, 0], ![-12, 0, -24, 36]] ![![-24, 12, 0, -12], ![60, 12, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS0]
      rfl
    g := ![![![127663, 135391, 321921, -546185], ![-356517, 127109, 4, 0]], ![![-101741, -107899, -256555, 435281], ![284131, -101300, -3, 0]]]
    h := ![![![-174, 50, 32, -81], ![-42, -25, 4, 0]], ![![417, -118, -74, 188], ![100, 59, -10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {12} * I3N0 =  Ideal.span {B.equivFun.symm ![-2, 1, 0, -1]} * (J0 ^ 4*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS0

def R3RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 2*J1^ 1) ![1, 0, 0, 0] ![![6, 0, 0, 0], ![-2, 2, -2, 2]]
  ![![6, 0, 0, 0], ![-2, 2, -2, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

def E3RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I3N1) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 2*J1^ 1))
      ![![6, 0, 0, 0], ![4, -4, 0, 2]] ![![6, 0, 0, 0], ![-2, 2, -2, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS1]
      rfl
    g := ![![![23, -14, -16, 32], ![6, 6, 0, 0]], ![![6959, -4251, -5153, 10176], ![1375, 1866, -20, 0]]]
    h := ![![![203, -122, -1020, 1601], ![753, -300, 6, 0]], ![![-101, 61, 493, -775], ![-362, 145, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 2*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS1


def R5RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 3*J1^ 1) ![8, -1, -3, 7] ![![12, 0, 0, 0], ![6, 2, 8, -12]]
  ![![96, -12, -36, 84], ![84, -60, -36, 108]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_3J1_1
    hmul := by decide

def E5RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {12} * I5N0) (Ideal.span {B.equivFun.symm ![8, -1, -3, 7]} * (J0 ^ 3*J1^ 1))
      ![![60, 0, 0, 0], ![-12, -12, -24, 48]] ![![96, -12, -36, 84], ![84, -60, -36, 108]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R5RS0]
      rfl
    g := ![![![3619502390974, -779159763714, -842155276793, 2292164649445], ![-1173710265763, -649852239054, 434480, 0]], ![![-666202310823, 143411435887, 155006332602, -421893736015], ![216032041653, 119611210765, -79970, 0]]]
    h := ![![![-629, -422, -9, -295], ![-21, 0, 0, -522]], ![![-839, -563, -11, -395], ![-26, 0, 0, -696]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {12} * I5N0 =  Ideal.span {B.equivFun.symm ![8, -1, -3, 7]} * (J0 ^ 3*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E5RS0


def R5RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 3*J1^ 1) ![-4, -1, 3, -5] ![![12, 0, 0, 0], ![6, 2, 8, -12]]
  ![![-48, -12, 36, -60], ![-228, 72, 48, -120]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_3J1_1
    hmul := by decide

def E5RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {12} * I5N1) (Ideal.span {B.equivFun.symm ![-4, -1, 3, -5]} * (J0 ^ 3*J1^ 1))
      ![![60, 0, 0, 0], ![-36, 12, 0, 0]] ![![-48, -12, 36, -60], ![-228, 72, 48, -120]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R5RS1]
      rfl
    g := ![![![9049002542, -1947958546, -2105460026, 5730622908], ![-2934421399, -1624683220, -7898, 0]], ![![-4113185341, 885436210, 957027829, -2604830083], ![1333828683, 738492797, 3590, 0]]]
    h := ![![![-2, 2, 0, -1], ![-2, 3, 0, 0]], ![![-35, 14, 0, -2], ![-52, 4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {12} * I5N1 =  Ideal.span {B.equivFun.symm ![-4, -1, 3, -5]} * (J0 ^ 3*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E5RS1


def R13RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 5*J1^ 1) ![2, 5, 3, -5] ![![24, 0, 0, 0], ![-14, 16, 14, -34]]
  ![![48, 120, 72, -120], ![168, 240, 288, -576]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_1
    hmul := by decide

def E13RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {24} * I13N0) (Ideal.span {B.equivFun.symm ![2, 5, 3, -5]} * (J0 ^ 5*J1^ 1))
      ![![312, 0, 0, 0], ![192, -24, 0, 24]] ![![48, 120, 72, -120], ![168, 240, 288, -576]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 24 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R13RS0]
      rfl
    g := ![![![3059486563861382633, 629474044491309961, 1831855591494108924, -2502237619577828023], ![3248367923515220059, -1397526330079245234, -6421910, 0]], ![![1766595269846439283, 363468133060197435, 1057741995405561593, -1444831036354988772], ![1875658313452520406, -806953504344824436, -3708111, 0]]]
    h := ![![![94894660, 7101589, -227535216, 447967121], ![92309456, -328661979, 3732, 0]], ![![260961725, 19529474, -625725213, 1231916216], ![253852363, -903825309, 10263, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {24} * I13N0 =  Ideal.span {B.equivFun.symm ![2, 5, 3, -5]} * (J0 ^ 5*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E13RS0


def R13RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-5, 1, 0, -1] ![![6, 0, 0, 0], ![0, -1, -1, 3]]
  ![![-30, 6, 0, -6], ![18, 6, 6, -12]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E13RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {6} * I13N1) (Ideal.span {B.equivFun.symm ![-5, 1, 0, -1]} * (J0 ^ 1*J1^ 1))
      ![![78, 0, 0, 0], ![30, -6, 0, 6]] ![![-30, 6, 0, -6], ![18, 6, 6, -12]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R13RS1]
      rfl
    g := ![![![-4652, 65241, 66018, -123528], ![-83639, 48904, 2330, 0]], ![![-1396, 19571, 19804, -37056], ![-25089, 14670, 699, 0]]]
    h := ![![![-717, 417, 1368, -2697], ![-508, 1976, 0, 0]], ![![2554404, -1488473, -4889900, 9638266], ![1838367, -7063364, 525, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {6} * I13N1 =  Ideal.span {B.equivFun.symm ![-5, 1, 0, -1]} * (J0 ^ 1*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E13RS1


def R13RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 5*J1^ 1) ![-10, 5, 9, -17] ![![24, 0, 0, 0], ![-14, 16, 14, -34]]
  ![![-240, 120, 216, -408], ![216, -72, -24, 24]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_1
    hmul := by decide

def E13RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {24} * I13N2) (Ideal.span {B.equivFun.symm ![-10, 5, 9, -17]} * (J0 ^ 5*J1^ 1))
      ![![312, 0, 0, 0], ![-96, -24, 0, 24]] ![![-240, 120, 216, -408], ![216, -72, -24, 24]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 24 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R13RS2]
      rfl
    g := ![![![828823452395560, 170526276195328, 496254794221703, -677863157301206], ![879991939705543, -378593784643726, -29936, 0]], ![![-466214711287816, -95921342951399, -279144231433807, 381299268572117], ![-494997079196574, 212959697861928, 16839, 0]]]
    h := ![![![-64293170, 125550574, 94414395, -188493694], ![-4374727, 136377990, -1232, 0]], ![![64291421, -125547148, -94411819, 188488550], ![4374623, -136374270, 1232, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {24} * I13N2 =  Ideal.span {B.equivFun.symm ![-10, 5, 9, -17]} * (J0 ^ 5*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E13RS2


def R13RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1, 1, 0, -1] ![![6, 0, 0, 0], ![0, -1, -1, 3]]
  ![![6, 6, 0, -6], ![18, 0, 0, 6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E13RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {6} * I13N3) (Ideal.span {B.equivFun.symm ![1, 1, 0, -1]} * (J0 ^ 1*J1^ 1))
      ![![78, 0, 0, 0], ![-6, -6, 0, 6]] ![![6, 6, 0, -6], ![18, 0, 0, 6]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R13RS3]
      rfl
    g := ![![![2511, -179, -31, 666], ![370, -897, 442, 0]], ![![-290, 19, 2, -74], ![-39, 102, -51, 0]]]
    h := ![![![6240, -8775, -8865, 17655], ![1559, -12870, 65, 0]], ![![2889, -4062, -4104, 8173], ![726, -5958, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N3 : Ideal.span {6} * I13N3 =  Ideal.span {B.equivFun.symm ![1, 1, 0, -1]} * (J0 ^ 1*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E13RS3


def R23RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![5, 2, 3, -5] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![30, 12, 18, -30], ![-24, 18, 24, -60]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E23RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {6} * I23N0) (Ideal.span {B.equivFun.symm ![5, 2, 3, -5]} * (J0 ^ 0*J1^ 1))
      ![![138, 0, 0, 0], ![60, -6, 0, 6]] ![![30, 12, 18, -30], ![-24, 18, 24, -60]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R23RS0]
      rfl
    g := ![![![8746347, 5247745, 7021550, -14701375], ![9635393, -6784879, -15281, 0]], ![![3782200, 2269292, 3036342, -6357343], ![4166651, -2933998, -6608, 0]]]
    h := ![![![339575, 150042, -636687, 1264701], ![196126, -1627032, 258, 0]], ![![-94878, -41917, 177875, -353328], ![-54772, 454553, -72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {6} * I23N0 =  Ideal.span {B.equivFun.symm ![5, 2, 3, -5]} * (J0 ^ 0*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E23RS0


def R23RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-7, 2, 3, -5] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![-42, 12, 18, -30], ![24, 6, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E23RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {6} * I23N1) (Ideal.span {B.equivFun.symm ![-7, 2, 3, -5]} * (J0 ^ 0*J1^ 1))
      ![![138, 0, 0, 0], ![-36, -6, 0, 6]] ![![-42, 12, 18, -30], ![24, 6, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R23RS1]
      rfl
    g := ![![![3869, 2350, 3040, -6345], ![4118, -2829, -46, 0]], ![![-1090, -663, -858, 1791], ![-1160, 798, 13, 0]]]
    h := ![![![-1085777, 2518100, 1612720, -3234959], ![33137, 4136607, -9779, 0]], ![![1170380, -2714282, -1738366, 3486991], ![-35678, -4458888, 10541, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {6} * I23N1 =  Ideal.span {B.equivFun.symm ![-7, 2, 3, -5]} * (J0 ^ 0*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E23RS1
