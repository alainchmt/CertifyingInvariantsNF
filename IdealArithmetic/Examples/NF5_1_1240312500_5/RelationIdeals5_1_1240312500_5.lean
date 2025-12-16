import IdealArithmetic.Examples.NF5_1_1240312500_5.PrimesBelow5_1_1240312500_5F36
import IdealArithmetic.Examples.NF5_1_1240312500_5.ClassGroupSaturated5_1_1240312500_5_2

noncomputable section

def R2RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![1291, -27, 511, 669, -1434] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![2582, -54, 1022, 1338, -2868], ![6878, -5136, -2750, -2396, 6502]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2N0) (Ideal.span {B.equivFun.symm ![1291, -27, 511, 669, -1434]} * (J0 ^ 1*J1^ 0)) 
      ![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]] ![![2582, -54, 1022, 1338, -2868], ![6878, -5136, -2750, -2396, 6502]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS0]  
      rfl
    g := ![![![1439, -2871, -82, 103, -1605], ![-4437, 0, 0, 0, 0]], ![![4115, -4854, -286, -170, -1769], ![-7865, 0, 0, 0, 0]]]
    h := ![![![158447, -598840, 0, -545334, 1348887], ![-299419, -876692, 0, -20667, -1866]], ![![1038956, -3945714, 0, -3595367, 8893864], ![-1972857, -5780107, 0, -135516, -13911]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![1291, -27, 511, 669, -1434]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS0
                    

def R2RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![7, 1, 4, 5, -11] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![14, 2, 8, 10, -22], ![48, 0, 20, 26, -56]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E2RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2N1) (Ideal.span {B.equivFun.symm ![7, 1, 4, 5, -11]} * (J0 ^ 0*J1^ 1)) 
      ![![4, 0, 0, 0, 0], ![-22, -14, -8, -10, 26]] ![![14, 2, 8, 10, -22], ![48, 0, 20, 26, -56]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS1]  
      rfl
    g := ![![![12, -5, -2, 0, -1], ![-17, 0, 0, 0, 0]], ![![13, 17, 2, -6, 21], ![33, 0, 0, 0, 0]]]
    h := ![![![-1702778, 817272, 240867, 162585, -637436], ![1473359, -538752, -2286, 48, 0]], ![![-4343936, 2084936, 614473, 414768, -1626154], ![3758662, -1374402, -5832, 123, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![7, 1, 4, 5, -11]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS1
                    

def R2RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-39, -18, -9, -11, 28] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-156, -72, -36, -44, 112], ![-192, -120, -76, -104, 276]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2N2) (Ideal.span {B.equivFun.symm ![-39, -18, -9, -11, 28]} * (J0 ^ 1*J1^ 1)) 
      ![![8, 0, 0, 0, 0], ![-72, -44, -24, -32, 84]] ![![-156, -72, -36, -44, 112], ![-192, -120, -76, -104, 276]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS2]  
      rfl
    g := ![![![61, -63, -18, -38, 74], ![-72, 14, 0, 0, 0]], ![![-363, 349, 95, 202, -393], ![375, -70, 0, 0, 0]]]
    h := ![![![-169852926, 151828693, -54800664, 14617175, -38167192], ![398796386, -131565714, 0, -77287, -77]], ![![-400825920, 358291595, -129320865, 34494205, -90068493], ![941096120, -310474185, 0, -182385, -182]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {4} * I2N2 =  Ideal.span {B.equivFun.symm ![-39, -18, -9, -11, 28]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS2
                    

def R3RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![18, 10, 6, 8, -21] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![36, 20, 12, 16, -42], ![-24, -20, -14, -20, 54]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E3RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I3N0) (Ideal.span {B.equivFun.symm ![18, 10, 6, 8, -21]} * (J0 ^ 0*J1^ 1)) 
      ![![6, 0, 0, 0, 0], ![0, 2, 0, 0, 0]] ![![36, 20, 12, 16, -42], ![-24, -20, -14, -20, 54]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS0]  
      rfl
    g := ![![![6, 1, 1, 1, -3], ![1, 0, 0, 0, 0]], ![![-9, 0, -1, -1, 3], ![-1, 0, 0, 0, 0]]]
    h := ![![![6, -9, 0, -24, -7], ![-3, 6, 40, 0, 0]], ![![-4, 12, 0, 30, 9], ![4, -7, -50, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![18, 10, 6, 8, -21]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS0
                    

def R3RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-297, 265, 166, 155, -403] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-594, 530, 332, 310, -806], ![-1612, 1558, 1032, 984, -2526]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E3RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I3N1) (Ideal.span {B.equivFun.symm ![-297, 265, 166, 155, -403]} * (J0 ^ 0*J1^ 1)) 
      ![![6, 0, 0, 0, 0], ![-2, 2, 0, 0, 0]] ![![-594, 530, 332, 310, -806], ![-1612, 1558, 1032, 984, -2526]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS1]  
      rfl
    g := ![![![105, -49, -8, -10, 15], ![-45, 0, 0, 0, 0]], ![![-85, 60, 4, 23, -47], ![-42, 0, 0, 0, 0]]]
    h := ![![![286, 3987, -7295, 13335, 3699], ![465, -3854, -22225, 0, -230]], ![![658, 9803, -17898, 32724, 9079], ![1070, -9450, -54540, 0, -570]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![-297, 265, 166, 155, -403]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS1
                    

def R7RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-67, -25, -10, -10, 23] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-268, -100, -40, -40, 92], ![-876, -500, -300, -408, 1080]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E7RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I7N0) (Ideal.span {B.equivFun.symm ![-67, -25, -10, -10, 23]} * (J0 ^ 1*J1^ 1)) 
      ![![28, 0, 0, 0, 0], ![-48, -16, -16, -20, 52]] ![![-268, -100, -40, -40, 92], ![-876, -500, -300, -408, 1080]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R7RS0]  
      rfl
    g := ![![![10714, -9176, -1789, -4037, 8233], ![-3775, 440, 0, 0, 0]], ![![-23777, 20529, 4118, 9240, -18763], ![9426, -1210, 0, 0, 0]]]
    h := ![![![-497716, -558720, 205038, -64685, 107425], ![1301095, -528798, 0, 0, -1023]], ![![-1943481, -2181713, 800613, -252606, 419538], ![5080506, -2064846, 0, 0, -3996]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![-67, -25, -10, -10, 23]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E7RS0
                    

def R7RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![3, -3, -2, -2, 5] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![12, -12, -8, -8, 20], ![-36, 20, 12, 8, -24]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E7RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I7N1) (Ideal.span {B.equivFun.symm ![3, -3, -2, -2, 5]} * (J0 ^ 1*J1^ 1)) 
      ![![28, 0, 0, 0, 0], ![-36, -28, -16, -20, 52]] ![![12, -12, -8, -8, 20], ![-36, 20, 12, 8, -24]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R7RS1]  
      rfl
    g := ![![![-2747, 2646, 736, 1555, -3025], ![2889, -550, 0, 0, 0]], ![![10133, -9841, -2726, -5774, 11223], ![-10803, 2035, 0, 0, 0]]]
    h := ![![![852726, -194027, 7251, 40983, -58744], ![-1044837, 420875, 2265, 0, 54]], ![![-11097843, 2525204, -94356, -533361, 764487], ![13598148, -5477514, -29479, 0, -702]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![3, -3, -2, -2, 5]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E7RS1
                    

def R17RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-74, 82, 18, 34, -75] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-148, 164, 36, 68, -150], ![-268, -20, -34, -32, 94]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E17RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I17N1) (Ideal.span {B.equivFun.symm ![-74, 82, 18, 34, -75]} * (J0 ^ 0*J1^ 1)) 
      ![![34, 0, 0, 0, 0], ![-14, 2, 0, 0, 0]] ![![-148, 164, 36, 68, -150], ![-268, -20, -34, -32, 94]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R17RS1]  
      rfl
    g := ![![![-402, 221, 77, 49, -163], ![-1, 0, 0, 0, 0]], ![![119, -96, -8, 3, 21], ![-12, 0, 0, 0, 0]]]
    h := ![![![-843574, 508821, -3728119, 1078538, -12723], ![-2044992, -376147, -9117792, 1716, 0]], ![![2332374, -1407283, 10312554, -2983396, 35179], ![5654186, 1040547, 25221224, -4746, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-74, 82, 18, 34, -75]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E17RS1
                    

def R23RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-10356, -6047, -3679, -4953, 13063] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-41424, -24188, -14716, -19812, 52252], ![63336, 32912, 18324, 23692, -61608]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E23RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I23N1) (Ideal.span {B.equivFun.symm ![-10356, -6047, -3679, -4953, 13063]} * (J0 ^ 1*J1^ 1)) 
      ![![92, 0, 0, 0, 0], ![-24, -48, -16, -20, 52]] ![![-41424, -24188, -14716, -19812, 52252], ![63336, 32912, 18324, 23692, -61608]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R23RS1]  
      rfl
    g := ![![![1912162, -1578778, -267346, -622119, 1296368], ![-310421, -2562, 0, 0, 0]], ![![2300032, -1901516, -323780, -752489, 1566669], ![-388840, 366, 0, 0, 0]]]
    h := ![![![-6839138796, 171094128, -2499896424, -1835665196, 4580230878], ![5117505058, -5193514395, -10819730, 0, 0]], ![![9427808046, -235854628, 3446127389, 2530479246, -6313885133], ![-7054521956, 7159301520, 14915065, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![-10356, -6047, -3679, -4953, 13063]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E23RS1
                    

def R31RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-6577, -3477, -1963, -2555, 6660] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-13154, -6954, -3926, -5110, 13320], ![37180, 20644, 12112, 16048, -42094]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E31RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I31N1) (Ideal.span {B.equivFun.symm ![-6577, -3477, -1963, -2555, 6660]} * (J0 ^ 1*J1^ 0)) 
      ![![62, 0, 0, 0, 0], ![24, 2, 0, 0, 0]] ![![-13154, -6954, -3926, -5110, 13320], ![37180, 20644, 12112, 16048, -42094]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R31RS1]  
      rfl
    g := ![![![-2150, 1149, 74, 356, -695], ![-203, 0, 0, 0, 0]], ![![-501, 289, 15, 85, -168], ![-42, 0, 0, 0, 0]]]
    h := ![![![261555467, 52839967, 543628066, 88343799, 9361080], ![-672806667, 23982445, -1414240027, -2303070, 0]], ![![-781849258, -157950196, -1625017631, -264077988, -27982385], ![2011173314, -71688179, 4227458392, 6884388, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![-6577, -3477, -1963, -2555, 6660]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E31RS1
                    

def R31RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![84, -117, -93, -94, 233] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![168, -234, -186, -188, 466], ![404, -656, -550, -564, 1386]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E31RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I31N2) (Ideal.span {B.equivFun.symm ![84, -117, -93, -94, 233]} * (J0 ^ 0*J1^ 1)) 
      ![![62, 0, 0, 0, 0], ![-22, 2, 0, 0, 0]] ![![168, -234, -186, -188, 466], ![404, -656, -550, -564, 1386]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R31RS2]  
      rfl
    g := ![![![-68, -54, 20, 21, -79], ![69, 0, 0, 0, 0]], ![![-1, 31, -2, 2, 4], ![-22, 0, 0, 0, 0]]]
    h := ![![![-68360719, 13155522, -104338219, 18797986, 383393], ![-192781568, -6604584, -294292905, -94325, 0]], ![![-234901141, 45204783, -358523403, 64592998, 1317393], ![-662436118, -22694422, -1011239175, -324115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {2} * I31N2 =  Ideal.span {B.equivFun.symm ![84, -117, -93, -94, 233]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E31RS2
                    

def R37RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![2, 31, 21, 30, -67] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![4, 62, 42, 60, -134], ![144, 28, 78, 104, -226]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E37RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I37N0) (Ideal.span {B.equivFun.symm ![2, 31, 21, 30, -67]} * (J0 ^ 0*J1^ 1)) 
      ![![74, 0, 0, 0, 0], ![-46, 14, -8, -10, 26]] ![![4, 62, 42, 60, -134], ![144, 28, 78, 104, -226]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R37RS0]  
      rfl
    g := ![![![270, -220, -78, -5, -31], ![-575, 0, 0, 0, 0]], ![![382, -151, -78, -43, 94], ![-458, 0, 0, 0, 0]]]
    h := ![![![4397080013, 5750468386, -1102378257, 1897296504, -4787517949], ![-3464709819, 6732628371, 59010, 0, 0]], ![![12586240005, 16460190663, -3155457103, 5430837989, -13703832950], ![-9917415513, 19271533932, 168910, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {2} * I37N0 =  Ideal.span {B.equivFun.symm ![2, 31, 21, 30, -67]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E37RS0
                    

def R37RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-40, 49, 12, 22, -50] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-80, 98, 24, 44, -100], ![-502, 608, 150, 274, -622]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E37RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I37N1) (Ideal.span {B.equivFun.symm ![-40, 49, 12, 22, -50]} * (J0 ^ 1*J1^ 0)) 
      ![![74, 0, 0, 0, 0], ![28, 2, 0, 0, 0]] ![![-80, 98, 24, 44, -100], ![-502, 608, 150, 274, -622]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R37RS1]  
      rfl
    g := ![![![-49, 38, 4, 5, 5], ![67, 0, 0, 0, 0]], ![![-20, 20, 3, 4, -2], ![32, 0, 0, 0, 0]]]
    h := ![![![92671096, 42661395, 670613900, 95984474, -240818], ![-244992238, 31848236, -1774404512, 70716, 0]], ![![573797802, 264149376, 4152284312, 594313398, -1491089], ![-1516934770, 197196828, -10986697440, 437857, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-40, 49, 12, 22, -50]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E37RS1
                    

def R37RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![1484, -1426, -941, -896, 2302] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![2968, -2852, -1882, -1792, 4604], ![-2686, -1594, -2872, -3362, 7658]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E37RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I37N2) (Ideal.span {B.equivFun.symm ![1484, -1426, -941, -896, 2302]} * (J0 ^ 1*J1^ 0)) 
      ![![74, 0, 0, 0, 0], ![30, 2, 0, 0, 0]] ![![2968, -2852, -1882, -1792, 4604], ![-2686, -1594, -2872, -3362, 7658]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R37RS2]  
      rfl
    g := ![![![-2469, 1179, 203, 333, -347], ![2451, 0, 0, 0, 0]], ![![-1253, 584, 101, 171, -193], ![1175, 0, 0, 0, 0]]]
    h := ![![![-1009681708, -639743343, -11848082540, -1584715496, 12257836], ![2494147817, -555203736, 29252445138, -3599505, 0]], ![![-976729004, -618857709, -11461270911, -1532978143, 11856901], ![2412746545, -537077222, 28297423161, -3481758, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {2} * I37N2 =  Ideal.span {B.equivFun.symm ![1484, -1426, -941, -896, 2302]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E37RS2
                    

def R37RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![11, 7, 4, 5, -13] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![22, 14, 8, 10, -26], ![-72, -34, -20, -28, 74]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E37RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I37N3) (Ideal.span {B.equivFun.symm ![11, 7, 4, 5, -13]} * (J0 ^ 0*J1^ 1)) 
      ![![74, 0, 0, 0, 0], ![-14, 2, 0, 0, 0]] ![![22, 14, 8, 10, -26], ![-72, -34, -20, -28, 74]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R37RS3]  
      rfl
    g := ![![![103, -47, -2, -14, 25], ![9, 0, 0, 0, 0]], ![![-29, 17, 2, 6, -12], ![-2, 0, 0, 0, 0]]]
    h := ![![![3897684, -5576845, 38282219, -10884549, -124519], ![20680396, 2028874, 202424544, 36565, 0]], ![![-11201084, 16026665, -110014884, 31279858, 357841], ![-59430896, -5830482, -581724700, -105080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N3 : Ideal.span {2} * I37N3 =  Ideal.span {B.equivFun.symm ![11, 7, 4, 5, -13]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E37RS3
                    

def R41RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-1429, -777, -448, -589, 1541] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-2858, -1554, -896, -1178, 3082], ![5220, 3194, 2008, 2740, -7258]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E41RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I41N0) (Ideal.span {B.equivFun.symm ![-1429, -777, -448, -589, 1541]} * (J0 ^ 0*J1^ 1)) 
      ![![82, 0, 0, 0, 0], ![2, -36, -8, -10, 26]] ![![-2858, -1554, -896, -1178, 3082], ![5220, 3194, 2008, 2740, -7258]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS0]  
      rfl
    g := ![![![33157, -18752, -2066, -6389, 12642], ![2257, 0, 0, 0, 0]], ![![49719, -28130, -3102, -9586, 18971], ![3383, 0, 0, 0, 0]]]
    h := ![![![-30073189588, 817382765, -16487783192, -9628549254, 24368966294], ![9417179599, -33984256900, -1566080, 0, 0]], ![![56884640884, -1546112151, 31187301350, 18212786026, -46094874429], ![-17812971770, 64282581130, 2962304, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2} * I41N0 =  Ideal.span {B.equivFun.symm ![-1429, -777, -448, -589, 1541]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS0
                    

def R41RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![2494, -3041, -751, -1373, 3117] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![9976, -12164, -3004, -5492, 12468], ![57360, -69888, -17252, -31548, 71616]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E41RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I41N1) (Ideal.span {B.equivFun.symm ![2494, -3041, -751, -1373, 3117]} * (J0 ^ 1*J1^ 1)) 
      ![![164, 0, 0, 0, 0], ![-112, -4, -16, -20, 52]] ![![9976, -12164, -3004, -5492, 12468], ![57360, -69888, -17252, -31548, 71616]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS1]  
      rfl
    g := ![![![-6505, 6345, 1753, 3726, -7239], ![7013, -1308, 0, 0, 0]], ![![11402, -11078, -3070, -6504, 12643], ![-12176, 2289, 0, 0, 0]]]
    h := ![![![575364886398, 943459838388, 48938208005, 293976203704, -741060276592], ![-691538880556, 1193130857304, 3522213, 0, 0]], ![![3312703098648, 5432035224948, 281765114855, 1692588310425, -4266705759432], ![-3981582899247, 6869533371894, 20279385, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {4} * I41N1 =  Ideal.span {B.equivFun.symm ![2494, -3041, -751, -1373, 3117]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS1
                    

def R41RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-4623, -2526, -1464, -1929, 5050] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-9246, -5052, -2928, -3858, 10100], ![21460, 12382, 7470, 10020, -26394]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E41RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I41N2) (Ideal.span {B.equivFun.symm ![-4623, -2526, -1464, -1929, 5050]} * (J0 ^ 1*J1^ 0)) 
      ![![82, 0, 0, 0, 0], ![-20, 2, 0, 0, 0]] ![![-9246, -5052, -2928, -3858, 10100], ![21460, 12382, 7470, 10020, -26394]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R41RS2]  
      rfl
    g := ![![![10165, -5138, -536, -1692, 3389], ![999, 0, 0, 0, 0]], ![![-3588, 1826, 191, 601, -1206], ![-350, 0, 0, 0, 0]]]
    h := ![![![1691898157, -219957379, 416349672, -90368655, 12986138], ![6930444494, -6833754, 1723675419, -4225608, 0]], ![![-4064854260, 528456826, -1000300451, 217115010, -31199649], ![-16650675296, 16418278, -4141214259, 10152162, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2} * I41N2 =  Ideal.span {B.equivFun.symm ![-4623, -2526, -1464, -1929, 5050]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E41RS2
                    

def R43RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![21, 18, 27, 32, -73] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![84, 72, 108, 128, -292], ![84, -336, -368, -376, 912]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E43RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I43N1) (Ideal.span {B.equivFun.symm ![21, 18, 27, 32, -73]} * (J0 ^ 1*J1^ 1)) 
      ![![172, 0, 0, 0, 0], ![0, 4, 0, 0, 0]] ![![84, 72, 108, 128, -292], ![84, -336, -368, -376, 912]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R43RS1]  
      rfl
    g := ![![![103621, -98712, -27643, -58314, 113726], ![-107481, 20580, 0, 0, 0]], ![![1779, -1622, -467, -978, 1926], ![-1742, 343, 0, 0, 0]]]
    h := ![![![-1113, -566275, 0, -1139768, -9355], ![-13141, 130899, 24586424, 3192, 0]], ![![-1113, -565835, 0, -1138886, -9348], ![-13137, 130780, 24567398, 3192, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {4} * I43N1 =  Ideal.span {B.equivFun.symm ![21, 18, 27, 32, -73]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E43RS1
                    

def R53RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1470, 894, 558, 759, -2009] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![5880, 3576, 2232, 3036, -8036], ![-12072, -6436, -3648, -4756, 12408]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E53RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I53N1) (Ideal.span {B.equivFun.symm ![1470, 894, 558, 759, -2009]} * (J0 ^ 1*J1^ 1)) 
      ![![212, 0, 0, 0, 0], ![8, 4, 0, 0, 0]] ![![5880, 3576, 2232, 3036, -8036], ![-12072, -6436, -3648, -4756, 12408]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R53RS1]  
      rfl
    g := ![![![-2809871, 2292087, 368214, 867491, -1822906], ![283457, 42300, 0, 0, 0]], ![![153277, -128232, -22914, -52680, 108857], ![-35282, 2115, 0, 0, 0]]]
    h := ![![![-294023503, -554631378, -818559155, -818995302, -1836583], ![7785829702, -29296112, 21722302500, 772515, 0]], ![![558438278, 1053412508, 1554692238, 1555520617, 3488214], ![-14787611576, 55642284, -41257244325, -1467240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![1470, 894, 558, 759, -2009]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E53RS1
                    

def R59RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![105247, 55505, 31274, 40667, -105969] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![210494, 111010, 62548, 81334, -211938], ![-555076, -321690, -194676, -261480, 689086]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E59RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I59N1) (Ideal.span {B.equivFun.symm ![105247, 55505, 31274, 40667, -105969]} * (J0 ^ 0*J1^ 1)) 
      ![![118, 0, 0, 0, 0], ![46, 2, 0, 0, 0]] ![![210494, 111010, 62548, 81334, -211938], ![-555076, -321690, -194676, -261480, 689086]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R59RS1]  
      rfl
    g := ![![![-49553, 28114, 3176, 9457, -18884], ![-3281, 0, 0, 0, 0]], ![![-15657, 8863, 1028, 2990, -5986], ![-1036, 0, 0, 0, 0]]]
    h := ![![![36545128037, 7962506028, 198304378565, 17275454825, -117752055], ![-93782152362, 5943822725, -508853978640, 55137026, 0]], ![![-100603126468, -21919572204, -545902000803, -47556718148, 324155161], ![258167867268, -16362447983, 1400798141112, -151784206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![105247, 55505, 31274, 40667, -105969]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E59RS1
                    

def R59RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-1327, 1641, 404, 746, -1689] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-5308, 6564, 1616, 2984, -6756], ![-31620, 38220, 9364, 17136, -38928]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E59RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I59N2) (Ideal.span {B.equivFun.symm ![-1327, 1641, 404, 746, -1689]} * (J0 ^ 1*J1^ 1)) 
      ![![236, 0, 0, 0, 0], ![-80, 4, 0, 0, 0]] ![![-5308, 6564, 1616, 2984, -6756], ![-31620, 38220, 9364, 17136, -38928]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R59RS2]  
      rfl
    g := ![![![544, -288, -195, 3235, -8649], ![15175, 1884, 0, 0, 0]], ![![344, -24, -35, -1043, 2763], ![-4168, -471, 0, 0, 0]]]
    h := ![![![1820917117, -2461303046, 59672228892, -5970611704, 524913], ![5371521207, 1814808290, 176124319528, -245806, 0]], ![![11380493690, -15382821483, 372943608423, -37315540489, 3280638], ![33571304594, 11342313735, 1100753909728, -1536249, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![-1327, 1641, 404, 746, -1689]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E59RS2
                    

def R61RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![17261, 8995, 5018, 6494, -16893] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![69044, 35980, 20072, 25976, -67572], ![-5652, 1644, 3068, 5320, -15096]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E61RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I61N1) (Ideal.span {B.equivFun.symm ![17261, 8995, 5018, 6494, -16893]} * (J0 ^ 1*J1^ 1)) 
      ![![244, 0, 0, 0, 0], ![-72, 4, 0, 0, 0]] ![![69044, 35980, 20072, 25976, -67572], ![-5652, 1644, 3068, 5320, -15096]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R61RS1]  
      rfl
    g := ![![![-61336, 61571, 16623, 37622, -71538], ![73217, -13636, 0, 0, 0]], ![![15342, -15295, -4227, -9530, 18048], ![-18574, 3409, 0, 0, 0]]]
    h := ![![![-823551744946, 299749713702, -5440304155392, 604809851717, -56017863], ![-2790902759144, -164101858507, -18445764847059, 27119625, 0]], ![![-7442931519, 2709014639, -49167219267, 5466021364, -506334], ![-25223063597, -1483084612, -166705194987, 245100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {4} * I61N1 =  Ideal.span {B.equivFun.symm ![17261, 8995, 5018, 6494, -16893]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E61RS1
                    

def R61RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-536, 773, 245, 410, -929] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-1072, 1546, 490, 820, -1858], ![-36, 780, 486, 704, -1574]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E61RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I61N2) (Ideal.span {B.equivFun.symm ![-536, 773, 245, 410, -929]} * (J0 ^ 0*J1^ 1)) 
      ![![122, 0, 0, 0, 0], ![-16, 2, 0, 0, 0]] ![![-1072, 1546, 490, 820, -1858], ![-36, 780, 486, 704, -1574]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R61RS2]  
      rfl
    g := ![![![-51530, 34039, 13432, 3074, -1902], ![91693, 0, 0, 0, 0]], ![![3535, -2828, -1018, -94, -312], ![-7391, 0, 0, 0, 0]]]
    h := ![![![14808754, -35591943, 281666442, -70191528, -478241], ![113350920, 9213349, 2147671708, 231522, 0]], ![![13526928, -32507530, 257255498, -64108298, -436795], ![103539312, 8414851, 1961541276, 211458, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![-536, 773, 245, 410, -929]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E61RS2
                    

def R67RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![506, -616, -152, -278, 631] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![1012, -1232, -304, -556, 1262], ![476, -576, -142, -260, 590]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E67RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I67N1) (Ideal.span {B.equivFun.symm ![506, -616, -152, -278, 631]} * (J0 ^ 0*J1^ 1)) 
      ![![134, 0, 0, 0, 0], ![-34, 2, 0, 0, 0]] ![![1012, -1232, -304, -556, 1262], ![476, -576, -142, -260, 590]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R67RS1]  
      rfl
    g := ![![![-56, 4, 15, 14, -30], ![35, 0, 0, 0, 0]], ![![21, 2, -2, -1, 1], ![-6, 0, 0, 0, 0]]]
    h := ![![![547115896, -1032748231, 19337600093, -2276187526, 386269], ![2156099038, 542449663, 76245298654, -205392, 0]], ![![254131111, -479703543, 8982165229, -1057271448, 179419], ![1001491362, 251963660, 35415349741, -95403, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![506, -616, -152, -278, 631]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E67RS1
                    

def R71RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![40, -11, 2, 0, -4] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![80, -22, 4, 0, -8], ![214, -316, -90, -158, 370]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E71RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I71N1) (Ideal.span {B.equivFun.symm ![40, -11, 2, 0, -4]} * (J0 ^ 1*J1^ 0)) 
      ![![142, 0, 0, 0, 0], ![30, 2, 0, 0, 0]] ![![80, -22, 4, 0, -8], ![214, -316, -90, -158, 370]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R71RS1]  
      rfl
    g := ![![![186, -162, -7, 7, 25], ![-27, 0, 0, 0, 0]], ![![64, -34, -6, -1, 11], ![-1, 0, 0, 0, 0]]]
    h := ![![![-47788450, -22194219, -314889546, -41887224, -468374], ![225934741, -8227837, 1491747102, 263925, 0]], ![![27692632, 12860629, 182464547, 24271783, 271435], ![-130925501, 4767708, -864401436, -152950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![40, -11, 2, 0, -4]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E71RS1
                    

def R71RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![10, 7, 5, 6, -15] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![20, 14, 10, 12, -30], ![-64, -28, -10, -16, 46]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E71RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I71N2) (Ideal.span {B.equivFun.symm ![10, 7, 5, 6, -15]} * (J0 ^ 0*J1^ 1)) 
      ![![142, 0, 0, 0, 0], ![46, 2, 0, 0, 0]] ![![20, 14, 10, 12, -30], ![-64, -28, -10, -16, 46]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R71RS2]  
      rfl
    g := ![![![1306, -728, -78, -247, 487], ![91, 0, 0, 0, 0]], ![![341, -189, -20, -64, 126], ![24, 0, 0, 0, 0]]]
    h := ![![![-3282795, -531207, -11034772, -959312, -2955], ![10132760, -277365, 34078889, 1665, 0]], ![![5034569, 814682, 16924040, 1471298, 4531], ![-15539832, 425457, -52266825, -2553, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![10, 7, 5, 6, -15]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E71RS2
                    

def R73RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![101297, -123428, -30470, -55717, 126482] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![202594, -246856, -60940, -111434, 252964], ![1259220, -1534334, -378774, -692620, 1572302]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E73RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I73N1) (Ideal.span {B.equivFun.symm ![101297, -123428, -30470, -55717, 126482]} * (J0 ^ 1*J1^ 0)) 
      ![![146, 0, 0, 0, 0], ![8, 2, 0, 0, 0]] ![![202594, -246856, -60940, -111434, 252964], ![1259220, -1534334, -378774, -692620, 1572302]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R73RS1]  
      rfl
    g := ![![![3072, 70, -263, -624, 1739], ![-575, 0, 0, 0, 0]], ![![263, 26, -22, -55, 162], ![-22, 0, 0, 0, 0]]]
    h := ![![![2114544516480, 3220110238848, 10828128041000, 5415920411988, 785529824], ![-38588730747142, 295153938097, -197691790092728, -455107545, 0]], ![![13143026098380, 20014708878923, 67302612137211, 33662844535440, 4882488355], ![-239849618374230, 1834539722812, -1228760301036544, -2828737014, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![101297, -123428, -30470, -55717, 126482]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E73RS1
                    

def R79RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![336, -494, -143, -256, 574] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![672, -988, -286, -512, 1148], ![4870, -6054, -1392, -2702, 6078]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E79RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I79N2) (Ideal.span {B.equivFun.symm ![336, -494, -143, -256, 574]} * (J0 ^ 1*J1^ 0)) 
      ![![158, 0, 0, 0, 0], ![-50, 2, 0, 0, 0]] ![![672, -988, -286, -512, 1148], ![4870, -6054, -1392, -2702, 6078]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R79RS2]  
      rfl
    g := ![![![63642, -40163, -4906, -7371, 1707], ![-71551, 0, 0, 0, 0]], ![![-17422, 11230, 1344, 1993, -293], ![19919, 0, 0, 0, 0]]]
    h := ![![![-2663808726, 701228254, -18127813403, 1451858874, -1926638], ![-8416910802, -416278365, -57302522563, 1207976, 0]], ![![-25637821960, 6748968917, -174471076517, 13973410635, -18542919], ![-81008541807, -4006470063, -551507927438, 11626140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {2} * I79N2 =  Ideal.span {B.equivFun.symm ![336, -494, -143, -256, 574]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E79RS2
                    

def R83RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![120, -152, -38, -69, 157] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![480, -608, -152, -276, 628], ![2832, -3460, -856, -1564, 3552]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E83RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I83N1) (Ideal.span {B.equivFun.symm ![120, -152, -38, -69, 157]} * (J0 ^ 1*J1^ 1)) 
      ![![332, 0, 0, 0, 0], ![-16, 4, 0, 0, 0]] ![![480, -608, -152, -276, 628], ![2832, -3460, -856, -1564, 3552]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R83RS1]  
      rfl
    g := ![![![481984, -468456, -129695, -274896, 534287], ![-514969, 96798, 0, 0, 0]], ![![-23114, 22461, 6219, 13181, -25618], ![24694, -4641, 0, 0, 0]]]
    h := ![![![95879373, -1133996697, 4462055278, -2231047332, -1046671], ![1992082491, 107379587, 92607424806, 689475, 0]], ![![598066961, -7073533842, 27832972638, -13916609158, -6528822], ![12426017035, 669801867, 577657550184, 4300739, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {4} * I83N1 =  Ideal.span {B.equivFun.symm ![120, -152, -38, -69, 157]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E83RS1
                    

def R109RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-1121, -519, -258, -313, 795] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-2242, -1038, -516, -626, 1590], ![13748, 7362, 4204, 5508, -14390]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E109RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I109N1) (Ideal.span {B.equivFun.symm ![-1121, -519, -258, -313, 795]} * (J0 ^ 0*J1^ 1)) 
      ![![218, 0, 0, 0, 0], ![64, 2, 0, 0, 0]] ![![-2242, -1038, -516, -626, 1590], ![13748, 7362, 4204, 5508, -14390]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R109RS1]  
      rfl
    g := ![![![-41805277, 23655621, 2608748, 8061614, -15954541], ![-2844259, 0, 0, 0, 0]], ![![-10545400, 5967147, 658060, 2033549, -4024548], ![-717465, 0, 0, 0, 0]]]
    h := ![![![66938248144, 3837271101, 66260806176, 4141641754, 2238321], ![-228007500126, 1104602439, -225737870780, -1936319, 0]], ![![-439525178315, -25196017228, -435076991763, -27194553445, -14697121], ![1497126679107, -7252961172, 1482223948260, 12714119, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {2} * I109N1 =  Ideal.span {B.equivFun.symm ![-1121, -519, -258, -313, 795]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E109RS1
                    

def R109RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-85232, -45059, -25439, -33111, 86309] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-340928, -180236, -101756, -132444, 345236], ![87120, 25392, 4780, 300, 4704]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E109RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I109N2) (Ideal.span {B.equivFun.symm ![-85232, -45059, -25439, -33111, 86309]} * (J0 ^ 1*J1^ 1)) 
      ![![436, 0, 0, 0, 0], ![200, 4, 0, 0, 0]] ![![-340928, -180236, -101756, -132444, 345236], ![87120, 25392, 4780, 300, 4704]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R109RS2]  
      rfl
    g := ![![![-177285, 48260, -61957, -106717, 168710], ![-579193, 135876, 0, 0, 0]], ![![-39798, -13099, -35062, -64050, 108331], ![-278296, 63583, 0, 0, 0]]]
    h := ![![![-3321998791188, -381543444132, -24167502282267, -966806061369, 6183928385], ![7243562239532, -374361071582, 52688255533977, -5349588156, 0]], ![![691985957860, 79477052611, 5034188965433, 201389632557, -1288136640], ![-1508863689830, 77980931924, -10975177804101, 1114340436, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {4} * I109N2 =  Ideal.span {B.equivFun.symm ![-85232, -45059, -25439, -33111, 86309]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E109RS2
                    

def R113RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-75, 95, 73, 73, -182] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-150, 190, 146, 146, -364], ![316, 8, 140, 180, -390]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E113RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I113N1) (Ideal.span {B.equivFun.symm ![-75, 95, 73, 73, -182]} * (J0 ^ 1*J1^ 0)) 
      ![![226, 0, 0, 0, 0], ![86, 2, 0, 0, 0]] ![![-150, 190, 146, 146, -364], ![316, 8, 140, 180, -390]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R113RS1]  
      rfl
    g := ![![![2312, -1195, -120, -374, 715], ![53, 0, 0, 0, 0]], ![![796, -414, -42, -129, 245], ![7, 0, 0, 0, 0]]]
    h := ![![![-27993298078, -1052903832, -23075982849, -1073429663, -361606], ![73563670193, -353788594, 60650073180, 324296, 0]], ![![-91912035292, -3457060892, -75766736400, -3524454966, -1187283], ![241535907358, -1161615266, 199135964760, 1064784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {2} * I113N1 =  Ideal.span {B.equivFun.symm ![-75, 95, 73, 73, -182]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E113RS1
                    

def R131RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-60, -26, -12, -14, 35] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-120, -52, -24, -28, 70], ![896, 476, 270, 352, -918]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E131RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I131N0) (Ideal.span {B.equivFun.symm ![-60, -26, -12, -14, 35]} * (J0 ^ 0*J1^ 1)) 
      ![![262, 0, 0, 0, 0], ![2, 2, 0, 0, 0]] ![![-120, -52, -24, -28, 70], ![896, 476, 270, 352, -918]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R131RS0]  
      rfl
    g := ![![![218, -102, -9, -40, 70], ![21, 0, 0, 0, 0]], ![![-5, 6, 2, 3, -7], ![0, 0, 0, 0, 0]]]
    h := ![![![-5370, -1752558, -1755062, -3516258, -22547], ![351780, -26710, 230900942, 23442, 0]], ![![40084, 13085303, 13104010, 26253822, 168345], ![-2625121, 199614, -1724000978, -175029, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {2} * I131N0 =  Ideal.span {B.equivFun.symm ![-60, -26, -12, -14, 35]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E131RS0
                    

def R131RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-50, -21, -14, -18, 48] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-100, -42, -28, -36, 96], ![134, 168, 82, 118, -302]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E131RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I131N1) (Ideal.span {B.equivFun.symm ![-50, -21, -14, -18, 48]} * (J0 ^ 1*J1^ 0)) 
      ![![262, 0, 0, 0, 0], ![92, 2, 0, 0, 0]] ![![-100, -42, -28, -36, 96], ![134, 168, 82, 118, -302]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R131RS1]  
      rfl
    g := ![![![-116, -54, 59, 51, -101], ![-53, 0, 0, 0, 0]], ![![-29, -24, 18, 16, -30], ![-18, 0, 0, 0, 0]]]
    h := ![![![393233023626, 14756519693, 365736409044, 15903210442, 791088], ![-1119858994736, 4964340902, -1041662340160, -822480, 0]], ![![-1431517101405, -53719319145, -1331419007366, -57893707427, -2879861], ![4076710768957, -18072080281, 3792045321848, 2994140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![-50, -21, -14, -18, 48]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E131RS1
                    

def R131RS4 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![5135, 3048, 1875, 2536, -6699] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![20540, 12192, 7500, 10144, -26796], ![-35916, -18880, -10608, -13776, 35880]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E131RS4 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I131N4) (Ideal.span {B.equivFun.symm ![5135, 3048, 1875, 2536, -6699]} * (J0 ^ 1*J1^ 1)) 
      ![![524, 0, 0, 0, 0], ![-112, 4, 0, 0, 0]] ![![20540, 12192, 7500, 10144, -26796], ![-35916, -18880, -10608, -13776, 35880]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R131RS4]  
      rfl
    g := ![![![727777, -707750, -196011, -416188, 808218], ![-780625, 146580, 0, 0, 0]], ![![-150848, 146640, 40640, 86254, -167502], ![161760, -30363, 0, 0, 0]]]
    h := ![![![-25630107979, 1356295387, -13282626455, 950470946, -2495913], ![-119910900958, -163257092, -62153346987, 2594904, 0]], ![![41280739593, -2184474262, 21392717402, -1530808950, 4020690], ![193132649754, 262928780, 100102867788, -4180170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N4 : Ideal.span {4} * I131N4 =  Ideal.span {B.equivFun.symm ![5135, 3048, 1875, 2536, -6699]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E131RS4
                    

def R137RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-176, -62, -17, -10, 16] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-352, -124, -34, -20, 32], ![3234, 1566, 816, 1026, -2642]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E137RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I137N1) (Ideal.span {B.equivFun.symm ![-176, -62, -17, -10, 16]} * (J0 ^ 1*J1^ 0)) 
      ![![274, 0, 0, 0, 0], ![34, 2, 0, 0, 0]] ![![-352, -124, -34, -20, 32], ![3234, 1566, 816, 1026, -2642]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R137RS1]  
      rfl
    g := ![![![-14593356, 7418129, 747932, 2427427, -4854451], ![-1426571, 0, 0, 0, 0]], ![![-1331005, 676588, 68219, 221401, -442767], ![-130111, 0, 0, 0, 0]]]
    h := ![![![261226210750, 46676653220, 548868394659, 64579068712, 1959668], ![-2105174053628, 7883872909, -4423702429527, -2130750, 0]], ![![-2770763219787, -495087967735, -5821714262186, -684974556771, -20785733], ![22329071888658, -83622331100, 46921141345020, 22600350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![-176, -62, -17, -10, 16]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E137RS1
                    

def R139RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-2139, 2544, 622, 1143, -2590] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-4278, 5088, 1244, 2286, -5180], ![-25948, 31970, 7930, 14468, -32874]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E139RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I139N1) (Ideal.span {B.equivFun.symm ![-2139, 2544, 622, 1143, -2590]} * (J0 ^ 1*J1^ 0)) 
      ![![278, 0, 0, 0, 0], ![-28, 2, 0, 0, 0]] ![![-4278, 5088, 1244, 2286, -5180], ![-25948, 31970, 7930, 14468, -32874]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R139RS1]  
      rfl
    g := ![![![6319, -2612, -1186, -724, 2267], ![297, 0, 0, 0, 0]], ![![-593, 314, 96, 53, -196], ![0, 0, 0, 0, 0]]]
    h := ![![![-33444433849, 165736918511, -2333419562054, 333385595979, -10284610], ![-332043294098, -33238286238, -23169930184719, 11345700, 0]], ![![-218033171355, 1080483116807, -15212183647394, 2173429499737, -67048113], ![-2164678665764, -216689241812, -151050946344642, 73965645, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![-2139, 2544, 622, 1143, -2590]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E139RS1
                    

def R149RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![826, -396, -88, -24, 155] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![1652, -792, -176, -48, 310], ![4912, -2584, -774, -416, 1570]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E149RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I149N1) (Ideal.span {B.equivFun.symm ![826, -396, -88, -24, 155]} * (J0 ^ 0*J1^ 1)) 
      ![![298, 0, 0, 0, 0], ![80, 2, 0, 0, 0]] ![![1652, -792, -176, -48, 310], ![4912, -2584, -774, -416, 1570]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R149RS1]  
      rfl
    g := ![![![4208, -3844, -1315, -10, -766], ![-9881, 0, 0, 0, 0]], ![![1255, -1108, -383, -9, -203], ![-2863, 0, 0, 0, 0]]]
    h := ![![![-388970876, -24324376, -689905597, -34371142, -1777037], ![1448128502, -6222637, 2572207866, 2101418, 0]], ![![139805199, 8740726, 247874022, 12349087, 638635], ![-520491103, 2235450, -924160713, -755205, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![826, -396, -88, -24, 155]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E149RS1
                    

def R149RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-3136, -769, -2157, -2622, 5849] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-6272, -1538, -4314, -5244, 11698], ![-21492, -1856, -11038, -13892, 30410]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E149RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I149N2) (Ideal.span {B.equivFun.symm ![-3136, -769, -2157, -2622, 5849]} * (J0 ^ 0*J1^ 1)) 
      ![![298, 0, 0, 0, 0], ![-58, 2, 0, 0, 0]] ![![-6272, -1538, -4314, -5244, 11698], ![-21492, -1856, -11038, -13892, 30410]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R149RS2]  
      rfl
    g := ![![![217538, -45723, -36872, -34776, 91826], ![-170007, 0, 0, 0, 0]], ![![-37957, 8215, 6482, 6016, -15822], ![30188, 0, 0, 0, 0]]]
    h := ![![![-4205269980454, 1636703118779, -46663994758875, 3218406741066, 120449653], ![-21606460814870, -603611214942, -239776999668648, -142436448, 0]], ![![-10721797026208, 4172954097149, -118974972212582, 8205680944498, 307099601], ![-55088041526014, -1538972989591, -611337756662334, -363157344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N2 : Ideal.span {2} * I149N2 =  Ideal.span {B.equivFun.symm ![-3136, -769, -2157, -2622, 5849]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E149RS2
                    

def R151RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![2423, -2953, -729, -1333, 3026] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![4846, -5906, -1458, -2666, 6052], ![30132, -36704, -9060, -16568, 37610]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E151RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I151N1) (Ideal.span {B.equivFun.symm ![2423, -2953, -729, -1333, 3026]} * (J0 ^ 1*J1^ 0)) 
      ![![302, 0, 0, 0, 0], ![132, 2, 0, 0, 0]] ![![4846, -5906, -1458, -2666, 6052], ![30132, -36704, -9060, -16568, 37610]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R151RS1]  
      rfl
    g := ![![![-252, -3, 74, 66, -145], ![-23, 0, 0, 0, 0]], ![![-97, -1, 33, 31, -68], ![-8, 0, 0, 0, 0]]]
    h := ![![![-4423648666783, -99774868667, -3180859601762, -96397113511, -2608714], ![10120771239266, -35340997751, 7277958621864, 3126340, 0]], ![![-27813549051966, -627331285010, -19999552678621, -606093758008, -16402205], ![63634024424402, -222205389891, 45759931299762, 19656760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {2} * I151N1 =  Ideal.span {B.equivFun.symm ![2423, -2953, -729, -1333, 3026]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E151RS1
                    

def R151RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-1386, -792, -477, -638, 1678] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-2772, -1584, -954, -1276, 3356], ![4342, 2786, 1784, 2450, -6510]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E151RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I151N2) (Ideal.span {B.equivFun.symm ![-1386, -792, -477, -638, 1678]} * (J0 ^ 1*J1^ 0)) 
      ![![302, 0, 0, 0, 0], ![-62, 2, 0, 0, 0]] ![![-2772, -1584, -954, -1276, 3356], ![4342, 2786, 1784, 2450, -6510]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R151RS2]  
      rfl
    g := ![![![-63805184, 32433573, 3270106, 10613201, -21224635], ![-6237269, 0, 0, 0, 0]], ![![15002543, -7626114, -768899, -2495483, 4990549], ![1466573, 0, 0, 0, 0]]]
    h := ![![![-2143049447916, 696967029700, -21175185179449, 1366220135404, 53368738], ![-10438755677430, -269177407749, -103152242491481, -63957760, 0]], ![![3543603111588, -1152458025824, 35013868762374, -2259090162193, -88246977], ![17260827619087, 445093742986, 170565643253336, 105756272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {2} * I151N2 =  Ideal.span {B.equivFun.symm ![-1386, -792, -477, -638, 1678]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E151RS2
                    

def R157RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-249, -153, -96, -131, 347] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-498, -306, -192, -262, 694], ![-880, -346, -140, -148, 354]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E157RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I157N1) (Ideal.span {B.equivFun.symm ![-249, -153, -96, -131, 347]} * (J0 ^ 0*J1^ 1)) 
      ![![314, 0, 0, 0, 0], ![12, 2, 0, 0, 0]] ![![-498, -306, -192, -262, 694], ![-880, -346, -140, -148, 354]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R157RS1]  
      rfl
    g := ![![![-151, -158, 102, 105, -170], ![-85, 0, 0, 0, 0]], ![![22, -12, 0, 2, -1], ![-1, 0, 0, 0, 0]]]
    h := ![![![12957583425, 17324271655, 91249600720, 30418750687, 983555], ![-339053702484, 1159461406, -2387899503600, -1225538, 0]], ![![13199480302, 17647690239, 92953098189, 30986624568, 1001913], ![-345383280274, 1181106923, -2432478117940, -1248414, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {2} * I157N1 =  Ideal.span {B.equivFun.symm ![-249, -153, -96, -131, 347]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E157RS1
                    

def R163RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![54, 20, 13, 18, -46] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![108, 40, 26, 36, -92], ![-214, -154, -96, -122, 318]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E163RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I163N1) (Ideal.span {B.equivFun.symm ![54, 20, 13, 18, -46]} * (J0 ^ 1*J1^ 0)) 
      ![![326, 0, 0, 0, 0], ![-96, 2, 0, 0, 0]] ![![108, 40, 26, 36, -92], ![-214, -154, -96, -122, 318]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R163RS1]  
      rfl
    g := ![![![83782, -42581, -4292, -13933, 27863], ![8193, 0, 0, 0, 0]], ![![-26984, 13719, 1384, 4490, -8980], ![-2638, 0, 0, 0, 0]]]
    h := ![![![-1488531294, 477904579, -25509741665, 1063244340, -331354], ![-5054670232, -287904688, -86633195229, 428656, 0]], ![![3767212336, -1209492718, 64560689771, -2690885266, 838599], ![12792486210, 728636706, 219253448925, -1084853, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![54, 20, 13, 18, -46]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E163RS1
                    

def R167RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-31, -1, -14, -18, 39] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-124, -4, -56, -72, 156], ![60, 220, 268, 296, -696]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E167RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I167N1) (Ideal.span {B.equivFun.symm ![-31, -1, -14, -18, 39]} * (J0 ^ 1*J1^ 1)) 
      ![![668, 0, 0, 0, 0], ![-112, 4, 0, 0, 0]] ![![-124, -4, -56, -72, 156], ![60, 220, 268, 296, -696]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R167RS1]  
      rfl
    g := ![![![226510, -219274, -60843, -128817, 250533], ![-240497, 45390, 0, 0, 0]], ![![-33314, 32243, 8947, 18942, -36840], ![35360, -6675, 0, 0, 0]]]
    h := ![![![2463074575, -7214536229, 211069496507, -15077550078, 162753], ![14690364942, 2458743765, 1258966910880, -215712, 0]], ![![-5504375911, 16122743519, -471689273211, 33694677610, -363714], ![-32829412364, -5494697432, -2813486538870, 482064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {4} * I167N1 =  Ideal.span {B.equivFun.symm ![-31, -1, -14, -18, 39]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E167RS1
                    

def R173RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![5581, -6795, -1677, -3067, 6962] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![11162, -13590, -3354, -6134, 13924], ![69316, -84500, -20864, -38148, 86602]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E173RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I173N1) (Ideal.span {B.equivFun.symm ![5581, -6795, -1677, -3067, 6962]} * (J0 ^ 1*J1^ 0)) 
      ![![346, 0, 0, 0, 0], ![134, 2, 0, 0, 0]] ![![11162, -13590, -3354, -6134, 13924], ![69316, -84500, -20864, -38148, 86602]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R173RS1]  
      rfl
    g := ![![![1363, -379, -303, -206, 561], ![143, 0, 0, 0, 0]], ![![520, -134, -118, -81, 217], ![59, 0, 0, 0, 0]]]
    h := ![![![-2792719387022, -299821078673, -23397361812008, -698450152347, 140304904], ![7211094680186, -235418093072, 60417479302922, -192640805, 0]], ![![-17381168305208, -1866009400561, -145619171551299, -4346974388474, 873221689], ![44880001508046, -1465181756785, 376022876168632, -1198946896, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {2} * I173N1 =  Ideal.span {B.equivFun.symm ![5581, -6795, -1677, -3067, 6962]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E173RS1
                    

def R179RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![6021, -2622, -353, 140, 383] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![24084, -10488, -1412, 560, 1532], ![-46116, 2568, -16552, -22016, 46776]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E179RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I179N2) (Ideal.span {B.equivFun.symm ![6021, -2622, -353, 140, 383]} * (J0 ^ 1*J1^ 1)) 
      ![![716, 0, 0, 0, 0], ![40, 4, 0, 0, 0]] ![![24084, -10488, -1412, 560, 1532], ![-46116, 2568, -16552, -22016, 46776]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R179RS2]  
      rfl
    g := ![![![-2156317, 1452709, 503979, 927221, -1889483], ![1041713, -386370, 0, 0, 0]], ![![-138305, 88050, 31713, 57218, -117616], ![57464, -24327, 0, 0, 0]]]
    h := ![![![-7940740081, -68116955373, -677500307193, -135503660530, -18553091], ![142099712294, -7543764064, 12128117939531, 26357172, 0]], ![![43396859019, 372265022336, 3702597447357, 740539158670, 101394798], ![-776587710246, 41227319401, -66281207624126, -144044898, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {4} * I179N2 =  Ideal.span {B.equivFun.symm ![6021, -2622, -353, 140, 383]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E179RS2
                    

def R181RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![549, -664, -163, -298, 677] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![2196, -2656, -652, -1192, 2708], ![12468, -15240, -3784, -6904, 15672]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E181RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I181N1) (Ideal.span {B.equivFun.symm ![549, -664, -163, -298, 677]} * (J0 ^ 1*J1^ 1)) 
      ![![724, 0, 0, 0, 0], ![208, 4, 0, 0, 0]] ![![2196, -2656, -652, -1192, 2708], ![12468, -15240, -3784, -6904, 15672]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R181RS1]  
      rfl
    g := ![![![-895421, 862861, 240067, 506859, -985951], ![940691, -179428, 0, 0, 0]], ![![-267200, 257436, 71632, 151228, -294178], ![280616, -53539, 0, 0, 0]]]
    h := ![![![93267473608783, 2606848788251, 49884695309963, 1918750812908, 29940437], ![-324642539962387, 508592801440, -173646927063488, -43009670, 0]], ![![542343806978331, 15158642572229, 290075998823341, 11157401184652, 174101538], ![-1887773563684647, 2957431411451, -1009744682162764, -250098210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {4} * I181N1 =  Ideal.span {B.equivFun.symm ![549, -664, -163, -298, 677]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E181RS1
                    

def R181RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![9432, 4570, 2388, 2989, -7681] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![37728, 18280, 9552, 11956, -30724], ![28608, 18812, 12336, 17116, -45600]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E181RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I181N2) (Ideal.span {B.equivFun.symm ![9432, 4570, 2388, 2989, -7681]} * (J0 ^ 1*J1^ 1)) 
      ![![724, 0, 0, 0, 0], ![-88, 4, 0, 0, 0]] ![![37728, 18280, 9552, 11956, -30724], ![28608, 18812, 12336, 17116, -45600]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R181RS2]  
      rfl
    g := ![![![-2440826, 2362079, 659135, 1388973, -2701114], ![2595527, -486192, 0, 0, 0]], ![![283859, -274526, -76656, -161332, 313861], ![-301250, 56433, 0, 0, 0]]]
    h := ![![![22947887476406, -2295416960676, 28405977197714, -2582038524245, -791621689], ![188799304126442, 316601157460, 233715993179064, 1137170778, 0]], ![![21167884766248, -2117367972125, 26202606165999, -2381757124017, -730217904], ![174154676233618, 292043305237, 215587306901604, 1048963724, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N2 : Ideal.span {4} * I181N2 =  Ideal.span {B.equivFun.symm ![9432, 4570, 2388, 2989, -7681]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E181RS2
                    

def R191RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![10, -10, -2, -4, 9] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![20, -20, -4, -8, 18], ![8, -12, -2, -4, 10]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E191RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I191N2) (Ideal.span {B.equivFun.symm ![10, -10, -2, -4, 9]} * (J0 ^ 0*J1^ 1)) 
      ![![382, 0, 0, 0, 0], ![146, 2, 0, 0, 0]] ![![20, -20, -4, -8, 18], ![8, -12, -2, -4, 10]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R191RS2]  
      rfl
    g := ![![![20, 44, 7, -10, 36], ![81, 0, 0, 0, 0]], ![![15, 23, 6, 0, 4], ![34, 0, 0, 0, 0]]]
    h := ![![![302346983384, 6680437855, 248647464269, 6812611672, 146007], ![-791072198718, 2269795281, -650601980070, -221328, 0]], ![![289036184002, 6386332117, 237700781730, 6512687048, 139579], ![-756245314666, 2169867878, -621959285661, -211584, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {2} * I191N2 =  Ideal.span {B.equivFun.symm ![10, -10, -2, -4, 9]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E191RS2
                    

def R197RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-545, -25, -445, -437, 1026] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-1090, -50, -890, -874, 2052], ![-8164, 6856, 1740, 2368, -5918]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E197RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I197N2) (Ideal.span {B.equivFun.symm ![-545, -25, -445, -437, 1026]} * (J0 ^ 1*J1^ 0)) 
      ![![394, 0, 0, 0, 0], ![148, 2, 0, 0, 0]] ![![-1090, -50, -890, -874, 2052], ![-8164, 6856, 1740, 2368, -5918]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R197RS2]  
      rfl
    g := ![![![1079696, -595153, -84402, -136726, 100641], ![-1090185, 0, 0, 0, 0]], ![![423258, -232099, -33100, -53757, 40442], ![-425638, 0, 0, 0, 0]]]
    h := ![![![132322645, 26980415, 2511460099, 68065113, 965934], ![-351958220, 21866854, -6687046296, -1510222, 0]], ![![304836194, 62155374, 5785697983, 156802924, 2225365], ![-810818160, 50374759, -15405074736, -3479364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {2} * I197N2 =  Ideal.span {B.equivFun.symm ![-545, -25, -445, -437, 1026]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E197RS2
                    

def R197RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![314695, -383449, -94660, -173094, 392937] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![1258780, -1533796, -378640, -692376, 1571748], ![7234332, -8814892, -2176092, -3979168, 9033024]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E197RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I197N3) (Ideal.span {B.equivFun.symm ![314695, -383449, -94660, -173094, 392937]} * (J0 ^ 1*J1^ 1)) 
      ![![788, 0, 0, 0, 0], ![-40, 4, 0, 0, 0]] ![![1258780, -1533796, -378640, -692376, 1571748], ![7234332, -8814892, -2176092, -3979168, 9033024]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R197RS3]  
      rfl
    g := ![![![-903079, 899958, 245624, 525971, -1019631], ![1010607, -182700, 0, 0, 0]], ![![38990, -38682, -10585, -22629, 43893], ![-43294, 7875, 0, 0, 0]]]
    h := ![![![-3689601864305, 2264828448686, -19086530731385, 3815398772472, 3861400017], ![-72694212656021, -210131508257, -376000915762480, -6037265162, 0]], ![![-21204561260816, 13016226506537, -109692461417192, 21927530389397, 22191904770], ![-417781902292522, -1207649661618, -2160919997749300, -34696849059, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N3 : Ideal.span {4} * I197N3 =  Ideal.span {B.equivFun.symm ![314695, -383449, -94660, -173094, 392937]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E197RS3
                    

def R239RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1864, -332, 442, 631, -1283] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![7456, -1328, 1768, 2524, -5132], ![-6504, -8812, -11808, -13716, 31608]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E239RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I239N2) (Ideal.span {B.equivFun.symm ![1864, -332, 442, 631, -1283]} * (J0 ^ 1*J1^ 1)) 
      ![![956, 0, 0, 0, 0], ![148, 4, 0, 0, 0]] ![![7456, -1328, 1768, 2524, -5132], ![-6504, -8812, -11808, -13716, 31608]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R239RS2]  
      rfl
    g := ![![![-2700446, 1780835, 625643, 1186093, -2449880], ![1420437, -458640, 0, 0, 0]], ![![-440686, 288605, 101852, 192939, -399091], ![229317, -74529, 0, 0, 0]]]
    h := ![![![-23408914044540, -6292922747813, -219709055848147, -11876552271507, -202471453], ![151208775563572, -1795244322811, 1419250684816290, 384052984, 0]], ![![42615890882058, 11456255874629, 399979987445322, 21621244559589, 368598978], ![-275275336035024, 3268239440410, -2583743619047480, -699167840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {4} * I239N2 =  Ideal.span {B.equivFun.symm ![1864, -332, 442, 631, -1283]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E239RS2
                    

def R241RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![3632, -4544, -3458, -3451, 8619] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![14528, -18176, -13832, -13804, 34476], ![-65328, 50196, 27640, 24428, -65712]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E241RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I241N2) (Ideal.span {B.equivFun.symm ![3632, -4544, -3458, -3451, 8619]} * (J0 ^ 1*J1^ 1)) 
      ![![964, 0, 0, 0, 0], ![56, 4, 0, 0, 0]] ![![14528, -18176, -13832, -13804, 34476], ![-65328, 50196, 27640, 24428, -65712]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R241RS2]  
      rfl
    g := ![![![-1187218, 1096722, 312735, 648674, -1267479], ![1149463, -235094, 0, 0, 0]], ![![-87572, 81057, 23085, 47937, -93654], ![85172, -17343, 0, 0, 0]]]
    h := ![![![59053715386752, 14117104659746, 139519852386677, 19932054142309, 149045739], ![-1016567223715100, 1153060233465, -2401817798120340, -285079480, 0]], ![![73754178782612, 17631328748475, 174251055906380, 24893815620287, 186148212], ![-1269625124710216, 1440095874110, -2999711369083650, -356045520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N2 : Ideal.span {4} * I241N2 =  Ideal.span {B.equivFun.symm ![3632, -4544, -3458, -3451, 8619]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E241RS2
                    

def R251RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-94, -21, -15, -16, 43] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-188, -42, -30, -32, 86], ![884, 500, 282, 372, -970]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E251RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I251N1) (Ideal.span {B.equivFun.symm ![-94, -21, -15, -16, 43]} * (J0 ^ 0*J1^ 1)) 
      ![![502, 0, 0, 0, 0], ![186, 2, 0, 0, 0]] ![![-188, -42, -30, -32, 86], ![884, 500, 282, 372, -970]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R251RS1]  
      rfl
    g := ![![![-322, -594, 272, 299, -435], ![-269, 0, 0, 0, 0]], ![![-69, -236, 90, 103, -141], ![-96, 0, 0, 0, 0]]]
    h := ![![![-11022408074, -1411346906, -158489264276, -3408364832, 298577], ![29748745680, -1110801979, 427762276872, -594784, 0]], ![![62637441596, 8020312469, 900652753524, 19368839808, -1696735], ![-169054285378, 6312396040, -2430860375811, 3380000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {2} * I251N1 =  Ideal.span {B.equivFun.symm ![-94, -21, -15, -16, 43]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E251RS1
                    

def R251RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![901, 421, 212, 260, -663] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![3604, 1684, 848, 1040, -2652], ![4188, 2620, 1668, 2288, -6072]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E251RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I251N2) (Ideal.span {B.equivFun.symm ![901, 421, 212, 260, -663]} * (J0 ^ 1*J1^ 1)) 
      ![![1004, 0, 0, 0, 0], ![-32, 4, 0, 0, 0]] ![![3604, 1684, 848, 1040, -2652], ![4188, 2620, 1668, 2288, -6072]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R251RS2]  
      rfl
    g := ![![![-1055776, 1023701, 282007, 598122, -1163292], ![1113189, -208728, 0, 0, 0]], ![![30796, -29812, -8183, -17365, 33789], ![-32168, 6021, 0, 0, 0]]]
    h := ![![![6109399400, -7863068725, 56952596766, -14234274625, -7920579], ![191711990358, 480523093, 1786866925152, 15778291, 0]], ![![8296911511, -10678504221, 77344943648, -19330974022, -10756614], ![260355775738, 652578487, 2426669361504, 21427846, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N2 : Ideal.span {4} * I251N2 =  Ideal.span {B.equivFun.symm ![901, 421, 212, 260, -663]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E251RS2
                    

def R271RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-3878, -2070, -1178, -1539, 4017] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-15512, -8280, -4712, -6156, 16068], ![5808, 2204, 840, 844, -1968]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E271RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I271N2) (Ideal.span {B.equivFun.symm ![-3878, -2070, -1178, -1539, 4017]} * (J0 ^ 1*J1^ 1)) 
      ![![1084, 0, 0, 0, 0], ![-276, 4, 0, 0, 0]] ![![-15512, -8280, -4712, -6156, 16068], ![5808, 2204, 840, 844, -1968]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R271RS2]  
      rfl
    g := ![![![-1731665, 1680803, 466294, 986321, -1917738], ![1845827, -346720, 0, 0, 0]], ![![422175, -409753, -113681, -240431, 467499], ![-449911, 84513, 0, 0, 0]]]
    h := ![![![23290387686466, -3340908192414, 235910987999394, -6838786398637, 636258207], ![91473544001956, 1634154572104, 926573449409744, -1368460080, 0]], ![![-7669456867158, 1100151342969, -77684801653352, 2251992454581, -209517972], ![-30121971761630, -538122343658, -305117939800420, 450629920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N2 : Ideal.span {4} * I271N2 =  Ideal.span {B.equivFun.symm ![-3878, -2070, -1178, -1539, 4017]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E271RS2
                    

def R293RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![110, 526, 514, 803, -2217] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![440, 2104, 2056, 3212, -8868], ![-43152, -24396, -14504, -19324, 50784]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E293RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I293N1) (Ideal.span {B.equivFun.symm ![110, 526, 514, 803, -2217]} * (J0 ^ 1*J1^ 1)) 
      ![![1172, 0, 0, 0, 0], ![308, 4, 0, 0, 0]] ![![440, 2104, 2056, 3212, -8868], ![-43152, -24396, -14504, -19324, 50784]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R293RS1]  
      rfl
    g := ![![![-108163121, 89060464, 14906640, 34781386, -72610743], ![16045683, 482658, 0, 0, 0]], ![![-26715152, 21990013, 3675610, 8578939, -17913531], ![3919851, 128865, 0, 0, 0]]]
    h := ![![![-2800516270470, -173999866267, -12169411155039, -316096214561, -3380757], ![10656508432780, -77688188807, 46307993232996, 7861584, 0]], ![![56015451666730, 3480315844375, 243410500449822, 6322502937607, 67621080], ![-213149675060734, 1553905995037, -926244636167169, -157245744, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R293N1 : Ideal.span {4} * I293N1 =  Ideal.span {B.equivFun.symm ![110, 526, 514, 803, -2217]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E293RS1
                    

def R347RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![18022, 10292, 6164, 8242, -21687] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![36044, 20584, 12328, 16484, -43374], ![-13924, -14144, -11122, -16420, 44602]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E347RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I347N1) (Ideal.span {B.equivFun.symm ![18022, 10292, 6164, 8242, -21687]} * (J0 ^ 0*J1^ 1)) 
      ![![694, 0, 0, 0, 0], ![286, 2, 0, 0, 0]] ![![36044, 20584, 12328, 16484, -43374], ![-13924, -14144, -11122, -16420, 44602]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R347RS1]  
      rfl
    g := ![![![-1565698, 885881, 97737, 301949, -597573], ![-106545, 0, 0, 0, 0]], ![![-624899, 353575, 39010, 120516, -238508], ![-42524, 0, 0, 0, 0]]]
    h := ![![![-310737091919422, -3603760118968, -287802919793376, -4025484463030, -288424929], ![754026286582962, -1411545030288, 698385015945230, 794312926, 0]], ![![176506660646618, 2047028437754, 163479460500379, 2286578707198, 163832821], ![-428306325010701, 801793879311, -396700650953252, -451190211, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R347N1 : Ideal.span {2} * I347N1 =  Ideal.span {B.equivFun.symm ![18022, 10292, 6164, 8242, -21687]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E347RS1
                    

def R347RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![632, 279, 132, 156, -392] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![1264, 558, 264, 312, -784], ![-6718, -3416, -1866, -2390, 6194]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E347RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I347N2) (Ideal.span {B.equivFun.symm ![632, 279, 132, 156, -392]} * (J0 ^ 1*J1^ 0)) 
      ![![694, 0, 0, 0, 0], ![-216, 2, 0, 0, 0]] ![![1264, 558, 264, 312, -784], ![-6718, -3416, -1866, -2390, 6194]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R347RS2]  
      rfl
    g := ![![![-2152, 930, 199, 393, -801], ![-257, 0, 0, 0, 0]], ![![705, -300, -62, -124, 252], ![84, 0, 0, 0, 0]]]
    h := ![![![21000882286408, -376290733651, 23869230259108, -442001112864, -22386952], ![67475065538678, 125832960616, 76692094491666, 61652952, 0]], ![![-117100585889689, 2098191151279, -133094448640323, 2464591181887, 124829291], ![-376239893151453, -701642588748, -427633900240452, -343775880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R347N2 : Ideal.span {2} * I347N2 =  Ideal.span {B.equivFun.symm ![632, 279, 132, 156, -392]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E347RS2
                    

def R347RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![23, -18, -10, -9, 24] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![46, -36, -20, -18, 48], ![-8, -42, -46, -52, 122]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E347RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I347N3) (Ideal.span {B.equivFun.symm ![23, -18, -10, -9, 24]} * (J0 ^ 1*J1^ 0)) 
      ![![694, 0, 0, 0, 0], ![-122, 2, 0, 0, 0]] ![![46, -36, -20, -18, 48], ![-8, -42, -46, -52, 122]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R347RS3]  
      rfl
    g := ![![![603, 72, -50, -128, 385], ![-11, 0, 0, 0, 0]], ![![-97, -6, 11, 25, -73], ![5, 0, 0, 0, 0]]]
    h := ![![![21516138490, -925992419, 37218768030, -1220205641, -112974], ![122395159392, 209460868, 211723101821, 311127, 0]], ![![-64899003658, 2793065893, -112262765739, 3680499578, 340763], ![-369179808952, -631794796, -638619229996, -938450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R347N3 : Ideal.span {2} * I347N3 =  Ideal.span {B.equivFun.symm ![23, -18, -10, -9, 24]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E347RS3
                    

def R349RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![5, -4, 0, -1, 2] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![10, -8, 0, -2, 4], ![60, -74, -18, -32, 74]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E349RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I349N1) (Ideal.span {B.equivFun.symm ![5, -4, 0, -1, 2]} * (J0 ^ 1*J1^ 0)) 
      ![![698, 0, 0, 0, 0], ![192, 2, 0, 0, 0]] ![![10, -8, 0, -2, 4], ![60, -74, -18, -32, 74]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R349RS1]  
      rfl
    g := ![![![-81, 150, 8, 0, 65], ![223, 0, 0, 0, 0]], ![![-22, 44, 3, 1, 16], ![64, 0, 0, 0, 0]]]
    h := ![![![-47761015, -7992393, -837224374, -17441331, 3050], ![173632510, -4464386, 3043702339, -8448, 0]], ![![-1079009661, -180562084, -18914445307, -394031891, 68899], ![3922679524, -100861769, 68762858849, -190839, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R349N1 : Ideal.span {2} * I349N1 =  Ideal.span {B.equivFun.symm ![5, -4, 0, -1, 2]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E349RS1
                    

def R349RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-33, 4, 8, 7, -16] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-66, 8, 16, 14, -32], ![284, 90, 74, 100, -246]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E349RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I349N2) (Ideal.span {B.equivFun.symm ![-33, 4, 8, 7, -16]} * (J0 ^ 1*J1^ 0)) 
      ![![698, 0, 0, 0, 0], ![232, 2, 0, 0, 0]] ![![-66, 8, 16, 14, -32], ![284, 90, 74, 100, -246]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R349RS2]  
      rfl
    g := ![![![500443, -254388, -25648, -83242, 166469], ![48921, 0, 0, 0, 0]], ![![159881, -81266, -8192, -26591, 53176], ![15630, 0, 0, 0, 0]]]
    h := ![![![4242882217827, 61150211053, 3558187369454, 61349126383, 309752], ![-12765223113381, 18354604038, -10705394670000, -857964, 0]], ![![-89430735974306, -1288913549557, -74998856584039, -1293106251418, -6528903], ![269063160204936, -386875160944, 225646453141686, 18084024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R349N2 : Ideal.span {2} * I349N2 =  Ideal.span {B.equivFun.symm ![-33, 4, 8, 7, -16]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E349RS2
                    

def R359RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1285, 549, 252, 292, -727] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![5140, 2196, 1008, 1168, -2908], ![10332, 6220, 3844, 5216, -13800]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E359RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I359N1) (Ideal.span {B.equivFun.symm ![1285, 549, 252, 292, -727]} * (J0 ^ 1*J1^ 1)) 
      ![![1436, 0, 0, 0, 0], ![72, 4, 0, 0, 0]] ![![5140, 2196, 1008, 1168, -2908], ![10332, 6220, 3844, 5216, -13800]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R359RS1]  
      rfl
    g := ![![![-33933693, 28419923, 5100234, 11714552, -24190700], ![8002875, -511038, 0, 0, 0]], ![![-1308627, 1100425, 200606, 459190, -945948], ![336104, -25839, 0, 0, 0]]]
    h := ![![![772984273967, 7829763754429, 140864843576400, 15651943492652, -229980089], ![-15417287959096, 782834083292, -2809513045128942, 655260724, 0]], ![![1813210641885, 18366493911316, 330430568916681, 36715197785482, -539470662], ![-36164759799014, 1836315611840, -6590352640950435, 1537063208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R359N1 : Ideal.span {4} * I359N1 =  Ideal.span {B.equivFun.symm ![1285, 549, 252, 292, -727]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E359RS1
                    

def R359RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-889, 1559, 1336, 1378, -3375] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-3556, 6236, 5344, 5512, -13500], ![21660, -19636, -12444, -11672, 30264]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E359RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I359N2) (Ideal.span {B.equivFun.symm ![-889, 1559, 1336, 1378, -3375]} * (J0 ^ 1*J1^ 1)) 
      ![![1436, 0, 0, 0, 0], ![-264, 4, 0, 0, 0]] ![![-3556, 6236, 5344, 5512, -13500], ![21660, -19636, -12444, -11672, 30264]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R359RS2]  
      rfl
    g := ![![![425344, -429717, -116297, -250774, 485670], ![-488881, 86130, 0, 0, 0]], ![![-70884, 71744, 19393, 41857, -81051], ![81758, -14355, 0, 0, 0]]]
    h := ![![![8076300529210, -972226589241, 60014449934457, -1818640513589, -6907527], ![43930184624264, 323433105216, 326447123525080, 19680943, 0]], ![![-9425716179612, 1134669515518, -70041868536669, 2122505161791, 8061672], ![-51270188682208, -377473409125, -380991020247403, -22969307, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R359N2 : Ideal.span {4} * I359N2 =  Ideal.span {B.equivFun.symm ![-889, 1559, 1336, 1378, -3375]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E359RS2
                    

def R373RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![334, -388, -93, -172, 388] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![668, -776, -186, -344, 776], ![4050, -4902, -1212, -2218, 5038]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E373RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I373N1) (Ideal.span {B.equivFun.symm ![334, -388, -93, -172, 388]} * (J0 ^ 1*J1^ 0)) 
      ![![746, 0, 0, 0, 0], ![194, 2, 0, 0, 0]] ![![668, -776, -186, -344, 776], ![4050, -4902, -1212, -2218, 5038]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R373RS1]  
      rfl
    g := ![![![-3101, 747, 755, 531, -1371], ![-371, 0, 0, 0, 0]], ![![-790, 180, 196, 139, -355], ![-99, 0, 0, 0, 0]]]
    h := ![![![-244432599038, -37885769082, -3927726515419, -80976818658, 22393348], ![939941791884, -19761770165, 15103701382199, -66291416, 0]], ![![-1583620562557, -245452869352, -25446804105733, -524629511095, 145081163], ![6089658887938, -128031800668, 97853282003103, -429486280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R373N1 : Ideal.span {2} * I373N1 =  Ideal.span {B.equivFun.symm ![334, -388, -93, -172, 388]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E373RS1
                    

def R379RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-2933, -1408, -729, -908, 2329] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-11732, -5632, -2916, -3632, 9316], ![-10116, -6544, -4248, -5872, 15624]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E379RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I379N2) (Ideal.span {B.equivFun.symm ![-2933, -1408, -729, -908, 2329]} * (J0 ^ 1*J1^ 1)) 
      ![![1516, 0, 0, 0, 0], ![-572, 4, 0, 0, 0]] ![![-11732, -5632, -2916, -3632, 9316], ![-10116, -6544, -4248, -5872, 15624]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R379RS2]  
      rfl
    g := ![![![8907275, -8656068, -2396923, -5079216, 9872570], ![-9514043, 1788290, 0, 0, 0]], ![![-3336460, 3242360, 897830, 1902550, -3698026], ![3563729, -669851, 0, 0, 0]]]
    h := ![![![-120929365251712, 1097674631113, -48375519882325, 676452509998, 88471969], ![-320505128826340, -228541115143, -128213564095634, -266118047, 0]], ![![-117827415070646, 1069518262936, -47134643759543, 659100887224, 86202648], ![-312283875532540, -222678831423, -124924769459599, -259292061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R379N2 : Ideal.span {4} * I379N2 =  Ideal.span {B.equivFun.symm ![-2933, -1408, -729, -908, 2329]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E379RS2
                    

def R389RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-44, 21, 1, -3, 1] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-176, 84, 4, -12, 4], ![360, 40, 180, 228, -504]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E389RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I389N1) (Ideal.span {B.equivFun.symm ![-44, 21, 1, -3, 1]} * (J0 ^ 1*J1^ 1)) 
      ![![1556, 0, 0, 0, 0], ![668, 4, 0, 0, 0]] ![![-176, 84, 4, -12, 4], ![360, 40, 180, 228, -504]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R389RS1]  
      rfl
    g := ![![![3207595, -3124073, -868981, -1840396, 3575035], ![-3467875, 653310, 0, 0, 0]], ![![1390675, -1354357, -376659, -797739, 1549669], ![-1502867, 283101, 0, 0, 0]]]
    h := ![![![3848903088970, 29287015764, 1512506709900, 18114114165, 64157], ![-8965408973882, 6562453255, -3523183716918, -198072, 0]], ![![-20242961025324, -154032436478, -7954893536921, -95269560627, -337428], ![47152765408533, -34514633639, 18529869121002, 1041741, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R389N1 : Ideal.span {4} * I389N1 =  Ideal.span {B.equivFun.symm ![-44, 21, 1, -3, 1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E389RS1
                    

def R389RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![547, 282, 156, 201, -522] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![1094, 564, 312, 402, -1044], ![-3496, -1902, -1098, -1444, 3778]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E389RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I389N2) (Ideal.span {B.equivFun.symm ![547, 282, 156, 201, -522]} * (J0 ^ 1*J1^ 0)) 
      ![![778, 0, 0, 0, 0], ![-282, 2, 0, 0, 0]] ![![1094, 564, 312, 402, -1044], ![-3496, -1902, -1098, -1444, 3778]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R389RS2]  
      rfl
    g := ![![![17502, -8874, -903, -2918, 5831], ![1721, 0, 0, 0, 0]], ![![-6545, 3322, 339, 1093, -2185], ![-643, 0, 0, 0, 0]]]
    h := ![![![122481230283365, -1451662370539, 107171854202431, -1520101596591, -55194210], ![337909227916638, 488487636483, 295676119049178, 170401168, 0]], ![![-400765448013508, 4749920612421, -350672311726273, 4973857594442, 180598549], ![-1105657926529684, -1598358915126, -967468828087842, -557562172, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R389N2 : Ideal.span {2} * I389N2 =  Ideal.span {B.equivFun.symm ![547, 282, 156, 201, -522]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E389RS2
                    

def R409RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![95, 63, 109, 127, -290] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![190, 126, 218, 254, -580], ![1004, -580, -216, -148, 470]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E409RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I409N2) (Ideal.span {B.equivFun.symm ![95, 63, 109, 127, -290]} * (J0 ^ 1*J1^ 0)) 
      ![![818, 0, 0, 0, 0], ![-240, 2, 0, 0, 0]] ![![190, 126, 218, 254, -580], ![1004, -580, -216, -148, 470]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R409RS2]  
      rfl
    g := ![![![-2233, 731, 121, 430, -1093], ![-827, 0, 0, 0, 0]], ![![684, -229, -36, -129, 324], ![240, 0, 0, 0, 0]]]
    h := ![![![42331945893650, -698837148268, 49360826180741, -822675586190, -10212476], ![144281386397942, 222455532979, 168239991702543, 33150019, 0]], ![![29282584516168, -483411697170, 34144722775164, -569075357892, -7064345], ![99804811758988, 153880781146, 116377871297072, 22931090, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R409N2 : Ideal.span {2} * I409N2 =  Ideal.span {B.equivFun.symm ![95, 63, 109, 127, -290]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E409RS2
                    

def R419RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![5, 15, 18, 20, -47] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![20, 60, 72, 80, -188], ![180, -268, -220, -224, 552]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E419RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I419N2) (Ideal.span {B.equivFun.symm ![5, 15, 18, 20, -47]} * (J0 ^ 1*J1^ 1)) 
      ![![1676, 0, 0, 0, 0], ![792, 4, 0, 0, 0]] ![![20, 60, 72, 80, -188], ![180, -268, -220, -224, 552]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R419RS2]  
      rfl
    g := ![![![-700314, 680829, 188513, 399522, -776476], ![748679, -140742, 0, 0, 0]], ![![-350178, 340428, 94259, 199767, -388251], ![374342, -70371, 0, 0, 0]]]
    h := ![![![184377172267, 4557025760, 1132219421571, 11432964058, -3164737], ![-390172692121, 4431793251, -2395979484582, 10524006, 0]], ![![-174686967657, -4317524883, -1072714027150, -10832088448, 2998410], ![369666611171, -4198873937, 2270055391125, -9970902, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R419N2 : Ideal.span {4} * I419N2 =  Ideal.span {B.equivFun.symm ![5, 15, 18, 20, -47]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E419RS2
                    

def R431RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-12641, 25496, 22644, 23567, -57416] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-25282, 50992, 45288, 47134, -114832], ![124308, -27726, 21690, 34436, -66950]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E431RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I431N2) (Ideal.span {B.equivFun.symm ![-12641, 25496, 22644, 23567, -57416]} * (J0 ^ 1*J1^ 0)) 
      ![![862, 0, 0, 0, 0], ![34, 2, 0, 0, 0]] ![![-25282, 50992, 45288, 47134, -114832], ![124308, -27726, 21690, 34436, -66950]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R431RS2]  
      rfl
    g := ![![![1852020, -399678, -152921, -318158, 687593], ![-979271, 0, 0, 0, 0]], ![![84431, -17292, -6981, -14625, 32103], ![-43315, 0, 0, 0, 0]]]
    h := ![![![-40496286300085, -18603199279423, -276617983817845, -32543522195455, -515344288], ![1026698409015342, -1279713180449, 7013159000803940, 1762804212, 0]], ![![-30849476488716, -14171645037895, -210723534970241, -24791179310782, -392581625], ![782123777854500, -974866792694, 5342521970410680, 1342878150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R431N2 : Ideal.span {2} * I431N2 =  Ideal.span {B.equivFun.symm ![-12641, 25496, 22644, 23567, -57416]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E431RS2
                    

def R433RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-1868, 2314, 575, 1048, -2382] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-3736, 4628, 1150, 2096, -4764], ![-23602, 28558, 7028, 12870, -29198]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E433RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I433N1) (Ideal.span {B.equivFun.symm ![-1868, 2314, 575, 1048, -2382]} * (J0 ^ 1*J1^ 0)) 
      ![![866, 0, 0, 0, 0], ![250, 2, 0, 0, 0]] ![![-3736, 4628, 1150, 2096, -4764], ![-23602, 28558, 7028, 12870, -29198]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R433RS1]  
      rfl
    g := ![![![1948, -2353, 130, 275, -27], ![-573, 0, 0, 0, 0]], ![![628, -686, 24, 71, 13], ![-155, 0, 0, 0, 0]]]
    h := ![![![36376158725174, 2360234626278, 305685911020793, 4890967772658, -92783346], ![-126007052086100, 1303632789707, -1058906320255315, 318850686, 0]], ![![230784564994678, 14974250734540, 1939390866774212, 31030210703215, -588653803], ![-799437975891261, 8270755814568, -6718115465036780, 2022913350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R433N1 : Ideal.span {2} * I433N1 =  Ideal.span {B.equivFun.symm ![-1868, 2314, 575, 1048, -2382]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E433RS1
                    

def R439RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![1491, 979, 641, 889, -2368] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![2982, 1958, 1282, 1778, -4736], ![2456, 276, -316, -704, 2106]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E439RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I439N2) (Ideal.span {B.equivFun.symm ![1491, 979, 641, 889, -2368]} * (J0 ^ 1*J1^ 0)) 
      ![![878, 0, 0, 0, 0], ![-194, 2, 0, 0, 0]] ![![2982, 1958, 1282, 1778, -4736], ![2456, 276, -316, -704, 2106]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R439RS2]  
      rfl
    g := ![![![-3007, 2553, 167, -78, -479], ![437, 0, 0, 0, 0]], ![![614, -554, -20, 31, 73], ![-105, 0, 0, 0, 0]]]
    h := ![![![-141061037485295, 17417583505158, -1707371218640422, 35204010716395, -111840448], ![-638410202175788, -7416183886551, -7727251516941762, 389666304, 0]], ![![-21262385260632, 2625383861011, -257355151545299, 5306364201296, -16857909], ![-96228724210228, -1117854808977, -1164742595786952, 58735104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R439N2 : Ideal.span {2} * I439N2 =  Ideal.span {B.equivFun.symm ![1491, 979, 641, 889, -2368]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E439RS2
                    

def R443RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-16238, 19786, 4890, 8935, -20285] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-64952, 79144, 19560, 35740, -81140], ![-372936, 454484, 112160, 205156, -465696]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E443RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I443N1) (Ideal.span {B.equivFun.symm ![-16238, 19786, 4890, 8935, -20285]} * (J0 ^ 1*J1^ 1)) 
      ![![1772, 0, 0, 0, 0], ![-92, 4, 0, 0, 0]] ![![-64952, 79144, 19560, 35740, -81140], ![-372936, 454484, 112160, 205156, -465696]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R443RS1]  
      rfl
    g := ![![![5473849, -5221659, -1461496, -3063335, 5959024], ![-5600997, 1098330, 0, 0, 0]], ![![-264766, 253041, 70746, 148421, -288673], ![271973, -53145, 0, 0, 0]]]
    h := ![![![-252853181750092, 39440955861187, -657861135021315, 57204884683361, 1650762257], ![-4870175937971046, -2979257439739, -12671096700573526, -5803870636, 0]], ![![-1451866945162942, 226467469003963, -3777396945672196, 328466822520921, 9478572264], ![-27964241590823944, -17106707410735, -72756634230281269, -33325457376, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R443N1 : Ideal.span {4} * I443N1 =  Ideal.span {B.equivFun.symm ![-16238, 19786, 4890, 8935, -20285]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E443RS1
                    

def R449RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![3278, -3994, -986, -1803, 4093] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![13112, -15976, -3944, -7212, 16372], ![75360, -91812, -22664, -41444, 94080]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E449RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I449N1) (Ideal.span {B.equivFun.symm ![3278, -3994, -986, -1803, 4093]} * (J0 ^ 1*J1^ 1)) 
      ![![1796, 0, 0, 0, 0], ![96, 4, 0, 0, 0]] ![![13112, -15976, -3944, -7212, 16372], ![75360, -91812, -22664, -41444, 94080]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R449RS1]  
      rfl
    g := ![![![-6473643, 6291942, 1741900, 3691820, -7175659], ![6915861, -1299942, 0, 0, 0]], ![![-375549, 365003, 101050, 214167, -416268], ![401200, -75411, 0, 0, 0]]]
    h := ![![![1762647498616, 2398956508098, 56132172354788, 4677718306811, 48023057], ![-32976089997044, 249279537756, -1050150070131596, -171129750, 0]], ![![10121741739672, 13775651818241, 322330671501991, 26861103350883, 275765280], ![-189360304199412, 1431450759911, -6030330968555614, -982687200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R449N1 : Ideal.span {4} * I449N1 =  Ideal.span {B.equivFun.symm ![3278, -3994, -986, -1803, 4093]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E449RS1
                    

def R449RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-3341, -1787, -1003, -1307, 3404] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-6682, -3574, -2006, -2614, 6808], ![19228, 10380, 6152, 8124, -21338]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E449RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I449N2) (Ideal.span {B.equivFun.symm ![-3341, -1787, -1003, -1307, 3404]} * (J0 ^ 1*J1^ 0)) 
      ![![898, 0, 0, 0, 0], ![280, 2, 0, 0, 0]] ![![-6682, -3574, -2006, -2614, 6808], ![19228, 10380, 6152, 8124, -21338]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R449RS2]  
      rfl
    g := ![![![62, 24583, -7808, -7840, 11447], ![10687, 0, 0, 0, 0]], ![![-846, 7905, -2234, -2307, 3202], ![3240, 0, 0, 0, 0]]]
    h := ![![![5589454343571, 72150790472, 5482865305803, 78327602201, 347524], ![-17926178440651, 22249131558, -17584491587224, -1238372, 0]], ![![-16461328559034, -212489054408, -16147416450028, -230680190326, -1023485], ![52793831916496, -65525225856, 51787540434446, 3647096, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R449N2 : Ideal.span {2} * I449N2 =  Ideal.span {B.equivFun.symm ![-3341, -1787, -1003, -1307, 3404]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E449RS2
                    

def R457RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-58871, -36230, -22817, -31162, 82585] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-235484, -144920, -91268, -124648, 330340], ![530076, 283392, 161432, 211016, -550872]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E457RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I457N1) (Ideal.span {B.equivFun.symm ![-58871, -36230, -22817, -31162, 82585]} * (J0 ^ 1*J1^ 1)) 
      ![![1828, 0, 0, 0, 0], ![-660, 4, 0, 0, 0]] ![![-235484, -144920, -91268, -124648, 330340], ![530076, 283392, 161432, 211016, -550872]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R457RS1]  
      rfl
    g := ![![![-10267585, 9816376, 2774917, 5715418, -11189986], ![10536969, -1973700, 0, 0, 0]], ![![3670794, -3509714, -991706, -2042302, 3999222], ![-3764503, 705415, 0, 0, 0]]]
    h := ![![![1050088865882227, -8369094914023, 436111740368802, -5284293172810, -1138717031], ![2908428325211366, 1765878082801, 1207907041770720, 4130109252, 0]], ![![-2346762184410003, 18703441297692, -974632312636708, 11809457070194, 2544830442], ![-6499820949857058, -3946423998198, -2699457787069848, -9230060712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R457N1 : Ideal.span {4} * I457N1 =  Ideal.span {B.equivFun.symm ![-58871, -36230, -22817, -31162, 82585]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E457RS1
                    

def R463RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![5343, -6455, -1598, -2903, 6601] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![10686, -12910, -3196, -5806, 13202], ![5416, -6298, -1600, -2796, 6414]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E463RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I463N1) (Ideal.span {B.equivFun.symm ![5343, -6455, -1598, -2903, 6601]} * (J0 ^ 0*J1^ 1)) 
      ![![926, 0, 0, 0, 0], ![248, 2, 0, 0, 0]] ![![10686, -12910, -3196, -5806, 13202], ![5416, -6298, -1600, -2796, 6414]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R463RS1]  
      rfl
    g := ![![![-155413, 134926, 47036, 2079, 21898], ![348051, 0, 0, 0, 0]], ![![-43032, 37011, 12954, 655, 5760], ![95597, 0, 0, 0, 0]]]
    h := ![![![25601596168825, 394256812331, 26832849057639, 432824556623, 56365687], ![-95593031607568, 106685112209, -100191324925656, -207121480, 0]], ![![12501433817578, 192518287187, 13102662976493, 211351179340, 27523749], ![-46678728552044, 52095067047, -48924106450614, -101138830, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R463N1 : Ideal.span {2} * I463N1 =  Ideal.span {B.equivFun.symm ![5343, -6455, -1598, -2903, 6601]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E463RS1
                    

def R467RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-5780, 7662, 5975, 6006, -14936] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-11560, 15324, 11950, 12012, -29872], ![26478, -314, 10748, 14010, -30098]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E467RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I467N1) (Ideal.span {B.equivFun.symm ![-5780, 7662, 5975, 6006, -14936]} * (J0 ^ 1*J1^ 0)) 
      ![![934, 0, 0, 0, 0], ![-248, 2, 0, 0, 0]] ![![-11560, 15324, 11950, 12012, -29872], ![26478, -314, 10748, 14010, -30098]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R467RS1]  
      rfl
    g := ![![![-177749, 43831, 14601, 29811, -61517], ![101583, 0, 0, 0, 0]], ![![46179, -11457, -3789, -7730, 15908], ![-26492, 0, 0, 0, 0]]]
    h := ![![![273725487154116, -4599928068185, 341741747981900, -5511898305972, -80804200], ![1030885540268588, 1368972805759, 1287054459688065, 299488464, 0]], ![![372220047350728, -6255118732063, 464710567287690, -7495242837264, -109879613], ![1401828775980308, 1861569818737, 1750174837063134, 407252097, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R467N1 : Ideal.span {2} * I467N1 =  Ideal.span {B.equivFun.symm ![-5780, 7662, 5975, 6006, -14936]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E467RS1
                    

def R467RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![31, -39, -10, -18, 41] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![124, -156, -40, -72, 164], ![732, -876, -212, -392, 888]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E467RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I467N2) (Ideal.span {B.equivFun.symm ![31, -39, -10, -18, 41]} * (J0 ^ 1*J1^ 1)) 
      ![![1868, 0, 0, 0, 0], ![-396, 4, 0, 0, 0]] ![![124, -156, -40, -72, 164], ![732, -876, -212, -392, 888]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R467RS2]  
      rfl
    g := ![![![-334665, 325572, 90090, 191005, -371195], ![358137, -67230, 0, 0, 0]], ![![55770, -54270, -15016, -31838, 61872], ![-59707, 11205, 0, 0, 0]]]
    h := ![![![-328647826804, 19525005299, -1755426320893, 35462586666, 737419], ![-1550288647621, -7198371971, -8280718971420, -2733132, 0]], ![![-1673410768584, 99417526471, -8938289166266, 180568589198, 3754794], ![-7893768057349, -36652710665, -42163809320982, -13916576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R467N2 : Ideal.span {4} * I467N2 =  Ideal.span {B.equivFun.symm ![31, -39, -10, -18, 41]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E467RS2
                    

def R467RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![2467, 1264, 695, 893, -2317] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![4934, 2528, 1390, 1786, -4634], ![-16844, -9474, -5612, -7468, 19618]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E467RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I467N3) (Ideal.span {B.equivFun.symm ![2467, 1264, 695, 893, -2317]} * (J0 ^ 0*J1^ 1)) 
      ![![934, 0, 0, 0, 0], ![-76, 2, 0, 0, 0]] ![![4934, 2528, 1390, 1786, -4634], ![-16844, -9474, -5612, -7468, 19618]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R467RS3]  
      rfl
    g := ![![![228389, -129229, -14243, -44051, 87164], ![15547, 0, 0, 0, 0]], ![![-20788, 11763, 1297, 4010, -7935], ![-1415, 0, 0, 0, 0]]]
    h := ![![![8508634309149, -985891791439, 29342223137565, -1544322411435, -26560247], ![104566676289292, 125052170986, 360603663718693, 98441532, 0]], ![![-31313975951798, 3628336906961, -107986973933487, 5683506093134, 97748587], ![-384832426416738, -460224347545, -1327114794667896, -362290320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R467N3 : Ideal.span {2} * I467N3 =  Ideal.span {B.equivFun.symm ![2467, 1264, 695, 893, -2317]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E467RS3
                    

def R479RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![97, -112, -27, -50, 113] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![388, -448, -108, -200, 452], ![2148, -2624, -648, -1184, 2688]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E479RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I479N1) (Ideal.span {B.equivFun.symm ![97, -112, -27, -50, 113]} * (J0 ^ 1*J1^ 1)) 
      ![![1916, 0, 0, 0, 0], ![-136, 4, 0, 0, 0]] ![![388, -448, -108, -200, 452], ![2148, -2624, -648, -1184, 2688]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R479RS1]  
      rfl
    g := ![![![-4540809, 4413031, 1221827, 2589457, -5033051], ![4850529, -911778, 0, 0, 0]], ![![286185, -278134, -77007, -163202, 317212], ![-305704, 57465, 0, 0, 0]]]
    h := ![![![-13420238645, 9259135148, -304456112148, 17908841530, 716371], ![-189068681213, -1265752931, -4289283288665, -2723346, 0]], ![![-81328145495, 56111392591, -1845038029110, 108529579016, 4341288], ![-1145777330863, -7670605872, -25993535585130, -16503780, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R479N1 : Ideal.span {4} * I479N1 =  Ideal.span {B.equivFun.symm ![97, -112, -27, -50, 113]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E479RS1
                    

def R503RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-11, -4, -2, -3, 8] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-22, -8, -4, -6, 16], ![52, 26, 18, 24, -62]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E503RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I503N1) (Ideal.span {B.equivFun.symm ![-11, -4, -2, -3, 8]} * (J0 ^ 1*J1^ 0)) 
      ![![1006, 0, 0, 0, 0], ![310, 2, 0, 0, 0]] ![![-22, -8, -4, -6, 16], ![52, 26, 18, 24, -62]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R503RS1]  
      rfl
    g := ![![![235, -122, -8, -34, 57], ![-7, 0, 0, 0, 0]], ![![69, -38, -3, -11, 19], ![-3, 0, 0, 0, 0]]]
    h := ![![![458034272758, 15561331832, 2363683374083, 30500376011, 1224334], ![-1486394618600, 8576083770, -7670590410580, -4887619, 0]], ![![-1201623261678, -40824147044, -6200970303754, -80015761828, -3211961], ![3899460053476, -22498799117, 20123297337444, 12822352, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R503N1 : Ideal.span {2} * I503N1 =  Ideal.span {B.equivFun.symm ![-11, -4, -2, -3, 8]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E503RS1
                    

def R521RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![9, -2, -4, -7, 20] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![18, -4, -8, -14, 40], ![-412, -194, -98, -120, 306]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E521RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I521N1) (Ideal.span {B.equivFun.symm ![9, -2, -4, -7, 20]} * (J0 ^ 1*J1^ 0)) 
      ![![1042, 0, 0, 0, 0], ![166, 2, 0, 0, 0]] ![![18, -4, -8, -14, 40], ![-412, -194, -98, -120, 306]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R521RS1]  
      rfl
    g := ![![![-1564, 826, 69, 258, -515], ![-147, 0, 0, 0, 0]], ![![-232, 128, 12, 41, -83], ![-21, 0, 0, 0, 0]]]
    h := ![![![8285539398, 1498314273, 122119846488, 2942682199, 54070], ![-52009188828, 457071542, -766565135643, -223575, 0]], ![![1781334458176, 322127376400, 26254935054020, 632656625766, 11624643], ![-11181620863919, 98267168815, -164806281940473, -48066975, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R521N1 : Ideal.span {2} * I521N1 =  Ideal.span {B.equivFun.symm ![9, -2, -4, -7, 20]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E521RS1
                    

def R521RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-72, 66, 36, 33, -89] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-288, 264, 144, 132, -356], ![888, -484, -120, -52, 240]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E521RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I521N2) (Ideal.span {B.equivFun.symm ![-72, 66, 36, 33, -89]} * (J0 ^ 1*J1^ 1)) 
      ![![2084, 0, 0, 0, 0], ![-160, 4, 0, 0, 0]] ![![-288, 264, 144, 132, -356], ![888, -484, -120, -52, 240]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R521RS2]  
      rfl
    g := ![![![18368797, -17885093, -4971464, -10530069, 20456714], ![-19825185, 3733632, 0, 0, 0]], ![![-1371170, 1335412, 371413, 786622, -1528057], ![1482062, -279189, 0, 0, 0]]]
    h := ![![![-25881178922, 1527734260, -35610780038, 1780869579, -431029], ![-337101687106, -127808216, -463835432028, 1782270, 0]], ![![-15793981808, 932299156, -21731458018, 1086774639, -263040], ![-205716205186, -77994642, -283055305391, 1087650, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R521N2 : Ideal.span {4} * I521N2 =  Ideal.span {B.equivFun.symm ![-72, 66, 36, 33, -89]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E521RS2
                    

def R541RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-144, -76, -43, -56, 146] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-288, -152, -86, -112, 292], ![806, 450, 264, 350, -918]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E541RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I541N2) (Ideal.span {B.equivFun.symm ![-144, -76, -43, -56, 146]} * (J0 ^ 1*J1^ 0)) 
      ![![1082, 0, 0, 0, 0], ![-462, 2, 0, 0, 0]] ![![-288, -152, -86, -112, 292], ![806, 450, 264, 350, -918]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R541RS2]  
      rfl
    g := ![![![-351, 83, 73, 75, -165], ![-59, 0, 0, 0, 0]], ![![159, -32, -29, -29, 63], ![27, 0, 0, 0, 0]]]
    h := ![![![7484125013064, -219537041676, 62495494835889, -541122945336, 14852666], ![17527751841928, 195356888248, 146364764838800, -63772160, 0]], ![![-21379527033242, 627140529108, -178527766302204, 1545798956859, -42428871], ![-50070655378195, -558066288112, -418112931190240, 182174752, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R541N2 : Ideal.span {2} * I541N2 =  Ideal.span {B.equivFun.symm ![-144, -76, -43, -56, 146]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E541RS2
                    

def R557RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-486047, 592239, 146203, 267345, -606894] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-972094, 1184478, 292406, 534690, -1213788], ![-6042064, 7362132, 1817452, 3323368, -7544306]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E557RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I557N2) (Ideal.span {B.equivFun.symm ![-486047, 592239, 146203, 267345, -606894]} * (J0 ^ 1*J1^ 0)) 
      ![![1114, 0, 0, 0, 0], ![-418, 2, 0, 0, 0]] ![![-972094, 1184478, 292406, 534690, -1213788], ![-6042064, 7362132, 1817452, 3323368, -7544306]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R557RS2]  
      rfl
    g := ![![![55880, -33099, -4342, -6764, 3297], ![-59697, 0, 0, 0, 0]], ![![-20633, 12252, 1605, 2497, -1203], ![22083, 0, 0, 0, 0]]]
    h := ![![![-87070672123329, 33549242437903, -9193960145782807, 87982583898945, -777542502], ![-232049343606734, -28938108556968, -24502702776248910, 3437226720, 0]], ![![-541184902990602, 208524214540693, -57144757336203395, 546852860681972, -4832789885], ![-1442295074177978, -179863863347387, -152295744383025400, 21363969792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R557N2 : Ideal.span {2} * I557N2 =  Ideal.span {B.equivFun.symm ![-486047, 592239, 146203, 267345, -606894]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E557RS2
                    

def R557RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![24934, 15350, 9670, 13208, -35005] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![49868, 30700, 19340, 26416, -70010], ![95344, 38268, 15994, 17340, -41978]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E557RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I557N3) (Ideal.span {B.equivFun.symm ![24934, 15350, 9670, 13208, -35005]} * (J0 ^ 0*J1^ 1)) 
      ![![1114, 0, 0, 0, 0], ![-316, 2, 0, 0, 0]] ![![49868, 30700, 19340, 26416, -70010], ![95344, 38268, 15994, 17340, -41978]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R557RS3]  
      rfl
    g := ![![![158692, 26244, -58805, -54702, 103080], ![39197, 0, 0, 0, 0]], ![![-47691, -6259, 17245, 15910, -30376], ![-11217, 0, 0, 0, 0]]]
    h := ![![![817842533066714, -27664691725282, 4175061867417570, -52848952998812, -148381817], ![2883153802261128, 13875800958376, 14718501956069184, 655941564, 0]], ![![943467055108920, -31914120554378, 4816371316729104, -60966804666878, -171173897], ![3326020006620746, 16007190275913, 16979334174580988, 756697140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R557N3 : Ideal.span {2} * I557N3 =  Ideal.span {B.equivFun.symm ![24934, 15350, 9670, 13208, -35005]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E557RS3
                    

def R571RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-89, -1031, -1167, -1279, 3024] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-178, -2062, -2334, -2558, 6048], ![-8320, 3548, 404, -284, -314]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E571RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I571N1) (Ideal.span {B.equivFun.symm ![-89, -1031, -1167, -1279, 3024]} * (J0 ^ 1*J1^ 0)) 
      ![![1142, 0, 0, 0, 0], ![250, 2, 0, 0, 0]] ![![-178, -2062, -2334, -2558, 6048], ![-8320, 3548, 404, -284, -314]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R571RS1]  
      rfl
    g := ![![![57231, 4201, -4941, -12062, 34981], ![-6467, 0, 0, 0, 0]], ![![12750, 994, -1098, -2689, 7823], ![-1363, 0, 0, 0, 0]]]
    h := ![![![5877412101066, 335979613302, 39755108193725, 636092612595, 12083904], ![-26848011906331, 132817873298, -181602414733592, -54761160, 0]], ![![427004485490, 24409526962, 2888280730500, 46213282246, 877913], ![-1950556012334, 9649460022, -13193744877544, -3978480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R571N1 : Ideal.span {2} * I571N1 =  Ideal.span {B.equivFun.symm ![-89, -1031, -1167, -1279, 3024]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E571RS1
                    

def R571RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-259, 311, 78, 140, -319] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-1036, 1244, 312, 560, -1276], ![-5676, 6988, 1732, 3176, -7200]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E571RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I571N2) (Ideal.span {B.equivFun.symm ![-259, 311, 78, 140, -319]} * (J0 ^ 1*J1^ 1)) 
      ![![2284, 0, 0, 0, 0], ![-336, 4, 0, 0, 0]] ![![-1036, 1244, 312, 560, -1276], ![-5676, 6988, 1732, 3176, -7200]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R571RS2]  
      rfl
    g := ![![![4097923, -3969496, -1101092, -2330475, 4531261], ![-4350535, 822060, 0, 0, 0]], ![![-569166, 551289, 152927, 323662, -629316], ![604168, -114175, 0, 0, 0]]]
    h := ![![![4644398808332, -3142127672243, 270763556088243, -6446797306801, 6730541], ![31570848357634, 928293510132, 1840558572267168, -30501105, 0]], ![![23969423404749, -16216305204998, 1397392124666440, -33271478318554, 34735860], ![162934980986922, 4790859076359, 9498996434495139, -157414110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R571N2 : Ideal.span {4} * I571N2 =  Ideal.span {B.equivFun.symm ![-259, 311, 78, 140, -319]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E571RS2
                    

def R577RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![77369, -94271, -23272, -42555, 96603] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![154738, -188542, -46544, -85110, 193206], ![72484, -88310, -21800, -39864, 90494]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E577RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I577N1) (Ideal.span {B.equivFun.symm ![77369, -94271, -23272, -42555, 96603]} * (J0 ^ 0*J1^ 1)) 
      ![![1154, 0, 0, 0, 0], ![-180, 2, 0, 0, 0]] ![![154738, -188542, -46544, -85110, 193206], ![72484, -88310, -21800, -39864, 90494]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R577RS1]  
      rfl
    g := ![![![3423, -512, -986, -825, 1814], ![629, 0, 0, 0, 0]], ![![-550, 102, 162, 136, -305], ![-95, 0, 0, 0, 0]]]
    h := ![![![-12346155826554073, 2411593129118296, -214905586780164958, 4775694966798817, 11318516259], ![-79152585437733751, -727237486374126, -1377791652050502452, -51831617340, 0]], ![![-5782583545586974, 1129520714220797, -100655582792572601, 2236797876336352, 5301266791], ![-37072789666113946, -340617078021503, -645317898811761548, -24276435660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R577N1 : Ideal.span {2} * I577N1 =  Ideal.span {B.equivFun.symm ![77369, -94271, -23272, -42555, 96603]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E577RS1
                    

def R593RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![2208, -2685, -665, -1212, 2753] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![4416, -5370, -1330, -2424, 5506], ![2120, -2556, -646, -1156, 2634]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E593RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I593N1) (Ideal.span {B.equivFun.symm ![2208, -2685, -665, -1212, 2753]} * (J0 ^ 0*J1^ 1)) 
      ![![1186, 0, 0, 0, 0], ![-406, 2, 0, 0, 0]] ![![4416, -5370, -1330, -2424, 5506], ![2120, -2556, -646, -1156, 2634]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R593RS1]  
      rfl
    g := ![![![-39306, 9651, 6944, 5976, -15408], ![33797, 0, 0, 0, 0]], ![![13261, -3259, -2340, -2008, 5174], ![-11418, 0, 0, 0, 0]]]
    h := ![![![-1055290665334, 9532763910, -1139324338896, 11210322668, 7235731], ![-3082698893365, -3722027751, -3328185511253, -34053855, 0]], ![![-505216427788, 4563774793, -545447235012, 5366899744, 3464079], ![-1475830474023, -1781906772, -1593356275070, -16303155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R593N1 : Ideal.span {2} * I593N1 =  Ideal.span {B.equivFun.symm ![2208, -2685, -665, -1212, 2753]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E593RS1
                    

def R599RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![7997, -9737, -2406, -4395, 9979] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![15994, -19474, -4812, -8790, 19958], ![7556, -9170, -2280, -4140, 9410]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E599RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I599N1) (Ideal.span {B.equivFun.symm ![7997, -9737, -2406, -4395, 9979]} * (J0 ^ 0*J1^ 1)) 
      ![![1198, 0, 0, 0, 0], ![320, 2, 0, 0, 0]] ![![15994, -19474, -4812, -8790, 19958], ![7556, -9170, -2280, -4140, 9410]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R599RS1]  
      rfl
    g := ![![![23795, 22779, 1588, -9990, 33819], ![42967, 0, 0, 0, 0]], ![![6394, 6219, 448, -2703, 9162], ![11759, 0, 0, 0, 0]]]
    h := ![![![70002118792663, 868881119589, 79588724268715, 994885399279, 24375317], ![-262070421366288, 247277380145, -297961861658740, -115879404, 0]], ![![33072651645552, 410504754365, 37601864029545, 470035747556, 11516171], ![-123815734465436, 116826730811, -140772722656724, -54747474, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R599N1 : Ideal.span {2} * I599N1 =  Ideal.span {B.equivFun.symm ![7997, -9737, -2406, -4395, 9979]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E599RS1
                    

def R599RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-207, -107, -60, -78, 203] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-828, -428, -240, -312, 812], ![132, 4, -20, -40, 120]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E599RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I599N2) (Ideal.span {B.equivFun.symm ![-207, -107, -60, -78, 203]} * (J0 ^ 1*J1^ 1)) 
      ![![2396, 0, 0, 0, 0], ![-308, 4, 0, 0, 0]] ![![-828, -428, -240, -312, 812], ![132, 4, -20, -40, 120]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R599RS2]  
      rfl
    g := ![![![10100978, -9819248, -2719895, -5764123, 11202811], ![-10804379, 2031384, 0, 0, 0]], ![![-1262453, 1227266, 339963, 720460, -1400236], ![1350519, -253923, 0, 0, 0]]]
    h := ![![![5930419497020, -146756646822, 5541339392708, -143954387680, 22198771], ![46134022022486, 17425491946, 43107585046057, -105532251, 0]], ![![-366451107123, 9068352625, -342409148891, 8895195886, -1371702], ![-2850702796770, -1076751538, -2663693822070, 6521028, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R599N2 : Ideal.span {4} * I599N2 =  Ideal.span {B.equivFun.symm ![-207, -107, -60, -78, 203]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E599RS2
                    

def R617RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![219, -1407, -1306, -1476, 3487] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![876, -5628, -5224, -5904, 13948], ![-8820, 11996, 12764, 11472, -29208]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E617RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I617N1) (Ideal.span {B.equivFun.symm ![219, -1407, -1306, -1476, 3487]} * (J0 ^ 1*J1^ 1)) 
      ![![2468, 0, 0, 0, 0], ![1172, 4, 0, 0, 0]] ![![876, -5628, -5224, -5904, 13948], ![-8820, 11996, 12764, 11472, -29208]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R617RS1]  
      rfl
    g := ![![![-8536229, 4728026, 1871136, 3311427, -7005775], ![2659621, -1391670, 0, 0, 0]], ![![-4088099, 2263191, 895969, 1585703, -3355195], ![1273077, -666225, 0, 0, 0]]]
    h := ![![![59122833418655096, 246930093255191, 20927297339010915, 142849340238792, 146672261], ![-124500983646883166, 55337885291699, -44068934558028645, -718228425, 0]], ![![37016551030707150, 154601866477669, 13102490613353854, 89437355874618, 91830864], ![-77949528939252960, 34646811334530, -27591369876066654, -449679765, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R617N1 : Ideal.span {4} * I617N1 =  Ideal.span {B.equivFun.symm ![219, -1407, -1306, -1476, 3487]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E617RS1
                    

def R619RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-10463, 8905, 5376, 4946, -12977] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-41852, 35620, 21504, 19784, -51908], ![135132, -75804, -26444, -17064, 56520]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E619RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I619N2) (Ideal.span {B.equivFun.symm ![-10463, 8905, 5376, 4946, -12977]} * (J0 ^ 1*J1^ 1)) 
      ![![2476, 0, 0, 0, 0], ![-1096, 4, 0, 0, 0]] ![![-41852, 35620, 21504, 19784, -51908], ![135132, -75804, -26444, -17064, 56520]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R619RS2]  
      rfl
    g := ![![![20371823, -19067653, -5392846, -11363930, 22249988], ![-20729459, 3990506, 0, 0, 0]], ![![-8971655, 8398123, 2375086, 5004726, -9798686], ![9129524, -1757605, 0, 0, 0]]]
    h := ![![![-1197179948202355, 44628936102394, -16407260755754449, 119761824060026, -106108403], ![-2704578029627993, -44326652958289, -37066199838822574, 521278480, 0]], ![![-45440007250723710, 1693930126336501, -622751867142433692, 4545664304115067, -4027435560], ![-102654613837278702, -1682456706542936, -1406879886967451182, 19785576395, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R619N2 : Ideal.span {4} * I619N2 =  Ideal.span {B.equivFun.symm ![-10463, 8905, 5376, 4946, -12977]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E619RS2
                    

def R631RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-1563, 2013, 508, 919, -2095] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-3126, 4026, 1016, 1838, -4190], ![-1744, 1718, 372, 720, -1590]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E631RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I631N1) (Ideal.span {B.equivFun.symm ![-1563, 2013, 508, 919, -2095]} * (J0 ^ 0*J1^ 1)) 
      ![![1262, 0, 0, 0, 0], ![26, 2, 0, 0, 0]] ![![-3126, 4026, 1016, 1838, -4190], ![-1744, 1718, 372, 720, -1590]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R631RS1]  
      rfl
    g := ![![![-17829, 9269, 3338, 2104, -6915], ![-161, 0, 0, 0, 0]], ![![-419, 181, 94, 68, -190], ![-18, 0, 0, 0, 0]]]
    h := ![![![-53846620556, -58284332303, -704444929831, -108376646283, -162241], ![2613631183241, -2231381885, 34192847339790, 812476, 0]], ![![19306601038, 20897760021, 252577698404, 38858287880, 58173], ![-937112375835, 800059340, -12259795361287, -291333, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R631N1 : Ideal.span {2} * I631N1 =  Ideal.span {B.equivFun.symm ![-1563, 2013, 508, 919, -2095]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E631RS1
                    

def R641RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-2619, 526, -514, -791, 1564] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-5238, 1052, -1028, -1582, 3128], ![-10208, 8810, 5462, 5020, -13146]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E641RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I641N1) (Ideal.span {B.equivFun.symm ![-2619, 526, -514, -791, 1564]} * (J0 ^ 1*J1^ 0)) 
      ![![1282, 0, 0, 0, 0], ![410, 2, 0, 0, 0]] ![![-5238, 1052, -1028, -1582, 3128], ![-10208, 8810, 5462, 5020, -13146]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R641RS1]  
      rfl
    g := ![![![-636043, -71536, 55260, 137384, -409259], ![36893, 0, 0, 0, 0]], ![![-205477, -23690, 17861, 44463, -132701], ![11085, 0, 0, 0, 0]]]
    h := ![![![2535021522436, 21922327262, 2357133647835, 23017507313, 17128754], ![-7926573116084, 6042258461, -7370401381587, -87139125, 0]], ![![-4580800487154, -39613783248, -4259354166932, -41592769142, -30951753], ![14323369513892, -10918391287, 13318358025816, 157460850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R641N1 : Ideal.span {2} * I641N1 =  Ideal.span {B.equivFun.symm ![-2619, 526, -514, -791, 1564]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E641RS1
                    

def R641RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-75, 181, 208, 336, -935] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-300, 724, 832, 1344, -3740], ![-20748, -11740, -7012, -9352, 24576]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E641RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I641N2) (Ideal.span {B.equivFun.symm ![-75, 181, 208, 336, -935]} * (J0 ^ 1*J1^ 1)) 
      ![![2564, 0, 0, 0, 0], ![-696, 4, 0, 0, 0]] ![![-300, 724, 832, 1344, -3740], ![-20748, -11740, -7012, -9352, 24576]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R641RS2]  
      rfl
    g := ![![![202244122, -169641563, -30626587, -70252958, 144939674], ![-49303875, 3404328, 0, 0, 0]], ![![-56169744, 47094872, 8488243, 19477885, -40195323], ![13568878, -917733, 0, 0, 0]]]
    h := ![![![-2313037169721, 220491395517, -41787391217704, 480321930154, -2744491], ![-8521015036554, -121428826078, -153941607884014, 13962046, 0]], ![![34316300244261, -3271218061397, 619959199130602, -7126072972370, 40717344], ![126418076721012, 1801522318989, 2283883084240416, -207141360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R641N2 : Ideal.span {4} * I641N2 =  Ideal.span {B.equivFun.symm ![-75, 181, 208, 336, -935]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E641RS2
                    

def R643RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![84315, 62587, 43664, 61994, -166379] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![337260, 250348, 174656, 247976, -665516], ![-1743108, -962420, -562268, -743560, 1949064]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E643RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I643N1) (Ideal.span {B.equivFun.symm ![84315, 62587, 43664, 61994, -166379]} * (J0 ^ 1*J1^ 1)) 
      ![![2572, 0, 0, 0, 0], ![-100, 4, 0, 0, 0]] ![![337260, 250348, 174656, 247976, -665516], ![-1743108, -962420, -562268, -743560, 1949064]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R643RS1]  
      rfl
    g := ![![![11343107, -10994444, -3045092, -6410297, 12495019], ![-11952775, 2252634, 0, 0, 0]], ![![-439364, 426362, 117812, 248380, -484114], ![463403, -87431, 0, 0, 0]]]
    h := ![![![23858474300414055, -4273747867090818, 83236718417517285, -6658953845995224, -25150793273], ![613640036015979018, 258788471983794, 2140858538745245593, 128348888160, 0]], ![![-110066149292173139, 19716054129515485, -383995429046749041, 30719709855324358, 116027995542], ![-2830901715061345448, -1193867228552094, -9876409218709291162, -592111116240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R643N1 : Ideal.span {4} * I643N1 =  Ideal.span {B.equivFun.symm ![84315, 62587, 43664, 61994, -166379]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E643RS1
                    

def R659RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![614843, 330039, 188640, 246962, -645071] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![2459372, 1320156, 754560, 987848, -2580284], ![-1087884, -443068, -189076, -208256, 507792]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E659RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I659N0) (Ideal.span {B.equivFun.symm ![614843, 330039, 188640, 246962, -645071]} * (J0 ^ 1*J1^ 1)) 
      ![![2636, 0, 0, 0, 0], ![216, 4, 0, 0, 0]] ![![2459372, 1320156, 754560, 987848, -2580284], ![-1087884, -443068, -189076, -208256, 507792]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R659RS0]  
      rfl
    g := ![![![4668468, -4188434, -1249485, -2245073, 4611851], ![-3756567, 716856, 0, 0, 0]], ![![434961, -391543, -117380, -214090, 436188], ![-363344, 68523, 0, 0, 0]]]
    h := ![![![-695297501006098340, -32837251719719018, -1092480132443768810, -40462413147888209, -26745190423], ![8485204649348067222, -3292794384236839, 13332364922406909255, 139881586061, 0]], ![![269295920477647596, 12718207551644865, 423128865630537272, 15671511515401745, 10358688966], ![-3286407607076041480, 1275333354989434, -5163762963058521228, -54177586521, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R659N0 : Ideal.span {4} * I659N0 =  Ideal.span {B.equivFun.symm ![614843, 330039, 188640, 246962, -645071]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E659RS0
                    

def R659RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-296, 366, 277, 276, -690] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-592, 732, 554, 552, -1380], ![1154, 66, 556, 706, -1538]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E659RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I659N1) (Ideal.span {B.equivFun.symm ![-296, 366, 277, 276, -690]} * (J0 ^ 1*J1^ 0)) 
      ![![1318, 0, 0, 0, 0], ![210, 2, 0, 0, 0]] ![![-592, 732, 554, 552, -1380], ![1154, 66, 556, 706, -1538]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R659RS1]  
      rfl
    g := ![![![-5016, 3159, 338, 647, -523], ![3707, 0, 0, 0, 0]], ![![-800, 510, 56, 105, -85], ![611, 0, 0, 0, 0]]]
    h := ![![![18005985299846, 475515831393, 33585714481064, 639731302396, 1230666], ![-113008992533810, 99379994637, -210791290351576, -6436584, 0]], ![![-113159936797387, -2988414157667, -211071888593422, -4020438340385, -7734215], ![710213311835344, -624560869778, 1324733340975552, 40451166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R659N1 : Ideal.span {2} * I659N1 =  Ideal.span {B.equivFun.symm ![-296, 366, 277, 276, -690]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E659RS1
                    

def R659RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![599, 361, 222, 300, -793] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![2396, 1444, 888, 1200, -3172], ![-4284, -2284, -1276, -1656, 4320]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E659RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I659N2) (Ideal.span {B.equivFun.symm ![599, 361, 222, 300, -793]} * (J0 ^ 1*J1^ 1)) 
      ![![2636, 0, 0, 0, 0], ![-412, 4, 0, 0, 0]] ![![2396, 1444, 888, 1200, -3172], ![-4284, -2284, -1276, -1656, 4320]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R659RS2]  
      rfl
    g := ![![![16149254, -16033806, -4644625, -9776637, 18896933], ![-19349049, 3710784, 0, 0, 0]], ![![-2481031, 2466511, 716403, 1507385, -2912629], ![2992547, -574539, 0, 0, 0]]]
    h := ![![![-4645962140127, 2934698027303, -312529815147326, 6068607479646, -32639567], ![-29725111550414, -925864865345, -1999593019864737, 170710110, 0]], ![![7746826212901, -4893409571227, 521122232873831, -10118990659298, 54424260], ![49564603928060, 1543816759184, 3334185504380214, -284647510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R659N2 : Ideal.span {4} * I659N2 =  Ideal.span {B.equivFun.symm ![599, 361, 222, 300, -793]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E659RS2
                    

def R659RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![839, -1318, -358, -627, 1450] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![1678, -2636, -716, -1254, 2900], ![13076, -14858, -3530, -6560, 14774]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E659RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I659N3) (Ideal.span {B.equivFun.symm ![839, -1318, -358, -627, 1450]} * (J0 ^ 1*J1^ 0)) 
      ![![1318, 0, 0, 0, 0], ![-78, 2, 0, 0, 0]] ![![1678, -2636, -716, -1254, 2900], ![13076, -14858, -3530, -6560, 14774]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R659RS3]  
      rfl
    g := ![![![50590, -16338, -10947, -7256, 20287], ![4373, 0, 0, 0, 0]], ![![-3034, 1080, 632, 411, -1187], ![-221, 0, 0, 0, 0]]]
    h := ![![![-1150044426248, 1019877182250, -38897255968565, 1994717700483, 30824564], ![-19432863978424, -117673147437, -657266737090257, -161217351, 0]], ![![-6162732130984, 5465206180933, -208438356567625, 10689074819080, 165179303], ![-104134703411121, -630573979730, -3522089029014675, -863913915, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R659N3 : Ideal.span {2} * I659N3 =  Ideal.span {B.equivFun.symm ![839, -1318, -358, -627, 1450]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E659RS3
                    

def R673RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![9, 11, 10, 14, -37] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![36, 44, 40, 56, -148], ![-444, -300, -188, -240, 624]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E673RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I673N1) (Ideal.span {B.equivFun.symm ![9, 11, 10, 14, -37]} * (J0 ^ 1*J1^ 1)) 
      ![![2692, 0, 0, 0, 0], ![876, 4, 0, 0, 0]] ![![36, 44, 40, 56, -148], ![-444, -300, -188, -240, 624]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R673RS1]  
      rfl
    g := ![![![15374983, -14952358, -4145526, -8784137, 17070401], ![-16484127, 3100608, 0, 0, 0]], ![![5045538, -4906756, -1360338, -2882498, 5601648], ![-5408959, 1017387, 0, 0, 0]]]
    h := ![![![893824995084, 34389271469, 8210487912621, 74976976216, -3702883], ![-2746778622662, 22080352729, -25231413856825, 19778097, 0]], ![![-6433256712336, -247514909592, -59094539441789, -539642701552, 26651298], ![19769789509948, -158922130593, 181601726621150, -142351773, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R673N1 : Ideal.span {4} * I673N1 =  Ideal.span {B.equivFun.symm ![9, 11, 10, 14, -37]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E673RS1
                    

def R683RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-100, 92, 62, 59, -151] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-400, 368, 248, 236, -604], ![1392, -908, -408, -324, 936]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E683RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I683N1) (Ideal.span {B.equivFun.symm ![-100, 92, 62, 59, -151]} * (J0 ^ 1*J1^ 1)) 
      ![![2732, 0, 0, 0, 0], ![728, 4, 0, 0, 0]] ![![-400, 368, 248, 236, -604], ![1392, -908, -408, -324, 936]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R683RS1]  
      rfl
    g := ![![![19913939, -19370027, -5372426, -11383171, 22120070], ![-21372003, 4020768, 0, 0, 0]], ![![5331077, -5185345, -1438120, -3047133, 5921306], ![-5720638, 1076211, 0, 0, 0]]]
    h := ![![![-19214300107793, -481757034667, -78930763178445, -867375938594, -1382879], ![72106411325172, -215792439332, 296208392036575, 7496081, 0]], ![![37299838243093, 935212802794, 153224665035735, 1683797068460, 2684520], ![-139976864295358, 418907951082, -575015745736165, -14551801, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R683N1 : Ideal.span {4} * I683N1 =  Ideal.span {B.equivFun.symm ![-100, 92, 62, 59, -151]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E683RS1
                    

def R709RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-131, 87, 41, 33, -94] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-262, 174, 82, 66, -188], ![-44, 248, 260, 276, -662]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E709RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I709N1) (Ideal.span {B.equivFun.symm ![-131, 87, 41, 33, -94]} * (J0 ^ 1*J1^ 0)) 
      ![![1418, 0, 0, 0, 0], ![-658, 2, 0, 0, 0]] ![![-262, 174, 82, 66, -188], ![-44, 248, 260, 276, -662]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R709RS1]  
      rfl
    g := ![![![-13559, 3735, 1113, 2226, -4379], ![8339, 0, 0, 0, 0]], ![![6244, -1718, -510, -1021, 2005], ![-3841, 0, 0, 0, 0]]]
    h := ![![![574164198253, -5481927460, 1903248318616, -11570746379, 268382], ![1237332504282, 4414268403, 4101542656792, -1510182, 0]], ![![-4065206478100, 38813229437, -13475408231449, 81923377782, -1900207], ![-8760581254062, -31253969347, -29039805861570, 10692432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R709N1 : Ideal.span {2} * I709N1 =  Ideal.span {B.equivFun.symm ![-131, 87, 41, 33, -94]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E709RS1
                    

def R709RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![55, -2, -15, -28, 81] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![220, -8, -60, -112, 324], ![2700, 1552, 928, 1240, -3264]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E709RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I709N2) (Ideal.span {B.equivFun.symm ![55, -2, -15, -28, 81]} * (J0 ^ 1*J1^ 1)) 
      ![![2836, 0, 0, 0, 0], ![-64, 4, 0, 0, 0]] ![![220, -8, -60, -112, 324], ![2700, 1552, 928, 1240, -3264]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R709RS2]  
      rfl
    g := ![![![-2829518, 2741004, 753406, 1598574, -3109884], ![2967041, -555758, 0, 0, 0]], ![![30029, -28927, -7851, -16691, 32523], ![-30470, 5671, 0, 0, 0]]]
    h := ![![![-6170515029, 46045325960, -731296795893, 91412430254, 57213], ![-273431249041, -2061869862, -32405717309913, -321936, 0]], ![![2545905918375, -18997938403253, 301727291363353, -37716047892474, -23605584], ![112815580534425, 850711392443, 13370343427628228, 132828240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R709N2 : Ideal.span {4} * I709N2 =  Ideal.span {B.equivFun.symm ![55, -2, -15, -28, 81]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E709RS2
                    

def R719RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![201863, 127065, 81146, 111449, -295911] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![403726, 254130, 162292, 222898, -591822], ![1058104, 454262, 207856, 240420, -598786]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E719RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I719N2) (Ideal.span {B.equivFun.symm ![201863, 127065, 81146, 111449, -295911]} * (J0 ^ 0*J1^ 1)) 
      ![![1438, 0, 0, 0, 0], ![-382, 2, 0, 0, 0]] ![![403726, 254130, 162292, 222898, -591822], ![1058104, 454262, 207856, 240420, -598786]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R719RS2]  
      rfl
    g := ![![![448423, -170932, -100468, -73551, 197664], ![25791, 0, 0, 0, 0]], ![![-119291, 46191, 26542, 19338, -52328], ![-6614, 0, 0, 0, 0]]]
    h := ![![![-3497541468273847, 377467764994176, -79014596198368889, 827387677374405, -3491014653], ![-13166136214004726, -205296687073814, -297443459581535007, 19920946346, 0]], ![![-5965960082478668, 643868740538693, -134779796471748744, 1411323326638984, -5954826439], ![-22458244971716964, -350186510236253, -507366624308328135, 33980316748, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R719N2 : Ideal.span {2} * I719N2 =  Ideal.span {B.equivFun.symm ![201863, 127065, 81146, 111449, -295911]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E719RS2
                    

def R733RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![8, 1, 1, 1, -3] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![32, 4, 4, 4, -12], ![48, -40, -4, -12, 24]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E733RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I733N1) (Ideal.span {B.equivFun.symm ![8, 1, 1, 1, -3]} * (J0 ^ 1*J1^ 1)) 
      ![![2932, 0, 0, 0, 0], ![144, 4, 0, 0, 0]] ![![32, 4, 4, 4, -12], ![48, -40, -4, -12, 24]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R733RS1]  
      rfl
    g := ![![![-16876258, 16401829, 4541008, 9624220, -18706215], ![18028469, -3388814, 0, 0, 0]], ![![-846735, 822928, 227835, 482875, -938544], ![904544, -170027, 0, 0, 0]]]
    h := ![![![-348398847016, -329943991316, -11585326009137, -643631448073, -1629903], ![7093783684286, -31532531942, 235890996832975, 9481896, 0]], ![![467004906120, 442267429691, 15529339801766, 862744083019, 2184774], ![-9508733487178, 42267210705, -316195801750235, -12709836, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R733N1 : Ideal.span {4} * I733N1 =  Ideal.span {B.equivFun.symm ![8, 1, 1, 1, -3]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E733RS1
                    

def R733RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![3566, -4346, -1073, -1962, 4454] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![7132, -8692, -2146, -3924, 8908], ![44334, -54022, -13336, -24386, 55358]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E733RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I733N2) (Ideal.span {B.equivFun.symm ![3566, -4346, -1073, -1962, 4454]} * (J0 ^ 1*J1^ 0)) 
      ![![1466, 0, 0, 0, 0], ![-630, 2, 0, 0, 0]] ![![7132, -8692, -2146, -3924, 8908], ![44334, -54022, -13336, -24386, 55358]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R733RS2]  
      rfl
    g := ![![![-164, -75, 134, 59, -197], ![-435, 0, 0, 0, 0]], ![![80, 34, -56, -23, 79], ![187, 0, 0, 0, 0]]]
    h := ![![![12855930806012, -61935661892, 9672139988379, -61409582838, -351898], ![29915547020670, 22296985078, 22506986744550, 2047188, 0]], ![![80308891883784, -386901925838, 60420272703404, -383615595529, -2198249], ![186877517278153, 139285607986, 140597456040900, 12788446, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R733N2 : Ideal.span {2} * I733N2 =  Ideal.span {B.equivFun.symm ![3566, -4346, -1073, -1962, 4454]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E733RS2
                    

def R733RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![2301, 9836, 11737, 12988, -30541] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![9204, 39344, 46948, 51952, -122164], ![119580, -176968, -143968, -146360, 361488]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E733RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I733N3) (Ideal.span {B.equivFun.symm ![2301, 9836, 11737, 12988, -30541]} * (J0 ^ 1*J1^ 1)) 
      ![![2932, 0, 0, 0, 0], ![-932, 4, 0, 0, 0]] ![![9204, 39344, 46948, 51952, -122164], ![119580, -176968, -143968, -146360, 361488]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R733RS3]  
      rfl
    g := ![![![5602204, -13246253, -2425818, -7161003, 13066145], ![-22612443, 1536106, 0, 0, 0]], ![![-1782797, 4178952, 767671, 2260892, -4127506], ![7120825, -486629, 0, 0, 0]]]
    h := ![![![-14083298829728, 26216482833, 14415300940625, -122547543312, -527283505], ![-44304772662805, 86036224546, 45349252618950, 3067450624, 0]], ![![35329383386502, -65768006884, -36161766401617, 307418866276, 1322731668], ![111143015442927, -215828255892, -113761695743073, -7694938272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R733N3 : Ideal.span {4} * I733N3 =  Ideal.span {B.equivFun.symm ![2301, 9836, 11737, 12988, -30541]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E733RS3
                    

def R757RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1, -2, -5, -8, 23] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![4, -8, -20, -32, 92], ![540, 400, 216, 296, -768]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E757RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I757N1) (Ideal.span {B.equivFun.symm ![1, -2, -5, -8, 23]} * (J0 ^ 1*J1^ 1)) 
      ![![3028, 0, 0, 0, 0], ![296, 4, 0, 0, 0]] ![![4, -8, -20, -32, 92], ![540, 400, 216, 296, -768]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R757RS1]  
      rfl
    g := ![![![-5306358, 5157610, 1427696, 3026174, -5881840], ![5668973, -1065680, 0, 0, 0]], ![![-572859, 556794, 154131, 326694, -634982], ![611996, -115045, 0, 0, 0]]]
    h := ![![![5856753883, 1765967939, 127273592253, 3440097028, 1350491], ![-59911364655, 330933734, -1301983417966, -8113664, 0]], ![![-174858975391, -52724662416, -3799874725210, -102707384284, -40320192], ![1788710956133, -9880321686, 38871959178283, 242241152, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R757N1 : Ideal.span {4} * I757N1 =  Ideal.span {B.equivFun.symm ![1, -2, -5, -8, 23]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E757RS1
                    

def R757RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![241401, 126224, 70617, 91514, -238175] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![965604, 504896, 282468, 366056, -952700], ![-118356, 712, 29664, 56744, -164712]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E757RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I757N2) (Ideal.span {B.equivFun.symm ![241401, 126224, 70617, 91514, -238175]} * (J0 ^ 1*J1^ 1)) 
      ![![3028, 0, 0, 0, 0], ![1024, 4, 0, 0, 0]] ![![965604, 504896, 282468, 366056, -952700], ![-118356, 712, 29664, 56744, -164712]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R757RS2]  
      rfl
    g := ![![![-36368998, 35354792, 9779918, 20733496, -40302278], ![38834027, -7302330, 0, 0, 0]], ![![-12334261, 11990203, 3316809, 7031555, -13668143], ![13170118, -2476495, 0, 0, 0]]]
    h := ![![![-44188306842251474833, -234756015790743007, -20016730804560290230, -156381382761944404, -112728395087], ![130666204177442934037, -47445846761825095, 59190283955729563186, 677265038434, 0]], ![![1760936628446958113, 9355200425088122, 797681490299432432, 6231913476511114, 4492309650], ![-5207144638005877535, 1890751997589410, -2358776484434523061, -26989511478, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R757N2 : Ideal.span {4} * I757N2 =  Ideal.span {B.equivFun.symm ![241401, 126224, 70617, 91514, -238175]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E757RS2
                    

def R757RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![200, 104, 58, 75, -195] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![800, 416, 232, 300, -780], ![-48, 28, 40, 68, -192]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E757RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I757N3) (Ideal.span {B.equivFun.symm ![200, 104, 58, 75, -195]} * (J0 ^ 1*J1^ 1)) 
      ![![3028, 0, 0, 0, 0], ![1292, 4, 0, 0, 0]] ![![800, 416, 232, 300, -780], ![-48, 28, 40, 68, -192]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R757RS3]  
      rfl
    g := ![![![-27863032, 27079635, 7497161, 15889535, -30883938], ![29764525, -5594820, 0, 0, 0]], ![![-11911142, 11576246, 3204954, 6792602, -13202544], ![12724013, -2391725, 0, 0, 0]]]
    h := ![![![-37728427464, -1061036878, -439758834288, -2728061193, -2354883], ![88421694646, -974840416, 1030647035492, 14147986, 0]], ![![956087490, 26887993, 11144055262, 69132585, 59676], ![-2240720904, 24703828, -26117923334, -358530, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R757N3 : Ideal.span {4} * I757N3 =  Ideal.span {B.equivFun.symm ![200, 104, 58, 75, -195]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E757RS3
                    

def R773RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-16, 21, 16, 16, -40] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-32, 42, 32, 32, -80], ![66, 0, 30, 38, -82]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E773RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I773N1) (Ideal.span {B.equivFun.symm ![-16, 21, 16, 16, -40]} * (J0 ^ 1*J1^ 0)) 
      ![![1546, 0, 0, 0, 0], ![-104, 2, 0, 0, 0]] ![![-32, 42, 32, 32, -80], ![66, 0, 30, 38, -82]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R773RS1]  
      rfl
    g := ![![![-531, 478, 46, 43, 115], ![935, 0, 0, 0, 0]], ![![36, -26, -1, 0, -14], ![-58, 0, 0, 0, 0]]]
    h := ![![![35200718442, -18084630175, 913428949720, -35131950570, -59252], ![523272323236, 2352795546, 13578517615872, 363506, 0]], ![![62650470787, -32187143477, 1625726838076, -62528076139, -105457], ![931323531209, 4187520813, 24167134746688, 646970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R773N1 : Ideal.span {2} * I773N1 =  Ideal.span {B.equivFun.symm ![-16, 21, 16, 16, -40]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E773RS1
                    

def R787RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![137, -167, -41, -75, 170] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![274, -334, -82, -150, 340], ![1728, -2068, -508, -932, 2114]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E787RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I787N1) (Ideal.span {B.equivFun.symm ![137, -167, -41, -75, 170]} * (J0 ^ 1*J1^ 0)) 
      ![![1574, 0, 0, 0, 0], ![280, 2, 0, 0, 0]] ![![274, -334, -82, -150, 340], ![1728, -2068, -508, -932, 2114]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R787RS1]  
      rfl
    g := ![![![756, -237, -172, -104, 299], ![121, 0, 0, 0, 0]], ![![133, -41, -31, -19, 54], ![22, 0, 0, 0, 0]]]
    h := ![![![-3548856052969, -286026728555, -38879956394462, -555430860065, -1650058], ![19949639707800, -95767626411, 218561584804478, 10306316, 0]], ![![-22676584565888, -1827661984620, -248436286496540, -3549108411546, -10543589], ![127474793325148, -611938792194, 1396571229368918, 65855600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R787N1 : Ideal.span {2} * I787N1 =  Ideal.span {B.equivFun.symm ![137, -167, -41, -75, 170]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E787RS1
                    

def R829RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-790158, 962792, 237680, 434618, -986617] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-1580316, 1925584, 475360, 869236, -1973234], ![-740212, 901936, 222658, 407148, -924258]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E829RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I829N1) (Ideal.span {B.equivFun.symm ![-790158, 962792, 237680, 434618, -986617]} * (J0 ^ 0*J1^ 1)) 
      ![![1658, 0, 0, 0, 0], ![626, 2, 0, 0, 0]] ![![-1580316, 1925584, 475360, 869236, -1973234], ![-740212, 901936, 222658, 407148, -924258]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R829RS1]  
      rfl
    g := ![![![31048, -18568, -7703, -2274, 2762], ![-51027, 0, 0, 0, 0]], ![![11859, -7077, -2940, -874, 1074], ![-19454, 0, 0, 0, 0]]]
    h := ![![![12099511872859346, 413053945937522, 156163579270670970, 997790142703778, -30145717801], ![-32046320503822094, 329867347437014, -413609996647944894, 198339675162, 0]], ![![5667421599780421, 193474817800837, 73147152675046383, 467365747166356, -14120279727], ![-15010523641391100, 154510144671273, -193735272424142724, 92902471679, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R829N1 : Ideal.span {2} * I829N1 =  Ideal.span {B.equivFun.symm ![-790158, 962792, 237680, 434618, -986617]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E829RS1
                    

def R829RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![1306, 864, 564, 780, -2077] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![2612, 1728, 1128, 1560, -4154], ![10168, 4664, 2282, 2744, -6950]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E829RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I829N2) (Ideal.span {B.equivFun.symm ![1306, 864, 564, 780, -2077]} * (J0 ^ 0*J1^ 1)) 
      ![![1658, 0, 0, 0, 0], ![-342, 2, 0, 0, 0]] ![![2612, 1728, 1128, 1560, -4154], ![10168, 4664, 2282, 2744, -6950]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R829RS2]  
      rfl
    g := ![![![-297601422, 168398475, 18571021, 57388615, -113576383], ![-20247579, 0, 0, 0, 0]], ![![63004165, -35651045, -3931602, -12149538, 24044846], ![4286546, 0, 0, 0, 0]]]
    h := ![![![803780944901974, -11013378080685, 1175508860197815, -13748603310748, -43454401], ![3896692442177020, 2721694781229, 5698827807466508, 285902352, 0]], ![![2315013994793834, -31720239881389, 3385648140978406, -39598113477640, -125155423], ![11223079614244042, 7838903802477, 16413509438676778, 823443192, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R829N2 : Ideal.span {2} * I829N2 =  Ideal.span {B.equivFun.symm ![1306, 864, 564, 780, -2077]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E829RS2
                    

def R853RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![1, -5, -2, -3, 7] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![2, -10, -4, -6, 14], ![12, 2, 0, 0, -2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E853RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I853N1) (Ideal.span {B.equivFun.symm ![1, -5, -2, -3, 7]} * (J0 ^ 0*J1^ 1)) 
      ![![1706, 0, 0, 0, 0], ![674, 2, 0, 0, 0]] ![![2, -10, -4, -6, 14], ![12, 2, 0, 0, -2]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R853RS1]  
      rfl
    g := ![![![-109, -54, 8, 35, -106], ![-51, 0, 0, 0, 0]], ![![-41, -20, 4, 15, -45], ![-20, 0, 0, 0, 0]]]
    h := ![![![4863946, -4528843, -2115238673, -12446687, 46963], ![-12297261, -4453505, 5353976280, -317932, 0]], ![![86764922, -80776254, -37727519255, -221999828, 837635], ![-219363260, -79434031, 95493830450, -5670656, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R853N1 : Ideal.span {2} * I853N1 =  Ideal.span {B.equivFun.symm ![1, -5, -2, -3, 7]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E853RS1
                    

def R857RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![264, -343, -163, -206, 491] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![528, -686, -326, -412, 982], ![620, -976, -714, -772, 1878]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E857RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I857N2) (Ideal.span {B.equivFun.symm ![264, -343, -163, -206, 491]} * (J0 ^ 0*J1^ 1)) 
      ![![1714, 0, 0, 0, 0], ![846, 2, 0, 0, 0]] ![![528, -686, -326, -412, 982], ![620, -976, -714, -772, 1878]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R857RS2]  
      rfl
    g := ![![![-160838, 80445, 36700, 15330, -27988], ![229039, 0, 0, 0, 0]], ![![-80045, 39974, 18254, 7647, -13993], ![113846, 0, 0, 0, 0]]]
    h := ![![![1207242214147641, 4056907622329, 836492522739100, 3955069722550, 4629553], ![-2445878432747526, 1569380414936, -1694741519288048, -31488305, 0]], ![![2766522349834094, 9296829979220, 1916910486204143, 9063457734206, 10609107], ![-5604987358688976, 3596400077924, -3883678217578104, -72158760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R857N2 : Ideal.span {2} * I857N2 =  Ideal.span {B.equivFun.symm ![264, -343, -163, -206, 491]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E857RS2
                    

def R857RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![42166, 20342, 10583, 13216, -33932] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![84332, 40684, 21166, 26432, -67864], ![-349518, -182974, -102468, -132854, 345826]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E857RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I857N3) (Ideal.span {B.equivFun.symm ![42166, 20342, 10583, 13216, -33932]} * (J0 ^ 1*J1^ 0)) 
      ![![1714, 0, 0, 0, 0], ![-36, 2, 0, 0, 0]] ![![84332, 40684, 21166, 26432, -67864], ![-349518, -182974, -102468, -132854, 345826]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R857RS3]  
      rfl
    g := ![![![50387, -26291, -3317, -7429, 16281], ![3809, 0, 0, 0, 0]], ![![-1233, 671, 71, 186, -402], ![-90, 0, 0, 0, 0]]]
    h := ![![![1413717764384, -5662031376857, 100612535166224, -11178132687808, -1831509856], ![67319054535754, 241432867083, 4790259629232231, 12457173910, 0]], ![![-6319606858251, 25310441135604, -449758662094383, 49968545112763, 8187224929], ![-300929909400136, -1079254419745, -21413442752121189, -55686123740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R857N3 : Ideal.span {2} * I857N3 =  Ideal.span {B.equivFun.symm ![42166, 20342, 10583, 13216, -33932]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E857RS3
                    

def R881RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-18067, -11177, -7062, -9658, 25607] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-72268, -44708, -28248, -38632, 102428], ![168084, 90004, 51348, 67168, -175392]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E881RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I881N2) (Ideal.span {B.equivFun.symm ![-18067, -11177, -7062, -9658, 25607]} * (J0 ^ 1*J1^ 1)) 
      ![![3524, 0, 0, 0, 0], ![112, 4, 0, 0, 0]] ![![-72268, -44708, -28248, -38632, 102428], ![168084, 90004, 51348, 67168, -175392]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R881RS2]  
      rfl
    g := ![![![-370447240, 307513456, 53255339, 123294381, -256016179], ![70385003, -1789938, 0, 0, 0]], ![![-9957548, 8276976, 1441283, 3332679, -6914267], ![1960548, -63423, 0, 0, 0]]]
    h := ![![![35998563466237, 6858722245840, 156361252999611, 11168675412282, 89024767], ![-1132668752741913, 353555677267, -4919808677481180, -622466620, 0]], ![![-77774536975954, -14818200978933, -337816927219083, -24129811807625, -192337110], ![2447119532262980, -763853512175, 10629197566845984, 1344832937, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R881N2 : Ideal.span {4} * I881N2 =  Ideal.span {B.equivFun.symm ![-18067, -11177, -7062, -9658, 25607]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E881RS2
                    

def R883RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![35437, -43175, -10652, -19485, 44231] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![70874, -86350, -21304, -38970, 88462], ![33184, -40402, -9936, -18208, 41326]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E883RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I883N1) (Ideal.span {B.equivFun.symm ![35437, -43175, -10652, -19485, 44231]} * (J0 ^ 0*J1^ 1)) 
      ![![1766, 0, 0, 0, 0], ![220, 2, 0, 0, 0]] ![![70874, -86350, -21304, -38970, 88462], ![33184, -40402, -9936, -18208, 41326]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R883RS1]  
      rfl
    g := ![![![-165973, 94181, 40130, 13330, -19317], ![261097, 0, 0, 0, 0]], ![![-21354, 12045, 5152, 1739, -2570], ![33423, 0, 0, 0, 0]]]
    h := ![![![2751731378699369, 83910487332648, 6682287839002915, 121497164529361, 1509543005], ![-22088896806452633, 14871654933419, -53640686065677696, -10578781184, 0]], ![![1286171023208904, 39220120897607, 3123329934662233, 56788294681984, 705566861], ![-10324444902953924, 6951075163373, -25071886237356288, -4944567600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R883N1 : Ideal.span {2} * I883N1 =  Ideal.span {B.equivFun.symm ![35437, -43175, -10652, -19485, 44231]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E883RS1
                    

def R911RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-2076, 510, 1032, 1804, -5129] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-4152, 1020, 2064, 3608, -10258], ![176332, 89804, 49126, 62964, -163218]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E911RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I911N2) (Ideal.span {B.equivFun.symm ![-2076, 510, 1032, 1804, -5129]} * (J0 ^ 0*J1^ 1)) 
      ![![1822, 0, 0, 0, 0], ![-620, 2, 0, 0, 0]] ![![-4152, 1020, 2064, 3608, -10258], ![176332, 89804, 49126, 62964, -163218]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R911RS2]  
      rfl
    g := ![![![1934257088, -1094503973, -120702129, -372996649, 738188395], ![131598917, 0, 0, 0, 0]], ![![-667763901, 377855804, 41670021, 128769703, -254844921], ![-45431915, 0, 0, 0, 0]]]
    h := ![![![673354314175634, -19973034293038, 6963378449469530, -44925834961014, 249613709], ![1978792752073558, 13699602939804, 20463392067949350, -1804746778, 0]], ![![-54353972633878824, 1612247425248231, -562092309621272156, 3626467600195258, -20149120155], ![-159730538336269844, -1105848477536885, -1651829696407713825, 145681336346, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R911N2 : Ideal.span {2} * I911N2 =  Ideal.span {B.equivFun.symm ![-2076, 510, 1032, 1804, -5129]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E911RS2
                    

def R919RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![11412, 5261, 2614, 3182, -8090] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![22824, 10522, 5228, 6364, -16180], ![-108410, -55812, -30818, -39682, 103038]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E919RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I919N2) (Ideal.span {B.equivFun.symm ![11412, 5261, 2614, 3182, -8090]} * (J0 ^ 1*J1^ 0)) 
      ![![1838, 0, 0, 0, 0], ![818, 2, 0, 0, 0]] ![![22824, 10522, 5228, 6364, -16180], ![-108410, -55812, -30818, -39682, 103038]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R919RS2]  
      rfl
    g := ![![![-797354040, 405312498, 40865503, 132629933, -265237773], ![-77945263, 0, 0, 0, 0]], ![![-350953174, 178397180, 17986840, 58376701, -116743679], ![-34307391, 0, 0, 0, 0]]]
    h := ![![![-24853497483286256, -91148042861888, -18562296911336629, -90769634932264, -97615034], ![55844411189390054, -33711075232714, 41708519808763725, 711969906, 0]], ![![135887957584423489, 498357279114518, 101490448859017745, 496288311519241, 533715969], ![-305332598928347624, 184317284287392, -228043782343090092, -3892737492, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R919N2 : Ideal.span {2} * I919N2 =  Ideal.span {B.equivFun.symm ![11412, 5261, 2614, 3182, -8090]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E919RS2
                    

def R929RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-9510, -5960, -3796, -5208, 13823] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-19020, -11920, -7592, -10416, 27646], ![-47152, -20040, -9054, -10384, 25770]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E929RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I929N2) (Ideal.span {B.equivFun.symm ![-9510, -5960, -3796, -5208, 13823]} * (J0 ^ 0*J1^ 1)) 
      ![![1858, 0, 0, 0, 0], ![-678, 2, 0, 0, 0]] ![![-19020, -11920, -7592, -10416, 27646], ![-47152, -20040, -9054, -10384, 25770]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R929RS2]  
      rfl
    g := ![![![3924, -2866, -983, 192, 1152], ![-565, 0, 0, 0, 0]], ![![-1365, 1040, 350, -79, -405], ![216, 0, 0, 0, 0]]]
    h := ![![![-1859394692355720, 9354153871613, -1716232337463513, 10124789563904, 160060279], ![-5095509400886010, -3270244019015, -4703194877175272, -1180126868, 0]], ![![-3855363949661302, 19395380524240, -3558523805474697, 20993255925894, 331877127], ![-10565289516045293, -6780691013273, -9751844529948844, -2446935223, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R929N2 : Ideal.span {2} * I929N2 =  Ideal.span {B.equivFun.symm ![-9510, -5960, -3796, -5208, 13823]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E929RS2
                    

def R947RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![41605, 28752, 19357, 27131, -72515] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![83210, 57504, 38714, 54262, -145030], ![482124, 226878, 115140, 141840, -362294]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E947RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I947N1) (Ideal.span {B.equivFun.symm ![41605, 28752, 19357, 27131, -72515]} * (J0 ^ 0*J1^ 1)) 
      ![![1894, 0, 0, 0, 0], ![856, 2, 0, 0, 0]] ![![83210, 57504, 38714, 54262, -145030], ![482124, 226878, 115140, 141840, -362294]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R947RS1]  
      rfl
    g := ![![![87015, -44129, -6877, -18405, 35150], ![7639, 0, 0, 0, 0]], ![![38834, -19679, -3059, -8220, 15681], ![3419, 0, 0, 0, 0]]]
    h := ![![![-338548230678557709, -1199808312590869, -264768525095558557, -1237242463963647, -1361136673], ![749077510044724871, -464230607989220, 585832378307330104, 10230129816, 0]], ![![-1460670873723025312, -5176589027632417, -1142347346247212353, -5338099174979598, -5872642157], ![3231904945686062482, -2002929173340745, 2527581639333978456, 44138031282, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R947N1 : Ideal.span {2} * I947N1 =  Ideal.span {B.equivFun.symm ![41605, 28752, 19357, 27131, -72515]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E947RS1
                    

def R983RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![1634, 924, 552, 738, -1941] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![3268, 1848, 1104, 1476, -3882], ![-1604, -1484, -1118, -1624, 4394]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E983RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I983N1) (Ideal.span {B.equivFun.symm ![1634, 924, 552, 738, -1941]} * (J0 ^ 0*J1^ 1)) 
      ![![1966, 0, 0, 0, 0], ![938, 2, 0, 0, 0]] ![![3268, 1848, 1104, 1476, -3882], ![-1604, -1484, -1118, -1624, 4394]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R983RS1]  
      rfl
    g := ![![![-34867896, 19730096, 2175839, 6723832, -13306970], ![-2372267, 0, 0, 0, 0]], ![![-16476071, 9323026, 1028144, 3177199, -6287915], ![-1120964, 0, 0, 0, 0]]]
    h := ![![![22509408433326578, 140043573271309, 68621676938006073, 292628355633306, -569530587], ![-47178568350977960, 113739471820323, -143827765431468750, 4443242580, 0]], ![![-14860495784988384, -92455425316426, -45303373650195271, -193190436716874, 375998639], ![31146838807344080, -75089709557331, 94953712724056875, -2933386190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R983N1 : Ideal.span {2} * I983N1 =  Ideal.span {B.equivFun.symm ![1634, 924, 552, 738, -1941]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E983RS1
                    

def R991RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-155, -88, -55, -72, 187] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-620, -352, -220, -288, 748], ![516, 352, 216, 256, -648]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E991RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I991N1) (Ideal.span {B.equivFun.symm ![-155, -88, -55, -72, 187]} * (J0 ^ 1*J1^ 1)) 
      ![![3964, 0, 0, 0, 0], ![424, 4, 0, 0, 0]] ![![-620, -352, -220, -288, 748], ![516, 352, 216, 256, -648]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R991RS1]  
      rfl
    g := ![![![-51361495, 50037650, 13926275, 29491562, -57284200], ![55611803, -10479494, 0, 0, 0]], ![![-5560498, 5416474, 1507066, 3191640, -6199636], ![6016298, -1133561, 0, 0, 0]]]
    h := ![![![2105923294166112, 45394661710490, 2768524110944733, 52236422961433, 31249375], ![-19688396045584292, 5522734947589, -25883140818472730, -245778813, 0]], ![![-2058046709818906, -44362648172097, -2705583794688474, -51048867119571, -30538944], ![19240795149317620, -5397179715785, 25294707052488995, 240191217, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R991N1 : Ideal.span {4} * I991N1 =  Ideal.span {B.equivFun.symm ![-155, -88, -55, -72, 187]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E991RS1
                    

def R997RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![340, 124, 30, 19, -27] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![1360, 496, 120, 76, -108], ![6408, 4212, 2432, 3308, -8664]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E997RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I997N1) (Ideal.span {B.equivFun.symm ![340, 124, 30, 19, -27]} * (J0 ^ 1*J1^ 1)) 
      ![![3988, 0, 0, 0, 0], ![240, 4, 0, 0, 0]] ![![1360, 496, 120, 76, -108], ![6408, 4212, 2432, 3308, -8664]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R997RS1]  
      rfl
    g := ![![![-28319990, 27537154, 7619443, 16162536, -31407405], ![30290699, -5694150, 0, 0, 0]], ![![-1705518, 1658406, 458849, 973338, -1891425], ![1824166, -342925, 0, 0, 0]]]
    h := ![![![-77235537712880, -4069522620652, -168146557909712, -5604899647361, -38674071], ![1283397108491630, -335045528326, 2794041097136298, 306016260, 0]], ![![-772473614836854, -40701456109424, -1681722989052377, -56057576827471, -386799918], ![12835935801381314, -3350968196063, 27944688275654847, 3060631080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R997N1 : Ideal.span {4} * I997N1 =  Ideal.span {B.equivFun.symm ![340, 124, 30, 19, -27]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E997RS1
                    

def R1013RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![184, -193, -45, -85, 191] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![736, -772, -180, -340, 764], ![3840, -4624, -1132, -2076, 4704]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1013RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1013N1) (Ideal.span {B.equivFun.symm ![184, -193, -45, -85, 191]} * (J0 ^ 1*J1^ 1)) 
      ![![4052, 0, 0, 0, 0], ![-352, 4, 0, 0, 0]] ![![736, -772, -180, -340, 764], ![3840, -4624, -1132, -2076, 4704]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1013RS1]  
      rfl
    g := ![![![-5324511, 5175686, 1432585, 3037023, -5902628], ![5689833, -1069596, 0, 0, 0]], ![![443700, -431301, -119380, -253084, 491881], ![-474154, 89133, 0, 0, 0]]]
    h := ![![![-68900558348, 10169383273, -838592953700, 19058621603, 311611], ![-793139808926, -1644831165, -9653365956976, -2505252, 0]], ![![-13560852139632, 2001514840552, -165049952837564, 3751074442981, 61330584], ![-156103984245732, -323731927231, -1899953474320048, -493078416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1013N1 : Ideal.span {4} * I1013N1 =  Ideal.span {B.equivFun.symm ![184, -193, -45, -85, 191]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1013RS1
                    

def R1019RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![19648, 10086, 5555, 7144, -18542] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![39296, 20172, 11110, 14288, -37084], ![-128238, -69490, -40016, -52570, 137482]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1019RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1019N2) (Ideal.span {B.equivFun.symm ![19648, 10086, 5555, 7144, -18542]} * (J0 ^ 1*J1^ 0)) 
      ![![2038, 0, 0, 0, 0], ![-562, 2, 0, 0, 0]] ![![39296, 20172, 11110, 14288, -37084], ![-128238, -69490, -40016, -52570, 137482]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1019RS2]  
      rfl
    g := ![![![-254, 403, -1050, 715, -131], ![-753, 0, 0, 0, 0]], ![![131, -124, 281, -209, 59], ![219, 0, 0, 0, 0]]]
    h := ![![![176645392432298730, -3882079049667119, 1064707470720004584, -7577988587420140, -5343837742], ![640575286607725252, 1942085655307143, 3860992359350297698, 43217227306, 0]], ![![-585008988220235499, 12856554624867973, -3526066723960810114, 25096558564191633, 17697563851], ![-2121438295883640372, -6431741856406464, -12786720347294572704, -143125535678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1019N2 : Ideal.span {2} * I1019N2 =  Ideal.span {B.equivFun.symm ![19648, 10086, 5555, 7144, -18542]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1019RS2
                    

def R1021RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![3547, -4322, -1067, -1951, 4429] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![7094, -8644, -2134, -3902, 8858], ![3324, -4050, -1000, -1828, 4150]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1021RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1021N1) (Ideal.span {B.equivFun.symm ![3547, -4322, -1067, -1951, 4429]} * (J0 ^ 0*J1^ 1)) 
      ![![2042, 0, 0, 0, 0], ![642, 2, 0, 0, 0]] ![![7094, -8644, -2134, -3902, 8858], ![3324, -4050, -1000, -1828, 4150]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1021RS1]  
      rfl
    g := ![![![1995, -589, -391, -291, 706], ![-1813, 0, 0, 0, 0]], ![![637, -183, -122, -90, 218], ![-574, 0, 0, 0, 0]]]
    h := ![![![-142315284989033, -2919509050711, -969333276351700, -6039192946635, 129270913], ![452660192169400, -1729171928743, 3083149412396632, -1047504744, 0]], ![![-66680444826708, -1367907615744, -454171693908285, -2829605211466, 60568631], ![212089537476770, -810186716147, 1444579718206696, -490798176, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1021N1 : Ideal.span {2} * I1021N1 =  Ideal.span {B.equivFun.symm ![3547, -4322, -1067, -1951, 4429]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1021RS1
                    

def R1031RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-201, 249, 62, 113, -257] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-402, 498, 124, 226, -514], ![-176, 238, 60, 108, -246]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1031RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1031N2) (Ideal.span {B.equivFun.symm ![-201, 249, 62, 113, -257]} * (J0 ^ 0*J1^ 1)) 
      ![![2062, 0, 0, 0, 0], ![1026, 2, 0, 0, 0]] ![![-402, 498, 124, 226, -514], ![-176, 238, 60, 108, -246]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1031RS2]  
      rfl
    g := ![![![509, -305, -92, -52, 193], ![107, 0, 0, 0, 0]], ![![255, -151, -46, -26, 96], ![54, 0, 0, 0, 0]]]
    h := ![![![-12532885185165, -70745847410, -39409219533473, -153636176151, 1700441], ![25187923654218, -61311095268, 79202662923265, -13913928, 0]], ![![-4798665847040, -27087592322, -15089237072937, -58825135650, 651075], ![9644102472144, -23475157461, 30325588068090, -5327448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1031N2 : Ideal.span {2} * I1031N2 =  Ideal.span {B.equivFun.symm ![-201, 249, 62, 113, -257]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1031RS2
                    

def R1049RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-59, -30, -17, -22, 57] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-236, -120, -68, -88, 228], ![12, -8, -8, -16, 48]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1049RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1049N1) (Ideal.span {B.equivFun.symm ![-59, -30, -17, -22, 57]} * (J0 ^ 1*J1^ 1)) 
      ![![4196, 0, 0, 0, 0], ![768, 4, 0, 0, 0]] ![![-236, -120, -68, -88, 228], ![12, -8, -8, -16, 48]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1049RS1]  
      rfl
    g := ![![![25825919, -25099688, -6948951, -14727674, 28625688], ![-27587807, 5185638, 0, 0, 0]], ![![4805781, -4670646, -1293089, -2740584, 5326782], ![-5133650, 964965, 0, 0, 0]]]
    h := ![![![1008030261971303, 8910555641134, 751508718520388, 7828232012100, 2164245], ![-5507415336133458, 1386185559237, -4105906420063502, -18018198, 0]], ![![2576609527251, 22776124146, 1920919039711, 20009614724, 5532], ![-14077413507268, 3543206927, -10495039675792, -46056, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1049N1 : Ideal.span {4} * I1049N1 =  Ideal.span {B.equivFun.symm ![-59, -30, -17, -22, 57]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1049RS1
                    

def R1049RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1, 3, 2, 2, -5] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![4, 12, 8, 8, -20], ![60, -12, -4, 0, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1049RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1049N2) (Ideal.span {B.equivFun.symm ![1, 3, 2, 2, -5]} * (J0 ^ 1*J1^ 1)) 
      ![![4196, 0, 0, 0, 0], ![-424, 4, 0, 0, 0]] ![![4, 12, 8, 8, -20], ![60, -12, -4, 0, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1049RS2]  
      rfl
    g := ![![![-71205206, 69203562, 19159659, 40607041, -78926339], ![76066837, -14298264, 0, 0, 0]], ![![7145590, -6944724, -1922713, -4075003, 7920427], ![-7633466, 1434861, 0, 0, 0]]]
    h := ![![![59010510733, -10600033704, 1086566861195, -20501159852, -110665], ![583981505461, 2051059657, 10752930666780, 921330, 0]], ![![-23717241694, 4260318593, -436708126188, 8239735099, 44478], ![-234711246146, -824351406, -4321770127740, -370297, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1049N2 : Ideal.span {4} * I1049N2 =  Ideal.span {B.equivFun.symm ![1, 3, 2, 2, -5]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1049RS2
                    

def R1051RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-19205, 23393, 5774, 10559, -23969] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-38410, 46786, 11548, 21118, -47938], ![-17988, 21918, 5412, 9896, -22466]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1051RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1051N2) (Ideal.span {B.equivFun.symm ![-19205, 23393, 5774, 10559, -23969]} * (J0 ^ 0*J1^ 1)) 
      ![![2102, 0, 0, 0, 0], ![-378, 2, 0, 0, 0]] ![![-38410, 46786, 11548, 21118, -47938], ![-17988, 21918, 5412, 9896, -22466]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1051RS2]  
      rfl
    g := ![![![-7669, 1850, 2012, 1621, -3820], ![-921, 0, 0, 0, 0]], ![![1409, -340, -360, -287, 679], ![166, 0, 0, 0, 0]]]
    h := ![![![1449116493919573, -102979568778127, 19218154561994528, -203366098721043, -509865371], ![8058314809012472, 35427965858802, 106869395228847616, 4252924452, 0]], ![![679053562276716, -48256053473966, 9005595043916187, -95297013292036, -238922059], ![3776112824584850, 16601485471253, 50078819634560512, 1992913276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1051N2 : Ideal.span {2} * I1051N2 =  Ideal.span {B.equivFun.symm ![-19205, 23393, 5774, 10559, -23969]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1051RS2
                    

def R1061RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![9, -14, -4, -7, 16] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![18, -28, -8, -14, 32], ![136, -162, -38, -72, 162]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1061RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1061N2) (Ideal.span {B.equivFun.symm ![9, -14, -4, -7, 16]} * (J0 ^ 1*J1^ 0)) 
      ![![2122, 0, 0, 0, 0], ![-480, 2, 0, 0, 0]] ![![18, -28, -8, -14, 32], ![136, -162, -38, -72, 162]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1061RS2]  
      rfl
    g := ![![![534, -320, -35, -60, 27], ![-569, 0, 0, 0, 0]], ![![-116, 74, 9, 15, -10], ![128, 0, 0, 0, 0]]]
    h := ![![![14813853894, -1658386054, 424498992091, -3537738980, 104402], ![65489524144, 761025314, 1876642615326, -879131, 0]], ![![70133316133, -7851307379, 2009708082244, -16748738521, 494271], ![310047441608, 3602924422, 8884600203460, -4162075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1061N2 : Ideal.span {2} * I1061N2 =  Ideal.span {B.equivFun.symm ![9, -14, -4, -7, 16]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1061RS2
                    

def R1091RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-285, -177, -111, -151, 400] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-570, -354, -222, -302, 800], ![256, 276, 220, 328, -894]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1091RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1091N1) (Ideal.span {B.equivFun.symm ![-285, -177, -111, -151, 400]} * (J0 ^ 1*J1^ 0)) 
      ![![2182, 0, 0, 0, 0], ![314, 2, 0, 0, 0]] ![![-570, -354, -222, -302, 800], ![256, 276, 220, 328, -894]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1091RS1]  
      rfl
    g := ![![![499105, -253695, -25585, -83018, 166025], ![48789, 0, 0, 0, 0]], ![![69768, -35456, -3574, -11601, 23199], ![6821, 0, 0, 0, 0]]]
    h := ![![![1854663224809, 113175620095, 16585887908453, 211297549091, 14201480], ![-12888125692772, 29689250218, -115256295789876, -122966780, 0]], ![![-1504568040968, -91812043157, -13455055531853, -171412002328, -11520741], ![10455300868608, -24084963001, 93499960255854, 99754984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1091N1 : Ideal.span {2} * I1091N1 =  Ideal.span {B.equivFun.symm ![-285, -177, -111, -151, 400]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1091RS1
                    

def R1093RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![978, -1285, -323, -583, 1327] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![3912, -5140, -1292, -2332, 5308], ![23400, -29192, -7292, -13268, 30192]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1093RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1093N1) (Ideal.span {B.equivFun.symm ![978, -1285, -323, -583, 1327]} * (J0 ^ 1*J1^ 1)) 
      ![![4372, 0, 0, 0, 0], ![-600, 4, 0, 0, 0]] ![![3912, -5140, -1292, -2332, 5308], ![23400, -29192, -7292, -13268, 30192]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1093RS1]  
      rfl
    g := ![![![-59042743, 57385766, 15884697, 33665973, -65438564], ![63061961, -11855508, 0, 0, 0]], ![![8055132, -7829126, -2167122, -4593033, 8927742], ![-8603548, 1617455, 0, 0, 0]]]
    h := ![![![2262792324549006, -28696950035369, 2120033495379618, -28267259769155, 62580403], ![16488213350594402, 3803252456971, 15448002906397640, -542860152, 0]], ![![12808172218569030, -162434472759871, 12000108814042619, -160002280079031, 354226308], ![93328881258695700, 21527699171924, 87440937249542885, -3072772596, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1093N1 : Ideal.span {4} * I1093N1 =  Ideal.span {B.equivFun.symm ![978, -1285, -323, -583, 1327]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1093RS1
                    

def R1103RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-9951, 4358, 607, -204, -697] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-39804, 17432, 2428, -816, -2788], ![76308, -4424, 27120, 36176, -76776]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1103RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1103N1) (Ideal.span {B.equivFun.symm ![-9951, 4358, 607, -204, -697]} * (J0 ^ 1*J1^ 1)) 
      ![![4412, 0, 0, 0, 0], ![532, 4, 0, 0, 0]] ![![-39804, 17432, 2428, -816, -2788], ![76308, -4424, 27120, 36176, -76776]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1103RS1]  
      rfl
    g := ![![![58129559, -56275862, -15615521, -33032628, 64224166], ![-61603909, 11664006, 0, 0, 0]], ![![7079428, -6853274, -1901722, -4022748, 7821332], ![-7501725, 1420503, 0, 0, 0]]]
    h := ![![![7630311730754230, 122822900778219, 8961387531235983, 134758395232860, 717088105], ![-63279952968882917, 15976327772566, -74318997598895400, -6277366512, 0]], ![![-46693793905507858, -751616371273688, -54839329913226585, -824655787844540, -4388230182], ![387242512041795287, -97767349787433, 454796092004738700, 38414427552, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1103N1 : Ideal.span {4} * I1103N1 =  Ideal.span {B.equivFun.symm ![-9951, 4358, 607, -204, -697]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1103RS1
                    

def R1103RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-9368, 11411, 2786, 5132, -11640] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-18736, 22822, 5572, 10264, -23280], ![-117214, 142580, 35114, 64254, -145874]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1103RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1103N2) (Ideal.span {B.equivFun.symm ![-9368, 11411, 2786, 5132, -11640]} * (J0 ^ 1*J1^ 0)) 
      ![![2206, 0, 0, 0, 0], ![670, 2, 0, 0, 0]] ![![-18736, 22822, 5572, 10264, -23280], ![-117214, 142580, 35114, 64254, -145874]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1103RS2]  
      rfl
    g := ![![![1088657, -540028, -85890, -145947, 151269], ![-1013103, 0, 0, 0, 0]], ![![333740, -165354, -26330, -44763, 46521], ![-310299, 0, 0, 0, 0]]]
    h := ![![![-193715191085803866, -1131626267258442, -223046516136245753, -1331625804554018, -1245122268], ![637814494340732072, -370209080647556, 734390083445522105, 10899760714, 0]], ![![-1211325205399049209, -7076199924943486, -1394737632386313001, -8326821929528351, -7785904547], ![3988333434426232266, -2314963468494146, 4592232615761288772, 68157560654, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1103N2 : Ideal.span {2} * I1103N2 =  Ideal.span {B.equivFun.symm ![-9368, 11411, 2786, 5132, -11640]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1103RS2
                    

def R1103RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![561, 246, 116, 137, -344] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![1122, 492, 232, 274, -688], ![-5984, -3042, -1662, -2128, 5514]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1103RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1103N3) (Ideal.span {B.equivFun.symm ![561, 246, 116, 137, -344]} * (J0 ^ 1*J1^ 0)) 
      ![![2206, 0, 0, 0, 0], ![-642, 2, 0, 0, 0]] ![![1122, 492, 232, 274, -688], ![-5984, -3042, -1662, -2128, 5514]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1103RS3]  
      rfl
    g := ![![![-820658, 417180, 42051, 136512, -272995], ![-80223, 0, 0, 0, 0]], ![![242192, -123106, -12406, -40281, 80551], ![23677, 0, 0, 0, 0]]]
    h := ![![![2655420830316, -52766977767, 16926325470512, -105459385081, -252688], ![9124390059247, 28297573360, 58161262307960, 2212020, 0]], ![![-14566714633658, 289461278237, -92851931522627, 578513488886, 1386159], ![-50053228731892, -155230640321, -319052446113981, -12134370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1103N3 : Ideal.span {2} * I1103N3 =  Ideal.span {B.equivFun.symm ![561, 246, 116, 137, -344]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1103RS3
                    

def R1117RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-22, 12, 9, 8, -20] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-44, 24, 18, 16, -40], ![74, 30, 40, 50, -118]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1117RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1117N1) (Ideal.span {B.equivFun.symm ![-22, 12, 9, 8, -20]} * (J0 ^ 1*J1^ 0)) 
      ![![2234, 0, 0, 0, 0], ![-1018, 2, 0, 0, 0]] ![![-44, 24, 18, 16, -40], ![74, 30, 40, 50, -118]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1117RS1]  
      rfl
    g := ![![![12609, -6433, -645, -2089, 4153], ![1137, 0, 0, 0, 0]], ![![-5788, 2964, 300, 965, -1921], ![-521, 0, 0, 0, 0]]]
    h := ![![![4729111618786, -13452168874, 3216713726739, -12640836626, 331396], ![10378030715356, 4737226699, 7059084657065, -2937852, 0]], ![![-47668887713956, 135596279805, -32424095648273, 127418144905, -3340427], ![-104609326389571, -47750681759, -71154742247430, 29613150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1117N1 : Ideal.span {2} * I1117N1 =  Ideal.span {B.equivFun.symm ![-22, 12, 9, 8, -20]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1117RS1
                    

def R1123RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-511, -298, -177, -238, 629] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-2044, -1192, -708, -952, 2516], ![2892, 1432, 760, 992, -2592]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1123RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1123N1) (Ideal.span {B.equivFun.symm ![-511, -298, -177, -238, 629]} * (J0 ^ 1*J1^ 1)) 
      ![![4492, 0, 0, 0, 0], ![-1268, 4, 0, 0, 0]] ![![-2044, -1192, -708, -952, 2516], ![2892, 1432, 760, 992, -2592]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1123RS1]  
      rfl
    g := ![![![-36937517, 34185482, 8424293, 18194620, -35898434], ![28843583, -5048446, 0, 0, 0]], ![![10400608, -9617626, -2364908, -5109574, 10084234], ![-8071491, 1410331, 0, 0, 0]]]
    h := ![![![-482586706129216, 2195522701630, -250541983185460, 1580667111830, 14280989], ![-1709605277262906, -415117907852, -887568003206976, -127282143, 0]], ![![648976186856892, -2952509741264, 336925528239505, -2125660118328, -19204884], ![2299054449235959, 558245045153, 1193589651230752, 171167334, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1123N1 : Ideal.span {4} * I1123N1 =  Ideal.span {B.equivFun.symm ![-511, -298, -177, -238, 629]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1123RS1
                    

def R1129RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![16004, 8017, 4321, 5497, -14211] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![64016, 32068, 17284, 21988, -56844], ![24456, 18320, 12836, 18252, -49008]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1129RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1129N1) (Ideal.span {B.equivFun.symm ![16004, 8017, 4321, 5497, -14211]} * (J0 ^ 1*J1^ 1)) 
      ![![4516, 0, 0, 0, 0], ![980, 4, 0, 0, 0]] ![![64016, 32068, 17284, 21988, -56844], ![24456, 18320, 12836, 18252, -49008]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1129RS1]  
      rfl
    g := ![![![-88223839, 85749136, 23738783, 50317301, -97797156], ![94262597, -17718822, 0, 0, 0]], ![![-19200614, 18662035, 5166388, 10950803, -21284085], ![20514829, -3856237, 0, 0, 0]]]
    h := ![![![-16587666698860404, -107812918468197, -10794888604095665, -88122412273025, -480410361], ![76438676075281525, -18213363182541, 49744684179089760, 4304629233, 0]], ![![-8952986761002864, -58190681617745, -5826406841681478, -47562975830821, -259295520], ![41256824564578320, -9830436211581, 26849074489603170, 2323370078, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1129N1 : Ideal.span {4} * I1129N1 =  Ideal.span {B.equivFun.symm ![16004, 8017, 4321, 5497, -14211]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1129RS1
                    

def R1151RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-320762, -180951, -107420, -143076, 375970] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-641524, -361902, -214840, -286152, 751940], ![1164558, 711364, 445870, 607762, -1609634]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1151RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1151N1) (Ideal.span {B.equivFun.symm ![-320762, -180951, -107420, -143076, 375970]} * (J0 ^ 1*J1^ 0)) 
      ![![2302, 0, 0, 0, 0], ![262, 2, 0, 0, 0]] ![![-641524, -361902, -214840, -286152, 751940], ![1164558, 711364, 445870, 607762, -1609634]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1151RS1]  
      rfl
    g := ![![![281809, -154078, -8502, -45351, 89119], ![25005, 0, 0, 0, 0]], ![![30980, -16982, -922, -4971, 9777], ![2729, 0, 0, 0, 0]]]
    h := ![![![237159100570780424, 5954591742509997, 557139087286338944, 8505956274313944, 5212687298], ![-2083741404906155436, 955564177265028, -4895175931168475190, -47617481778, 0]], ![![-472896189631603888, -11873479613507060, -1110937555549497340, -16960910635481417, -10394119367], ![4154988647646831457, -1905398769314169, 9761000272741743424, 94949449100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1151N1 : Ideal.span {2} * I1151N1 =  Ideal.span {B.equivFun.symm ![-320762, -180951, -107420, -143076, 375970]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1151RS1
                    

def R1151RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![4, 11, -1, -2, 9] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![8, 22, -2, -4, 18], ![-868, -428, -238, -304, 790]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1151RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1151N2) (Ideal.span {B.equivFun.symm ![4, 11, -1, -2, 9]} * (J0 ^ 0*J1^ 1)) 
      ![![2302, 0, 0, 0, 0], ![630, 2, 0, 0, 0]] ![![8, 22, -2, -4, 18], ![-868, -428, -238, -304, 790]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1151RS2]  
      rfl
    g := ![![![-5076, 1230, 1336, 1075, -2527], ![-541, 0, 0, 0, 0]], ![![-1373, 331, 366, 296, -694], ![-148, 0, 0, 0, 0]]]
    h := ![![![-725547968021176, -4333377406016, -742995947848090, -4717445604294, -2093193], ![2651129240970020, -1200945807759, 2714887421279132, 19121152, 0]], ![![43670514808051856, 260824687705892, 44720703486171603, 283941637491824, 125988661], ![-159570674688267430, 72284568362712, -163408260458217876, -1150896416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1151N2 : Ideal.span {2} * I1151N2 =  Ideal.span {B.equivFun.symm ![4, 11, -1, -2, 9]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1151RS2
                    

def R1163RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![337, 139, 74, 89, -229] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![674, 278, 148, 178, -458], ![-3644, -1986, -1136, -1492, 3898]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1163RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1163N1) (Ideal.span {B.equivFun.symm ![337, 139, 74, 89, -229]} * (J0 ^ 0*J1^ 1)) 
      ![![2326, 0, 0, 0, 0], ![238, 2, 0, 0, 0]] ![![674, 278, 148, 178, -458], ![-3644, -1986, -1136, -1492, 3898]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1163RS1]  
      rfl
    g := ![![![20855, -9475, -4268, -2912, 8609], ![667, 0, 0, 0, 0]], ![![2157, -950, -444, -305, 889], ![78, 0, 0, 0, 0]]]
    h := ![![![-503206108090550, -15466590472946, -1365603019722990, -22951371136905, -48267497], ![4917888210307228, -2322852711335, 13346207168543964, 445516657, 0]], ![![2820518109767716, 86691711057636, 7654334845999147, 128644618765054, 270543913], ![-27565231295818545, 13019810442762, -74806760908328944, -2497163245, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1163N1 : Ideal.span {2} * I1163N1 =  Ideal.span {B.equivFun.symm ![337, 139, 74, 89, -229]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1163RS1
                    

def R1163RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![1386, -1688, -417, -762, 1730] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![2772, -3376, -834, -1524, 3460], ![17210, -20974, -5180, -9470, 21498]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1163RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1163N2) (Ideal.span {B.equivFun.symm ![1386, -1688, -417, -762, 1730]} * (J0 ^ 1*J1^ 0)) 
      ![![2326, 0, 0, 0, 0], ![-434, 2, 0, 0, 0]] ![![2772, -3376, -834, -1524, 3460], ![17210, -20974, -5180, -9470, 21498]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1163RS2]  
      rfl
    g := ![![![634, 2259, -90, -429, 2219], ![3133, 0, 0, 0, 0]], ![![-118, -412, 18, 81, -413], ![-573, 0, 0, 0, 0]]]
    h := ![![![-84656735959580, 1138740934319, -174966024969544, 1611732051564, 403984666], ![-453713547712588, -307920161326, -937721852890299, -3728842578, 0]], ![![-526028949183048, 7075759420721, -1087180992897777, 10014769738351, 2510227059], ![-2819225877635047, -1913314013839, -5826693355265286, -23169794118, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1163N2 : Ideal.span {2} * I1163N2 =  Ideal.span {B.equivFun.symm ![1386, -1688, -417, -762, 1730]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1163RS2
                    

def R1163RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-28, 29, 21, 20, -51] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-56, 58, 42, 40, -102], ![-152, 176, 130, 128, -322]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1163RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1163N3) (Ideal.span {B.equivFun.symm ![-28, 29, 21, 20, -51]} * (J0 ^ 0*J1^ 1)) 
      ![![2326, 0, 0, 0, 0], ![-30, 2, 0, 0, 0]] ![![-56, 58, 42, 40, -102], ![-152, 176, 130, 128, -322]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1163RS3]  
      rfl
    g := ![![![3654, -1763, -818, -364, 694], ![-5039, 0, 0, 0, 0]], ![![-27, 25, 12, 8, -18], ![54, 0, 0, 0, 0]]]
    h := ![![![6766651204, -14337685596, 208375344428, -27782944632, -839253], ![524648769790, 361073795, 16156037935972, 7746438, 0]], ![![39629690668, -83970337546, 1220374642313, -162714073542, -4915183], ![3072667384382, 2114664669, 94619730905999, 45367918, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1163N3 : Ideal.span {2} * I1163N3 =  Ideal.span {B.equivFun.symm ![-28, 29, 21, 20, -51]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1163RS3
                    

def R1171RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![175529, 88048, 47514, 60483, -156398] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![351058, 176096, 95028, 120966, -312796], ![-1262932, -674222, -383678, -501268, 1308374]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1171RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1171N2) (Ideal.span {B.equivFun.symm ![175529, 88048, 47514, 60483, -156398]} * (J0 ^ 1*J1^ 0)) 
      ![![2342, 0, 0, 0, 0], ![-706, 2, 0, 0, 0]] ![![351058, 176096, 95028, 120966, -312796], ![-1262932, -674222, -383678, -501268, 1308374]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1171RS2]  
      rfl
    g := ![![![-43598, 37802, -2411, 2036, -7191], ![2795, 0, 0, 0, 0]], ![![13085, -11416, 771, -603, 2123], ![-851, 0, 0, 0, 0]]]
    h := ![![![-40286817910641762, 697128127610328, -246934546522985365, 1399076958486359, -3896764538], ![-133642672040040127, -386573409065280, -819152243729877753, 36215167600, 0]], ![![152595930786136014, -2640539040407278, 935323486014707936, -5299337644085096, 14759925097], ![506203492614623620, 1464238980160328, 3102734481547649591, -137173584400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1171N2 : Ideal.span {2} * I1171N2 =  Ideal.span {B.equivFun.symm ![175529, 88048, 47514, 60483, -156398]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1171RS2
                    

def R1213RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-637, -328, -181, -233, 605] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-1274, -656, -362, -466, 1210], ![4200, 2370, 1408, 1876, -4930]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1213RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1213N1) (Ideal.span {B.equivFun.symm ![-637, -328, -181, -233, 605]} * (J0 ^ 0*J1^ 1)) 
      ![![2426, 0, 0, 0, 0], ![910, 2, 0, 0, 0]] ![![-1274, -656, -362, -466, 1210], ![4200, 2370, 1408, 1876, -4930]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1213RS1]  
      rfl
    g := ![![![-11743, 6768, 675, 2248, -4443], ![-775, 0, 0, 0, 0]], ![![-4353, 2520, 254, 839, -1661], ![-286, 0, 0, 0, 0]]]
    h := ![![![105457034181, 40459595482, 24297794546543, 106804325763, 220085], ![-281141430068, 35120657990, -64776395587876, -2118750, 0]], ![![-381071420450, -146201679383, -87800639659470, -385939888590, -795281], ![1015911028936, -126909305268, 234070995890428, 7656138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1213N1 : Ideal.span {2} * I1213N1 =  Ideal.span {B.equivFun.symm ![-637, -328, -181, -233, 605]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1213RS1
                    

def R1217RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-119, 110, 71, 67, -173] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-238, 220, 142, 134, -346], ![-636, 646, 440, 424, -1082]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1217RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1217N1) (Ideal.span {B.equivFun.symm ![-119, 110, 71, 67, -173]} * (J0 ^ 0*J1^ 1)) 
      ![![2434, 0, 0, 0, 0], ![528, 2, 0, 0, 0]] ![![-238, 220, 142, 134, -346], ![-636, 646, 440, 424, -1082]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1217RS1]  
      rfl
    g := ![![![2071, -1676, -209, -290, 361], ![-819, 0, 0, 0, 0]], ![![442, -360, -45, -61, 74], ![-181, 0, 0, 0, 0]]]
    h := ![![![-266024173532503, -2207247850111, -347961569569560, -2636077971981, -1226269], ![1226331132618913, -546067630617, 1604052184543172, 11844200, 0]], ![![-903887447454486, -7499708010423, -1182291408950571, -8956771701692, -4166573], ![4166784177835046, -1855409115905, 5450191294514988, 40243800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1217N1 : Ideal.span {2} * I1217N1 =  Ideal.span {B.equivFun.symm ![-119, 110, 71, 67, -173]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1217RS1
                    

def R1217RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-466, 398, 241, 222, -582] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-932, 796, 482, 444, -1164], ![466, 654, 912, 1034, -2398]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1217RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1217N2) (Ideal.span {B.equivFun.symm ![-466, 398, 241, 222, -582]} * (J0 ^ 1*J1^ 0)) 
      ![![2434, 0, 0, 0, 0], ![-574, 2, 0, 0, 0]] ![![-932, 796, 482, 444, -1164], ![466, 654, 912, 1034, -2398]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1217RS2]  
      rfl
    g := ![![![-5818, 3403, 188, 1041, -2359], ![-3961, 0, 0, 0, 0]], ![![1424, -818, -44, -249, 561], ![933, 0, 0, 0, 0]]]
    h := ![![![13856397079135458, -107361043917471, 18953902529902928, -132082701599652, -153407190], ![58756917308479556, 29515670642688, 80372574333839865, 1481718648, 0]], ![![16167710930280224, -125269383757700, 22115504870805186, -154114733151537, -178996249], ![68557854453254980, 34439026834891, 93779107302832094, 1728876459, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1217N2 : Ideal.span {2} * I1217N2 =  Ideal.span {B.equivFun.symm ![-466, 398, 241, 222, -582]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1217RS2
                    

def R1223RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![612, -749, -185, -339, 769] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![2448, -2996, -740, -1356, 3076], ![14208, -17272, -4252, -7780, 17664]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1223RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1223N1) (Ideal.span {B.equivFun.symm ![612, -749, -185, -339, 769]} * (J0 ^ 1*J1^ 1)) 
      ![![4892, 0, 0, 0, 0], ![-1460, 4, 0, 0, 0]] ![![2448, -2996, -740, -1356, 3076], ![14208, -17272, -4252, -7780, 17664]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1223RS1]  
      rfl
    g := ![![![-110981885, 107854773, 29861779, 63286224, -123007093], ![118539209, -22285674, 0, 0, 0]], ![![33080198, -32148129, -8900858, -18863641, 36664561], ![-35332851, 6642657, 0, 0, 0]]]
    h := ![![![-3715093330527586, 14306653275717, -1804333133798873, 9886300423089, 141888191], ![-12448107298338310, -2730775634815, -6045759169714485, -1377216324, 0]], ![![-21187362072285916, 81591555318840, -10290201619169807, 56382063109975, 809195412], ![-70992175156768978, -15573749291937, -34479265293058365, -7854333210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1223N1 : Ideal.span {4} * I1223N1 =  Ideal.span {B.equivFun.symm ![612, -749, -185, -339, 769]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1223RS1
                    

def R1229RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![8657, 6904, 4974, 7141, -19232] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![17314, 13808, 9948, 14282, -38464], ![83768, 33266, 13686, 14656, -35278]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1229RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1229N2) (Ideal.span {B.equivFun.symm ![8657, 6904, 4974, 7141, -19232]} * (J0 ^ 1*J1^ 0)) 
      ![![2458, 0, 0, 0, 0], ![-88, 2, 0, 0, 0]] ![![17314, 13808, 9948, 14282, -38464], ![83768, 33266, 13686, 14656, -35278]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1229RS2]  
      rfl
    g := ![![![64624, -15002, -15691, -11252, 28663], ![8267, 0, 0, 0, 0]], ![![-2426, 636, 569, 403, -1050], ![-280, 0, 0, 0, 0]]]
    h := ![![![2567519716655, -2476884596855, 106688806050049, -4849486418581, -14542324], ![71715542259967, 173422395967, 2980016141869260, 141845214, 0]], ![![5365711947822, -5176298440581, 222962789671422, -10134662298638, -30391135], ![149874191598676, 362425474071, 6227764063132950, 296434026, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1229N2 : Ideal.span {2} * I1229N2 =  Ideal.span {B.equivFun.symm ![8657, 6904, 4974, 7141, -19232]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1229RS2
                    

def R1237RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-520, 634, 156, 286, -649] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-1040, 1268, 312, 572, -1298], ![-480, 588, 142, 264, -598]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1237RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1237N2) (Ideal.span {B.equivFun.symm ![-520, 634, 156, 286, -649]} * (J0 ^ 0*J1^ 1)) 
      ![![2474, 0, 0, 0, 0], ![-818, 2, 0, 0, 0]] ![![-1040, 1268, 312, 572, -1298], ![-480, 588, 142, 264, -598]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1237RS2]  
      rfl
    g := ![![![-4208, 435, 625, 779, -2177], ![2337, 0, 0, 0, 0]], ![![1385, -141, -204, -254, 710], ![-768, 0, 0, 0, 0]]]
    h := ![![![31041442188182, -128318179914, 26595277874890, -130078159682, 7597883], ![93883283295606, 38129833246, 80436185621860, -74591920, 0]], ![![13384274927978, -55327512978, 11467202702145, -56086371094, 3276013], ![40480067490164, 16440607621, 34682023231805, -32162130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1237N2 : Ideal.span {2} * I1237N2 =  Ideal.span {B.equivFun.symm ![-520, 634, 156, 286, -649]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1237RS2
                    

def R1237RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-6470, 7160, 5136, 5032, -12707] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-12940, 14320, 10272, 10064, -25414], ![-33384, 41056, 31006, 30872, -77210]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1237RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1237N3) (Ideal.span {B.equivFun.symm ![-6470, 7160, 5136, 5032, -12707]} * (J0 ^ 0*J1^ 1)) 
      ![![2474, 0, 0, 0, 0], ![-628, 2, 0, 0, 0]] ![![-12940, 14320, 10272, 10064, -25414], ![-33384, 41056, 31006, 30872, -77210]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1237RS3]  
      rfl
    g := ![![![-94340, 173500, 47099, -19150, 91722], ![414397, 0, 0, 0, 0]], ![![23495, -43599, -11807, 4860, -23188], ![-104073, 0, 0, 0, 0]]]
    h := ![![![177635372281686, -1128860629118, 201484699750000, -1283203334192, -48395927], ![699792874647538, 309257930520, 793747972511308, 475124992, 0]], ![![721411595614440, -4584521252207, 818268308265154, -5211336755570, -196545097], ![2841994180632738, 1255956216451, 3223563930470343, 1929573384, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1237N3 : Ideal.span {2} * I1237N3 =  Ideal.span {B.equivFun.symm ![-6470, 7160, 5136, 5032, -12707]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1237RS3
                    

def R1249RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-67464, -47676, -32470, -45704, 122323] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-134928, -95352, -64940, -91408, 244646], ![-890300, -422656, -216418, -267928, 685650]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1249RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1249N2) (Ideal.span {B.equivFun.symm ![-67464, -47676, -32470, -45704, 122323]} * (J0 ^ 0*J1^ 1)) 
      ![![2498, 0, 0, 0, 0], ![678, 2, 0, 0, 0]] ![![-134928, -95352, -64940, -91408, 244646], ![-890300, -422656, -216418, -267928, 685650]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1249RS2]  
      rfl
    g := ![![![672400, -147341, -179937, -146261, 338021], ![76405, 0, 0, 0, 0]], ![![180897, -38856, -48614, -39603, 91227], ![20826, 0, 0, 0, 0]]]
    h := ![![![43491284836309698, 240832662733940, 44213480633857760, 260848437868440, 713937319], ![-160237801340398864, 65888320197732, -162898830354476080, -7077044358, 0]], ![![240416983222571345, 1331307236748513, 244409234464214563, 1441953135030980, 3946598691], ![-885784104596373030, 364226332554729, -900494099339574296, -39121439859, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1249N2 : Ideal.span {2} * I1249N2 =  Ideal.span {B.equivFun.symm ![-67464, -47676, -32470, -45704, 122323]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1249RS2
                    

def R1259RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-12190, 14853, 3667, 6705, -15221] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-48760, 59412, 14668, 26820, -60884], ![-280200, 341424, 84284, 154124, -349872]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1259RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1259N1) (Ideal.span {B.equivFun.symm ![-12190, 14853, 3667, 6705, -15221]} * (J0 ^ 1*J1^ 1)) 
      ![![5036, 0, 0, 0, 0], ![528, 4, 0, 0, 0]] ![![-48760, 59412, 14668, 26820, -60884], ![-280200, 341424, 84284, 154124, -349872]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1259RS1]  
      rfl
    g := ![![![70613946, -68625313, -19000150, -40266818, 78264611], ![-75422131, 14179968, 0, 0, 0]], ![![7472640, -7262184, -2010668, -4261183, 8282250], ![-7981430, 1500579, 0, 0, 0]]]
    h := ![![![-5351104210358234, -1975894437577633, -261145955806220426, -3956767526950405, -8772547039], ![51038173378812888, -410322338733039, 2490781608153484660, 87655846880, 0]], ![![-30751133314460718, -11354851424428410, -1500724670243717079, -22738313613862415, -50413102212], ![293300524901077366, -2357994993982244, 14313748018824253188, 503730917440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1259N1 : Ideal.span {4} * I1259N1 =  Ideal.span {B.equivFun.symm ![-12190, 14853, 3667, 6705, -15221]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1259RS1
                    

def R1279RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![12344, -15038, -3712, -6788, 15409] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![24688, -30076, -7424, -13576, 30818], ![11564, -14088, -3478, -6360, 14438]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1279RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1279N2) (Ideal.span {B.equivFun.symm ![12344, -15038, -3712, -6788, 15409]} * (J0 ^ 0*J1^ 1)) 
      ![![2558, 0, 0, 0, 0], ![-550, 2, 0, 0, 0]] ![![24688, -30076, -7424, -13576, 30818], ![11564, -14088, -3478, -6360, 14438]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1279RS2]  
      rfl
    g := ![![![-2764, 1429, 521, 323, -1039], ![301, 0, 0, 0, 0]], ![![595, -304, -108, -65, 213], ![-64, 0, 0, 0, 0]]]
    h := ![![![106540741374136, -2657900780676, 685002208061414, -4981586181548, -98038529], ![495511356891064, 1024993353582, 3185886575643552, 995169000, 0]], ![![49891937977458, -1244667712891, 320779518125216, -2332825786560, -45910439], ![232042893322090, 479993889447, 1491918052977880, 466027450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1279N2 : Ideal.span {2} * I1279N2 =  Ideal.span {B.equivFun.symm ![12344, -15038, -3712, -6788, 15409]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1279RS2
                    

def R1291RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-86648, 105579, 26064, 47660, -108192] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-173296, 211158, 52128, 95320, -216384], ![-1077118, 1312448, 323998, 592458, -1344926]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1291RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1291N2) (Ideal.span {B.equivFun.symm ![-86648, 105579, 26064, 47660, -108192]} * (J0 ^ 1*J1^ 0)) 
      ![![2582, 0, 0, 0, 0], ![-616, 2, 0, 0, 0]] ![![-173296, 211158, 52128, 95320, -216384], ![-1077118, 1312448, 323998, 592458, -1344926]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1291RS2]  
      rfl
    g := ![![![17063, -244, -1442, -3395, 9149], ![-4207, 0, 0, 0, 0]], ![![-4039, 64, 342, 804, -2164], ![1004, 0, 0, 0, 0]]]
    h := ![![![-11785694039554676, 77971356161602, -13683883219137461, 88867847700974, -3985368744], ![-49400423352440886, -19802360040457, -57356865949575633, 40834213812, 0]], ![![-73253620888247915, 484628579804014, -85051757686018630, 552355389745695, -24770937553], ![-307046820648280557, -123080963265465, -356499846297303813, 253803807210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1291N2 : Ideal.span {2} * I1291N2 =  Ideal.span {B.equivFun.symm ![-86648, 105579, 26064, 47660, -108192]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1291RS2
                    

def R1297RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-31525, -23212, -16132, -22873, 61360] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-63050, -46424, -32264, -45746, 122720], ![-195064, -71046, -25282, -23716, 53306]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1297RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1297N1) (Ideal.span {B.equivFun.symm ![-31525, -23212, -16132, -22873, 61360]} * (J0 ^ 1*J1^ 0)) 
      ![![2594, 0, 0, 0, 0], ![310, 2, 0, 0, 0]] ![![-63050, -46424, -32264, -45746, 122720], ![-195064, -71046, -25282, -23716, 53306]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1297RS1]  
      rfl
    g := ![![![-771953, 315130, 146234, 89832, -279141], ![-38209, 0, 0, 0, 0]], ![![-92688, 37052, 17808, 11037, -33883], ![-4929, 0, 0, 0, 0]]]
    h := ![![![76900959797204570, 1805720398356341, 208866685167618272, 2695058591387517, 1724507980], ![-643487384456142723, 317492636270339, -1747744573437728811, -17751482450, 0]], ![![141666763520680984, 3326493782979048, 384773706010458964, 4964830467296904, 3176884363], ![-1185430914811595247, 584884172372533, -3219690857551670457, -32701738033, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1297N1 : Ideal.span {2} * I1297N1 =  Ideal.span {B.equivFun.symm ![-31525, -23212, -16132, -22873, 61360]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1297RS1
                    

def R1361RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-3, 13, 8, 11, -25] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-6, 26, 16, 22, -50], ![32, 22, 32, 40, -90]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1361RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1361N2) (Ideal.span {B.equivFun.symm ![-3, 13, 8, 11, -25]} * (J0 ^ 0*J1^ 1)) 
      ![![2722, 0, 0, 0, 0], ![-290, 2, 0, 0, 0]] ![![-6, 26, 16, 22, -50], ![32, 22, 32, 40, -90]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1361RS2]  
      rfl
    g := ![![![-3387, -307, 370, 776, -2325], ![371, 0, 0, 0, 0]], ![![357, 33, -38, -80, 240], ![-40, 0, 0, 0, 0]]]
    h := ![![![521616784552, -58649498783, 8165855286121, -112632521451, -54809], ![4896003121763, 11865397946, 76646488865763, 592024, 0]], ![![4940203886036, -555466178272, 77338366446103, -1066736417988, -519093], ![46369776365520, 112376532241, 725914681929588, 5607028, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1361N2 : Ideal.span {2} * I1361N2 =  Ideal.span {B.equivFun.symm ![-3, 13, 8, 11, -25]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1361RS2
                    

def R1367RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-395, -173, -81, -95, 238] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-790, -346, -162, -190, 476], ![4296, 2180, 1188, 1520, -3938]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1367RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1367N1) (Ideal.span {B.equivFun.symm ![-395, -173, -81, -95, 238]} * (J0 ^ 1*J1^ 0)) 
      ![![2734, 0, 0, 0, 0], ![-394, 2, 0, 0, 0]] ![![-790, -346, -162, -190, 476], ![4296, 2180, 1188, 1520, -3938]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1367RS1]  
      rfl
    g := ![![![61373, -31179, -3169, -10192, 20409], ![5987, 0, 0, 0, 0]], ![![-9041, 4600, 469, 1505, -3015], ![-881, 0, 0, 0, 0]]]
    h := ![![![-454258720744786, 7348278150240, -1035671860504937, 10514137908471, 156368786], ![-3152140592412591, -1490097620530, -7186623623615752, -1696477224, 0]], ![![2642366465034132, -42744019813107, 6024374366532147, -61159432169080, -909577775], ![18335609673728988, 8667712484329, 41803695543989104, 9868196956, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1367N1 : Ideal.span {2} * I1367N1 =  Ideal.span {B.equivFun.symm ![-395, -173, -81, -95, 238]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1367RS1
                    

def R1373RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-3237, 3945, 974, 1781, -4043] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-6474, 7890, 1948, 3562, -8086], ![-3032, 3694, 912, 1668, -3786]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1373RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1373N1) (Ideal.span {B.equivFun.symm ![-3237, 3945, 974, 1781, -4043]} * (J0 ^ 0*J1^ 1)) 
      ![![2746, 0, 0, 0, 0], ![458, 2, 0, 0, 0]] ![![-6474, 7890, 1948, 3562, -8086], ![-3032, 3694, 912, 1668, -3786]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1373RS1]  
      rfl
    g := ![![![1129, 696, -24, -393, 1256], ![1185, 0, 0, 0, 0]], ![![193, 121, -2, -64, 206], ![202, 0, 0, 0, 0]]]
    h := ![![![-10660791285263, -31075473587361, -7512269749141122, -65609532782907, -86378611], ![63918132383728, -10646670276134, 45040860483984256, 941252610, 0]], ![![-4989636754734, -14544448064659, -3516014547837988, -30707639560990, -40428321], ![29916002865254, -4983027610448, 21080755350529792, 440540340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1373N1 : Ideal.span {2} * I1373N1 =  Ideal.span {B.equivFun.symm ![-3237, 3945, 974, 1781, -4043]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1373RS1
                    

def R1409RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-11366, -5811, -3189, -4094, 10619] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-22732, -11622, -6378, -8188, 21238], ![78856, 44284, 26202, 34848, -91526]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1409RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1409N2) (Ideal.span {B.equivFun.symm ![-11366, -5811, -3189, -4094, 10619]} * (J0 ^ 0*J1^ 1)) 
      ![![2818, 0, 0, 0, 0], ![1236, 2, 0, 0, 0]] ![![-22732, -11622, -6378, -8188, 21238], ![78856, 44284, 26202, 34848, -91526]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1409RS2]  
      rfl
    g := ![![![-12898, 24964, -2458, -4527, 1967], ![6223, 0, 0, 0, 0]], ![![-5893, 11014, -1018, -1938, 748], ![2707, 0, 0, 0, 0]]]
    h := ![![![155244151732469, 5834805787246, 5094061574852490, 16489687487375, 896990101], ![-353946374323059, 6061721728462, -11614141152013932, -10030627315, 0]], ![![-584043388196402, -21951098986808, -19164348214044308, -62035785846846, -3374562767], ![1331580207000072, -22804778516909, 43693512921602604, 37736181690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1409N2 : Ideal.span {2} * I1409N2 =  Ideal.span {B.equivFun.symm ![-11366, -5811, -3189, -4094, 10619]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1409RS2
                    

def R1427RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-152, 130, 13, 34, -80] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-304, 260, 26, 68, -160], ![-1578, 1802, 496, 814, -1886]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1427RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1427N1) (Ideal.span {B.equivFun.symm ![-152, 130, 13, 34, -80]} * (J0 ^ 1*J1^ 0)) 
      ![![2854, 0, 0, 0, 0], ![1130, 2, 0, 0, 0]] ![![-304, 260, 26, 68, -160], ![-1578, 1802, 496, 814, -1886]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1427RS1]  
      rfl
    g := ![![![42657, 18455, -3883, -11049, 38759], ![17107, 0, 0, 0, 0]], ![![16940, 7370, -1540, -4389, 15413], ![6849, 0, 0, 0, 0]]]
    h := ![![![436990313812854, 1215755710296, 342819686752547, 1213523692256, 403616], ![-1103690580075002, 415318302927, -865847979648855, -4571112, 0]], ![![-8605043125961982, -23940188120475, -6750671800096487, -23896236081607, -7947851], ![21733445202473556, -8178286309159, 17049941310999135, 90012559, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1427N1 : Ideal.span {2} * I1427N1 =  Ideal.span {B.equivFun.symm ![-152, 130, 13, 34, -80]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1427RS1
                    

def R1439RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![7069, 4289, 2676, 3641, -9637] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![14138, 8578, 5352, 7282, -19274], ![20404, 7506, 2720, 2600, -5906]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1439RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1439N1) (Ideal.span {B.equivFun.symm ![7069, 4289, 2676, 3641, -9637]} * (J0 ^ 0*J1^ 1)) 
      ![![2878, 0, 0, 0, 0], ![-1406, 2, 0, 0, 0]] ![![14138, 8578, 5352, 7282, -19274], ![20404, 7506, 2720, 2600, -5906]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1439RS1]  
      rfl
    g := ![![![-68987, 46464, 10070, 4637, -22710], ![3035, 0, 0, 0, 0]], ![![33489, -22679, -4848, -2202, 10960], ![-1518, 0, 0, 0, 0]]]
    h := ![![![-63453007419108045, 322027083522467, -265062629427116504, 754101503180539, -1826401223], ![-129884605068586858, -297378747950318, -542568167823006720, 20858661510, 0]], ![![-62498212440457456, 317181452802454, -261074158627711851, 742754328998596, -1798918847], ![-127930195439041762, -292904007565607, -534403994326630912, 20544795380, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1439N1 : Ideal.span {2} * I1439N1 =  Ideal.span {B.equivFun.symm ![7069, 4289, 2676, 3641, -9637]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1439RS1
                    

def R1439RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![57093, 33059, 19994, 26848, -70747] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![228372, 132236, 79976, 107392, -282988], ![-322908, -166660, -92220, -118872, 308784]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1439RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1439N2) (Ideal.span {B.equivFun.symm ![57093, 33059, 19994, 26848, -70747]} * (J0 ^ 1*J1^ 1)) 
      ![![5756, 0, 0, 0, 0], ![-408, 4, 0, 0, 0]] ![![228372, 132236, 79976, 107392, -282988], ![-322908, -166660, -92220, -118872, 308784]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1439RS2]  
      rfl
    g := ![![![38604845, -37474468, -10399158, -22005591, 42775741], ![-41195951, 7735392, 0, 0, 0]], ![![-2700405, 2621203, 727426, 1539166, -2991990], ![2881284, -541017, 0, 0, 0]]]
    h := ![![![208795891785956175, -41676953046618812, 4083075389241648050, -80060356606119838, -18091983269], ![2945659719405097146, 5646590259474610, 57603442384681290681, 206621935344, 0]], ![![-259513145946655233, 51800431062439223, -5074868716687350382, 99507297920034894, 22486589412], ![-3661170792837291320, -7018166830633909, -71595520499516388000, -256811127672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1439N2 : Ideal.span {4} * I1439N2 =  Ideal.span {B.equivFun.symm ![57093, 33059, 19994, 26848, -70747]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1439RS2
                    

def R1447RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![3922, 1949, 1043, 1322, -3413] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![7844, 3898, 2086, 2644, -6826], ![-32952, -18180, -10614, -14032, 36778]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1447RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1447N1) (Ideal.span {B.equivFun.symm ![3922, 1949, 1043, 1322, -3413]} * (J0 ^ 0*J1^ 1)) 
      ![![2894, 0, 0, 0, 0], ![1386, 2, 0, 0, 0]] ![![7844, 3898, 2086, 2644, -6826], ![-32952, -18180, -10614, -14032, 36778]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1447RS1]  
      rfl
    g := ![![![-1270058, 718774, 79210, 244901, -484677], ![-86387, 0, 0, 0, 0]], ![![-604307, 341998, 37688, 116525, -230611], ![-41104, 0, 0, 0, 0]]]
    h := ![![![1597808503798930, 6847063305806, 5023213895409992, 14496083680886, -183940307], ![-3336261091894596, 5652673849203, -10488594621535296, 2112393816, 0]], ![![-7044787305382722, -30188914719380, -22147506037094781, -63913683056564, 810998531], ![14709678745444346, -24922814515770, 46244539360220274, -9313609968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1447N1 : Ideal.span {2} * I1447N1 =  Ideal.span {B.equivFun.symm ![3922, 1949, 1043, 1322, -3413]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1447RS1
                    

def R1451RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![39003, -47524, -11732, -21453, 48700] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![78006, -95048, -23464, -42906, 97400], ![484840, -590774, -145842, -266684, 605394]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1451RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1451N2) (Ideal.span {B.equivFun.symm ![39003, -47524, -11732, -21453, 48700]} * (J0 ^ 1*J1^ 0)) 
      ![![2902, 0, 0, 0, 0], ![-1408, 2, 0, 0, 0]] ![![78006, -95048, -23464, -42906, 97400], ![484840, -590774, -145842, -266684, 605394]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1451RS2]  
      rfl
    g := ![![![518, 644, -177, -312, 511], ![-229, 0, 0, 0, 0]], ![![-248, -304, 91, 157, -262], ![112, 0, 0, 0, 0]]]
    h := ![![![15252469951631614, -31235720502832, 10999220684497073, -31237902553784, -1653249874], ![31436554240620274, 12475108619656, 22670285380299188, 19038615999, 0]], ![![94800084995840924, -194142258137575, 68364472055027147, -194155820439698, -10275596613], ![195390518613568126, 77537694629454, 140904718235664628, 118332468160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1451N2 : Ideal.span {2} * I1451N2 =  Ideal.span {B.equivFun.symm ![39003, -47524, -11732, -21453, 48700]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1451RS2
                    

def R1453RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-12, 6, 0, 1, -1] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-48, 24, 0, 4, -4], ![-96, 260, 80, 132, -312]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1453RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1453N1) (Ideal.span {B.equivFun.symm ![-12, 6, 0, 1, -1]} * (J0 ^ 1*J1^ 1)) 
      ![![5812, 0, 0, 0, 0], ![-432, 4, 0, 0, 0]] ![![-48, 24, 0, 4, -4], ![-96, 260, 80, 132, -312]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1453RS1]  
      rfl
    g := ![![![54872920, -53330154, -14764981, -31292840, 60822785], ![-58618773, 11018604, 0, 0, 0]], ![![-3993915, 3881625, 1074666, 2277643, -4426974], ![4266556, -801987, 0, 0, 0]]]
    h := ![![![-1099800527469, 679306481027, -73068183347046, 1353115514848, 210089], ![-14796390766230, -100023318395, -983038614141165, -2422693, 0]], ![![2852050823733, -1761607273619, 189483608452856, -3508958327172, -544812], ![38370647602996, 259384846389, 2549258724159798, 6282633, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1453N1 : Ideal.span {4} * I1453N1 =  Ideal.span {B.equivFun.symm ![-12, 6, 0, 1, -1]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1453RS1
                    

def R1471RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![58, 126, 110, 169, -463] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![232, 504, 440, 676, -1852], ![-8232, -4460, -2688, -3564, 9384]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1471RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1471N1) (Ideal.span {B.equivFun.symm ![58, 126, 110, 169, -463]} * (J0 ^ 1*J1^ 1)) 
      ![![5884, 0, 0, 0, 0], ![-2752, 4, 0, 0, 0]] ![![232, 504, 440, 676, -1852], ![-8232, -4460, -2688, -3564, 9384]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1471RS1]  
      rfl
    g := ![![![49955478, -48540736, -13442491, -28479300, 55359587], ![-53337421, 10025484, 0, 0, 0]], ![![-23277414, 22618193, 6263697, 13270277, -25795490], ![24853206, -4671499, 0, 0, 0]]]
    h := ![![![4110855753767830, -7341444075388, 1466730888320598, -4263744588117, -1914193], ![8789344206580944, 1636730827476, 3135992401939218, 22347440, 0]], ![![-56291163379225878, 100528564530334, -20084379750998511, 58384715390481, 26211606], ![-120355089150336360, -22412239165599, -42942071240423781, -306010080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1471N1 : Ideal.span {4} * I1471N1 =  Ideal.span {B.equivFun.symm ![58, 126, 110, 169, -463]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1471RS1
                    

def R1471RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-10622, 12846, 3135, 5754, -13066] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-21244, 25692, 6270, 11508, -26132], ![-131570, 160082, 39600, 72254, -164090]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1471RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1471N2) (Ideal.span {B.equivFun.symm ![-10622, 12846, 3135, 5754, -13066]} * (J0 ^ 1*J1^ 0)) 
      ![![2942, 0, 0, 0, 0], ![-778, 2, 0, 0, 0]] ![![-21244, 25692, 6270, 11508, -26132], ![-131570, 160082, 39600, 72254, -164090]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1471RS2]  
      rfl
    g := ![![![-2071063, 622197, 168715, 332205, -623673], ![1346353, 0, 0, 0, 0]], ![![543759, -163602, -44289, -87181, 163523], ![-353841, 0, 0, 0, 0]]]
    h := ![![![34921845116819594, -606038461967220, 231028117642695211, -1187804492502216, -505397974], ![132056643329939444, 293586516862807, 873631502305934105, 5900320688, 0]], ![![220134786731455738, -3820249105677300, 1456318394290960846, -7487493509027043, -3185847565], ![832437716812015522, 1850664106107589, 5507059658460606090, 37193505445, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1471N2 : Ideal.span {2} * I1471N2 =  Ideal.span {B.equivFun.symm ![-10622, 12846, 3135, 5754, -13066]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1471RS2
                    

def R1493RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-28, 118, 4, 59, -111] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-112, 472, 16, 236, -444], ![-5928, 5868, 1336, 2252, -5304]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1493RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1493N1) (Ideal.span {B.equivFun.symm ![-28, 118, 4, 59, -111]} * (J0 ^ 1*J1^ 1)) 
      ![![5972, 0, 0, 0, 0], ![2016, 4, 0, 0, 0]] ![![-112, 472, 16, 236, -444], ![-5928, 5868, 1336, 2252, -5304]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1493RS1]  
      rfl
    g := ![![![75755863, -73836922, -20409602, -43278358, 84073899], ![-81239495, 15239268, 0, 0, 0]], ![![25588164, -24940269, -6893813, -14618271, 28397844], ![-27440694, 5147433, 0, 0, 0]]]
    h := ![![![-12046117598247374, -31954358858888, -5102803483905985, -20249246561183, -2802327], ![35684233281121526, -6135770272497, 15116055036911364, 33205350, 0]], ![![99712235788740582, 264503524806495, 42238666526969491, 167613974478503, 23196378], ![-295377714342196052, 50789091783143, -125123769692711188, -274858680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1493N1 : Ideal.span {4} * I1493N1 =  Ideal.span {B.equivFun.symm ![-28, 118, 4, 59, -111]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1493RS1
                    

def R1511RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-343, -109, 14, 51, -175] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-686, -218, 28, 102, -350], ![15768, 8050, 4452, 5724, -14866]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1511RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1511N1) (Ideal.span {B.equivFun.symm ![-343, -109, 14, 51, -175]} * (J0 ^ 0*J1^ 1)) 
      ![![3022, 0, 0, 0, 0], ![-688, 2, 0, 0, 0]] ![![-686, -218, 28, 102, -350], ![15768, 8050, 4452, 5724, -14866]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1511RS1]  
      rfl
    g := ![![![159401, -95994, -26308, -14449, 56780], ![-3081, 0, 0, 0, 0]], ![![-35926, 21863, 5870, 3183, -12714], ![773, 0, 0, 0, 0]]]
    h := ![![![-11573957235938769, 73265413340362, -15120101154748771, 87907284367109, 112766647], ![-50837934313337359, -19034943355413, -66414220419547244, -1352304792, 0]], ![![321231025623594268, -2033455229723901, 419652976288068514, -2439835100605298, -3129797791], ![1410988605465819586, 528308015360060, 1843302831222223250, 37532733768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1511N1 : Ideal.span {2} * I1511N1 =  Ideal.span {B.equivFun.symm ![-343, -109, 14, 51, -175]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1511RS1
                    

def R1511RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-2, 2, 2, 2, -5] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-4, 4, 4, 4, -10], ![12, 24, 18, 20, -50]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1511RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1511N2) (Ideal.span {B.equivFun.symm ![-2, 2, 2, 2, -5]} * (J0 ^ 0*J1^ 1)) 
      ![![3022, 0, 0, 0, 0], ![-624, 2, 0, 0, 0]] ![![-4, 4, 4, 4, -10], ![12, 24, 18, 20, -50]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1511RS2]  
      rfl
    g := ![![![-176, -14, 37, 38, -122], ![123, 0, 0, 0, 0]], ![![47, 11, -3, -2, 10], ![-23, 0, 0, 0, 0]]]
    h := ![![![4279797189392, -95926773416, 27934405475686, -179065660024, -413527], ![20726838549862, 35468407050, 135285006214256, 4959042, 0]], ![![24655166344065, -552617437682, 160925245563604, -1031566085645, -2382257], ![119403707610272, 204327315158, 779353362828928, 28568177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1511N2 : Ideal.span {2} * I1511N2 =  Ideal.span {B.equivFun.symm ![-2, 2, 2, 2, -5]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1511RS2
                    

def R1531RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-79, -52, -35, -48, 127] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-316, -208, -140, -192, 508], ![948, 552, 328, 424, -1104]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1531RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1531N1) (Ideal.span {B.equivFun.symm ![-79, -52, -35, -48, 127]} * (J0 ^ 1*J1^ 1)) 
      ![![6124, 0, 0, 0, 0], ![-1536, 4, 0, 0, 0]] ![![-316, -208, -140, -192, 508], ![948, 552, 328, 424, -1104]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1531RS1]  
      rfl
    g := ![![![-168732531, 163966390, 45381895, 96187026, -186962126], ![180112051, -33850708, 0, 0, 0]], ![![42305697, -41110634, -11378379, -24116512, 46876140], ![-45158418, 8487171, 0, 0, 0]]]
    h := ![![![612256043053127, -16409538836615, 6452734314337664, -33608304614036, 82921429], ![2441052048960729, 7929835043945, 25726938037489624, -1007561172, 0]], ![![-1725716698673565, 46252242847565, -18187801467577690, 94729015980678, -233723940], ![-6880396414245463, -22351186088428, -72514444048137286, 2839931364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1531N1 : Ideal.span {4} * I1531N1 =  Ideal.span {B.equivFun.symm ![-79, -52, -35, -48, 127]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1531RS1
                    

def R1531RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-1817, -885, -464, -582, 1497] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-7268, -3540, -1856, -2328, 5988], ![-5172, -3436, -2268, -3152, 8400]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1531RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1531N2) (Ideal.span {B.equivFun.symm ![-1817, -885, -464, -582, 1497]} * (J0 ^ 1*J1^ 1)) 
      ![![6124, 0, 0, 0, 0], ![-1192, 4, 0, 0, 0]] ![![-7268, -3540, -1856, -2328, 5988], ![-5172, -3436, -2268, -3152, 8400]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1531RS2]  
      rfl
    g := ![![![71746765, -70151790, -19678394, -41622667, 80768823], ![-79259511, 14990328, 0, 0, 0]], ![![-13880644, 13573805, 3808659, 8055530, -15631230], ![15344882, -2902539, 0, 0, 0]]]
    h := ![![![-19539598501235496, 509388327145481, -142675508769210387, 957550655497497, 1400392137], ![-100386327384663358, -179595984789578, -733007996053674432, -17015875875, 0]], ![![-15103269362334899, 393735271194485, -110282032674052630, 740145478278640, 1082442900], ![-77594314063835012, -138819972912209, -566583658740581664, -13152540300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1531N2 : Ideal.span {4} * I1531N2 =  Ideal.span {B.equivFun.symm ![-1817, -885, -464, -582, 1497]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1531RS2
                    

def R1543RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-751244, -413012, -240507, -317584, 832042] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-1502488, -826024, -481014, -635168, 1664084], ![3342474, 1946154, 1181564, 1589230, -4190126]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1543RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1543N1) (Ideal.span {B.equivFun.symm ![-751244, -413012, -240507, -317584, 832042]} * (J0 ^ 1*J1^ 0)) 
      ![![3086, 0, 0, 0, 0], ![642, 2, 0, 0, 0]] ![![-1502488, -826024, -481014, -635168, 1664084], ![3342474, 1946154, 1181564, 1589230, -4190126]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1543RS1]  
      rfl
    g := ![![![-102697, -198641, 95277, 88859, -148933], ![-109887, 0, 0, 0, 0]], ![![-18926, -42072, 19288, 18129, -30001], ![-22633, 0, 0, 0, 0]]]
    h := ![![![2707819573658980882, 19672299636740688, 3933288871696236713, 24506509193635790, 7805754934], ![-13016092214087119970, 4886249600109631, -18906758938305494577, -95589516120, 0]], ![![-6337126034709515364, -46039198254917400, -9205099022548330002, -57352727242513597, -18267854161], ![30461636972589262609, -11435318606123925, 44247598866924413793, 223708705360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1543N1 : Ideal.span {2} * I1543N1 =  Ideal.span {B.equivFun.symm ![-751244, -413012, -240507, -317584, 832042]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1543RS1
                    

def R1553RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-63, -163, -152, -235, 647] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-126, -326, -304, -470, 1294], ![-13036, -6554, -3544, -4516, 11682]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1553RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1553N1) (Ideal.span {B.equivFun.symm ![-63, -163, -152, -235, 647]} * (J0 ^ 0*J1^ 1)) 
      ![![3106, 0, 0, 0, 0], ![-596, 2, 0, 0, 0]] ![![-126, -326, -304, -470, 1294], ![-13036, -6554, -3544, -4516, 11682]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1553RS1]  
      rfl
    g := ![![![1829, 313, -882, -472, 1171], ![321, 0, 0, 0, 0]], ![![-344, -51, 174, 95, -238], ![-59, 0, 0, 0, 0]]]
    h := ![![![-5868566688765169, 50852848338977, -9995652695315005, 67084861389911, 39571207], ![-30583503607276073, -12417704610677, -52091479978294797, -487730824, 0]], ![![-181675387704439502, 1574270418606130, -309439114362862374, 2076770845127428, 1225020465], ![-946784823259991576, -384419470595076, -1612615195993095519, -15098863304, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1553N1 : Ideal.span {2} * I1553N1 =  Ideal.span {B.equivFun.symm ![-63, -163, -152, -235, 647]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1553RS1
                    

def R1559RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![174, -167, -61, -76, 187] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![348, -334, -122, -152, 374], ![604, -512, -262, -256, 666]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1559RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1559N2) (Ideal.span {B.equivFun.symm ![174, -167, -61, -76, 187]} * (J0 ^ 0*J1^ 1)) 
      ![![3118, 0, 0, 0, 0], ![1150, 2, 0, 0, 0]] ![![348, -334, -122, -152, 374], ![604, -512, -262, -256, 666]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1559RS2]  
      rfl
    g := ![![![102710, -7132, -14482, -19635, 55717], ![-48235, 0, 0, 0, 0]], ![![38069, -2627, -5362, -7276, 20650], ![-17848, 0, 0, 0, 0]]]
    h := ![![![276682992711706, 835864798879, 267885211670797, 931818870668, 10468781], ![-750171797729728, 301510229344, -726318872723040, -129530392, 0]], ![![501169381814493, 1514042625515, 485233532480357, 1687848908964, 18962613], ![-1358822717790302, 546140163037, -1315616752863744, -234624709, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1559N2 : Ideal.span {2} * I1559N2 =  Ideal.span {B.equivFun.symm ![174, -167, -61, -76, 187]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1559RS2
                    

def R1567RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![10, 0, 4, 5, -11] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![40, 0, 16, 20, -44], ![0, -84, -80, -92, 216]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1567RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1567N1) (Ideal.span {B.equivFun.symm ![10, 0, 4, 5, -11]} * (J0 ^ 1*J1^ 1)) 
      ![![6268, 0, 0, 0, 0], ![1804, 4, 0, 0, 0]] ![![40, 0, 16, 20, -44], ![0, -84, -80, -92, 216]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1567RS1]  
      rfl
    g := ![![![-19101997, 18563615, 5139736, 10892747, -21171922], ![20402947, -3835710, 0, 0, 0]], ![![-5555812, 5399222, 1494890, 3168152, -6157846], ![5934195, -1115615, 0, 0, 0]]]
    h := ![![![-790463371495992, -2535899514535, -417022948631043, -1849328126225, -321401], ![2746465860475084, -491482990859, 1448947787476090, 3997106, 0]], ![![3484250413482096, 11177885338990, 1838178002392679, 8151576051131, 1416690], ![-12106031923862892, 2166387309721, -6386756312325950, -17618676, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1567N1 : Ideal.span {4} * I1567N1 =  Ideal.span {B.equivFun.symm ![10, 0, 4, 5, -11]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1567RS1
                    

def R1579RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![65697, 35150, 20038, 26201, -68408] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![131394, 70300, 40076, 52402, -136816], ![-347528, -195342, -115658, -153868, 404166]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1579RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1579N1) (Ideal.span {B.equivFun.symm ![65697, 35150, 20038, 26201, -68408]} * (J0 ^ 1*J1^ 0)) 
      ![![3158, 0, 0, 0, 0], ![618, 2, 0, 0, 0]] ![![131394, 70300, 40076, 52402, -136816], ![-347528, -195342, -115658, -153868, 404166]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1579RS1]  
      rfl
    g := ![![![-310478, 79158, 73879, 51300, -134383], ![-36047, 0, 0, 0, 0]], ![![-60425, 15158, 14457, 10063, -26269], ![-7123, 0, 0, 0, 0]]]
    h := ![![![-1565207803973545254, -12488155034835678, -2476277830346969101, -16027712431468567, -5770460144], ![7998262528768669627, -3020486417260170, 12653869636146126375, 72313940468, 0]], ![![4224786525841706294, 33707849519945941, 6683933714953350457, 43261772237915320, 15575543529], ![-21588795862058974430, 8152853751897515, -34155144002484890775, -195188754208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1579N1 : Ideal.span {2} * I1579N1 =  Ideal.span {B.equivFun.symm ![65697, 35150, 20038, 26201, -68408]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1579RS1
                    

def R1579RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![75016, -91406, -22565, -41262, 93668] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![150032, -182812, -45130, -82524, 187336], ![932530, -1136266, -280504, -512926, 1164382]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1579RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1579N2) (Ideal.span {B.equivFun.symm ![75016, -91406, -22565, -41262, 93668]} * (J0 ^ 1*J1^ 0)) 
      ![![3158, 0, 0, 0, 0], ![778, 2, 0, 0, 0]] ![![150032, -182812, -45130, -82524, 187336], ![932530, -1136266, -280504, -512926, 1164382]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1579RS2]  
      rfl
    g := ![![![-1464, -1005, 300, 477, -1621], ![-1281, 0, 0, 0, 0]], ![![-359, -252, 73, 117, -399], ![-319, 0, 0, 0, 0]]]
    h := ![![![-8240249001646120, -104901777934141, -36769548469482394, -189053911483542, -2699862058], ![33448207367839339, -43851611319831, 149252345172538403, 33833986375, 0]], ![![-51220566988124552, -652059002435610, -228555850694294028, -1175140282238363, -16782073621], ![207910725243235982, -272577247939163, 927737710658597232, 210308689125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1579N2 : Ideal.span {2} * I1579N2 =  Ideal.span {B.equivFun.symm ![75016, -91406, -22565, -41262, 93668]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1579RS2
                    

def R1579RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![128, -163, -38, -74, 166] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![256, -326, -76, -148, 332], ![1754, -2116, -502, -938, 2126]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1579RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1579N3) (Ideal.span {B.equivFun.symm ![128, -163, -38, -74, 166]} * (J0 ^ 1*J1^ 0)) 
      ![![3158, 0, 0, 0, 0], ![1320, 2, 0, 0, 0]] ![![256, -326, -76, -148, 332], ![1754, -2116, -502, -938, 2126]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1579RS3]  
      rfl
    g := ![![![-16721, 13326, 1256, 1567, 1839], ![22769, 0, 0, 0, 0]], ![![-7023, 5600, 530, 662, 762], ![9564, 0, 0, 0, 0]]]
    h := ![![![1758411924583742, 4063063566347, 1314037410454254, 3981939829460, 1150894], ![-4206867316214224, 1416706119706, -3143737103643512, -14422710, 0]], ![![11361329925199063, 26251986263447, 8490167943855107, 25727835163197, 7436077], ![-27181121137108355, 9153523924136, -20312097485896676, -93187020, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1579N3 : Ideal.span {2} * I1579N3 =  Ideal.span {B.equivFun.symm ![128, -163, -38, -74, 166]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1579RS3
                    

def R1579RS4 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-596, -121, -142, -176, 496] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-1192, -242, -284, -352, 992], ![-1662, 2348, 786, 1366, -3314]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1579RS4 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1579N4) (Ideal.span {B.equivFun.symm ![-596, -121, -142, -176, 496]} * (J0 ^ 1*J1^ 0)) 
      ![![3158, 0, 0, 0, 0], ![-62, 2, 0, 0, 0]] ![![-1192, -242, -284, -352, 992], ![-1662, 2348, 786, 1366, -3314]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1579RS4]  
      rfl
    g := ![![![13661, 34628, -15322, -14383, 23597], ![18129, 0, 0, 0, 0]], ![![-662, -558, 390, 343, -629], ![-393, 0, 0, 0, 0]]]
    h := ![![![-376702446899636, 217270107043757, -6363574046991706, 410553345559888, 220335568], ![-19187522744269848, -8058386039264, -324131979528296080, -2761189376, 0]], ![![174556084119847, -100678451663922, 2948747947093059, -190241887020111, -102098923], ![8891099226367924, 3734088598608, 150196022260966136, 1279477760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1579N4 : Ideal.span {2} * I1579N4 =  Ideal.span {B.equivFun.symm ![-596, -121, -142, -176, 496]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1579RS4
                    

def R1583RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-1232, -690, -399, -528, 1382] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-2464, -1380, -798, -1056, 2764], ![5590, 3098, 1920, 2570, -6794]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1583RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1583N1) (Ideal.span {B.equivFun.symm ![-1232, -690, -399, -528, 1382]} * (J0 ^ 1*J1^ 0)) 
      ![![3166, 0, 0, 0, 0], ![-1124, 2, 0, 0, 0]] ![![-2464, -1380, -798, -1056, 2764], ![5590, 3098, 1920, 2570, -6794]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1583RS1]  
      rfl
    g := ![![![43348, -10683, -10432, -7275, 18927], ![5189, 0, 0, 0, 0]], ![![-15436, 3843, 3706, 2582, -6730], ![-1832, 0, 0, 0, 0]]]
    h := ![![![-5456612441465791, 36649633871460, -19511839532218257, 69434277625225, 600666664], ![-15369782220707133, -21908233599481, -54959543733682909, -7546470855, 0]], ![![12463653796016802, -83712807757694, 44567726856519755, -158597446159346, -1372005329], ![35106697896178408, 50041420717928, 125535161830190729, 17237178035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1583N1 : Ideal.span {2} * I1583N1 =  Ideal.span {B.equivFun.symm ![-1232, -690, -399, -528, 1382]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1583RS1
                    

def R1613RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-1029, -8735, -10022, -10997, 25975] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-2058, -17470, -20044, -21994, 51950], ![-17564, -44302, -55924, -62436, 146058]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1613RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1613N1) (Ideal.span {B.equivFun.symm ![-1029, -8735, -10022, -10997, 25975]} * (J0 ^ 0*J1^ 1)) 
      ![![3226, 0, 0, 0, 0], ![298, 2, 0, 0, 0]] ![![-2058, -17470, -20044, -21994, 51950], ![-17564, -44302, -55924, -62436, 146058]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1613RS1]  
      rfl
    g := ![![![-11865999, 4035412, 2323188, 1553887, -3690246], ![12688447, 0, 0, 0, 0]], ![![-1119935, 379323, 218956, 147008, -349630], ![1194126, 0, 0, 0, 0]]]
    h := ![![![10789005482761852, 318054156049026, 37230802828095642, 499743328572545, 802935473], ![-116796414023571430, 45750547834183, -403042490830193940, -10278848349, 0]], ![![33544665145984171, 988878926820722, 115756249825466546, 1553778301745332, 2496448959], ![-363137881886542590, 142245437716677, -1253120634390698930, -31958508713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1613N1 : Ideal.span {2} * I1613N1 =  Ideal.span {B.equivFun.symm ![-1029, -8735, -10022, -10997, 25975]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1613RS1
                    

def R1613RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-4312, -2441, -1453, -1938, 5095] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-8624, -4882, -2906, -3876, 10190], ![5420, 4444, 3238, 4664, -12574]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1613RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1613N2) (Ideal.span {B.equivFun.symm ![-4312, -2441, -1453, -1938, 5095]} * (J0 ^ 0*J1^ 1)) 
      ![![3226, 0, 0, 0, 0], ![608, 2, 0, 0, 0]] ![![-8624, -4882, -2906, -3876, 10190], ![5420, 4444, 3238, 4664, -12574]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1613RS2]  
      rfl
    g := ![![![-25159380, 14236496, 1570010, 4851659, -9601807], ![-1711737, 0, 0, 0, 0]], ![![-4671485, 2643380, 291516, 900840, -1782834], ![-317827, 0, 0, 0, 0]]]
    h := ![![![7665911421273614, 62095872584322, 12030735117129556, 79153212668050, 1781628431], ![-40674719672366006, 14298228628669, -63834180846293257, -22807671858, 0]], ![![-6498903975242333, -52642809314041, -10199255897353380, -67103453217057, -1510405153], ![34482670467210971, -12121561253568, 54116489068260446, 19335583377, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1613N2 : Ideal.span {2} * I1613N2 =  Ideal.span {B.equivFun.symm ![-4312, -2441, -1453, -1938, 5095]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1613RS2
                    

def R1613RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-3951, -2355, -1452, -1966, 5195] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-15804, -9420, -5808, -7864, 20780], ![28452, 14964, 8428, 10952, -28536]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1613RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1613N3) (Ideal.span {B.equivFun.symm ![-3951, -2355, -1452, -1966, 5195]} * (J0 ^ 1*J1^ 1)) 
      ![![6452, 0, 0, 0, 0], ![1396, 4, 0, 0, 0]] ![![-15804, -9420, -5808, -7864, 20780], ![28452, 14964, 8428, 10952, -28536]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1613RS3]  
      rfl
    g := ![![![-90179986, 87661176, 24262531, 51436527, -99970547], ![96365967, -18115812, 0, 0, 0]], ![![-19590458, 19043257, 5270722, 11173897, -21717283], ![20934187, -3935415, 0, 0, 0]]]
    h := ![![![381546540269050616, 6479357738768622, 2064386673382659442, 11830313838801730, 3814690339], ![-1763422833012800221, 2445146752740970, -9541140834713983290, -48834091362, 0]], ![![-644557594930060064, -10945766243477534, -3487428055992990823, -19985290994460770, -6444266610], ![2979001144368866095, -4130657059781988, 16118124895003222020, 82496841546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1613N3 : Ideal.span {4} * I1613N3 =  Ideal.span {B.equivFun.symm ![-3951, -2355, -1452, -1966, 5195]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1613RS3
                    

def R1619RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-8, -6, -5, -8, 22] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-16, -12, -10, -16, 44], ![-186, -82, -36, -42, 106]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1619RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1619N2) (Ideal.span {B.equivFun.symm ![-8, -6, -5, -8, 22]} * (J0 ^ 1*J1^ 0)) 
      ![![3238, 0, 0, 0, 0], ![-216, 2, 0, 0, 0]] ![![-16, -12, -10, -16, 44], ![-186, -82, -36, -42, 106]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1619RS2]  
      rfl
    g := ![![![13406, -6815, -680, -2231, 4455], ![1301, 0, 0, 0, 0]], ![![-930, 475, 48, 156, -312], ![-90, 0, 0, 0, 0]]]
    h := ![![![1210917555851, -9039930024205, 983817574515405, -18218863393667, 4401968], ![18152543282369, 1209955684545, 14748165420510730, -56561795, 0]], ![![9485450551251, -70812260358958, 7706513882862034, -142713372184289, 34481827], ![142193868486239, 9477915938946, 115526439559585190, -443064110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1619N2 : Ideal.span {2} * I1619N2 =  Ideal.span {B.equivFun.symm ![-8, -6, -5, -8, 22]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1619RS2
                    

def R1621RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![153, 88, 53, 71, -187] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![306, 176, 106, 142, -374], ![-52, -86, -76, -116, 318]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1621RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1621N1) (Ideal.span {B.equivFun.symm ![153, 88, 53, 71, -187]} * (J0 ^ 0*J1^ 1)) 
      ![![3242, 0, 0, 0, 0], ![1276, 2, 0, 0, 0]] ![![306, 176, 106, 142, -374], ![-52, -86, -76, -116, 318]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1621RS1]  
      rfl
    g := ![![![-275, -91, 153, 87, -202], ![-57, 0, 0, 0, 0]], ![![-100, -31, 63, 38, -89], ![-21, 0, 0, 0, 0]]]
    h := ![![![-623198182621565, -1563079999999, -511097285483859, -1602195960965, -1943791], ![1583392247107291, -545784174636, 1298572486800624, 25007024, 0]], ![![179470540451442, 450140613115, 147187377311676, 461405349102, 559779], ![-455990197435366, 157176616366, -373966921777600, -7201600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1621N1 : Ideal.span {2} * I1621N1 =  Ideal.span {B.equivFun.symm ![153, 88, 53, 71, -187]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1621RS1
                    

def R1621RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-527, -415, -688, -789, 1813] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-1054, -830, -1376, -1578, 3626], ![-3888, -1894, -3716, -4380, 9934]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1621RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1621N2) (Ideal.span {B.equivFun.symm ![-527, -415, -688, -789, 1813]} * (J0 ^ 0*J1^ 1)) 
      ![![3242, 0, 0, 0, 0], ![1514, 2, 0, 0, 0]] ![![-1054, -830, -1376, -1578, 3626], ![-3888, -1894, -3716, -4380, 9934]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1621RS2]  
      rfl
    g := ![![![-913451, 162899, 148950, 152534, -410565], ![649339, 0, 0, 0, 0]], ![![-428239, 76277, 69810, 71528, -192550], ![304218, 0, 0, 0, 0]]]
    h := ![![![35876946346709757, 71786039385396, 28749577515952907, 75958000281995, 239327473], ![-76825006581019832, 29091801271919, -61562872353234582, -3078966920, 0]], ![![107324062386948453, 214744289970159, 86002900612250099, 227224499049866, 715935977], ![-229818104347536126, 87026645592329, -184162205147604363, -9210573125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1621N2 : Ideal.span {2} * I1621N2 =  Ideal.span {B.equivFun.symm ![-527, -415, -688, -789, 1813]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1621RS2
                    

def R1627RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-1, 2, 1, 1, -3] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-2, 4, 2, 2, -6], ![4, 18, 8, 8, -22]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1627RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1627N3) (Ideal.span {B.equivFun.symm ![-1, 2, 1, 1, -3]} * (J0 ^ 0*J1^ 1)) 
      ![![3254, 0, 0, 0, 0], ![-784, 2, 0, 0, 0]] ![![-2, 4, 2, 2, -6], ![4, 18, 8, 8, -22]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1627RS3]  
      rfl
    g := ![![![-119, 1, 39, 25, -74], ![151, 0, 0, 0, 0]], ![![34, 4, -7, -3, 10], ![-35, 0, 0, 0, 0]]]
    h := ![![![-1529364852780, 35936522676, -14105233267245, 71966296404, -218667], ![-6347644319182, -16385398667, -58543956701462, 2823581, 0]], ![![-17987156720870, 422656410098, -165894384734314, 846409572770, -2571785], ![-74655876241646, -192711870778, -688546831724887, 33208684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1627N3 : Ideal.span {2} * I1627N3 =  Ideal.span {B.equivFun.symm ![-1, 2, 1, 1, -3]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1627RS3
                    

def R1637RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-37, -7, -15, -21, 50] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-74, -14, -30, -42, 100], ![-252, 44, 32, 24, -70]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1637RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1637N1) (Ideal.span {B.equivFun.symm ![-37, -7, -15, -21, 50]} * (J0 ^ 1*J1^ 0)) 
      ![![3274, 0, 0, 0, 0], ![1554, 2, 0, 0, 0]] ![![-74, -14, -30, -42, 100], ![-252, 44, 32, 24, -70]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1637RS1]  
      rfl
    g := ![![![-2892335, 1470243, 148237, 481106, -962133], ![-282755, 0, 0, 0, 0]], ![![-1364883, 693804, 69953, 227033, -454029], ![-133431, 0, 0, 0, 0]]]
    h := ![![![-29970045222191, -111184519842, -89242810980020, -229709005559, 409450], ![63141523949190, -88998184562, 188018752064831, -5319600, 0]], ![![27693141533358, 102737536938, 82462798449640, 212257404484, -378343], ![-58344495191556, 82236758284, -173734469880676, 4915456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1637N1 : Ideal.span {2} * I1637N1 =  Ideal.span {B.equivFun.symm ![-37, -7, -15, -21, 50]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1637RS1
                    

def R1637RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![6, 4, 0, 0, -1] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![12, 8, 0, 0, -2], ![-136, -60, -46, -60, 150]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1637RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1637N2) (Ideal.span {B.equivFun.symm ![6, 4, 0, 0, -1]} * (J0 ^ 0*J1^ 1)) 
      ![![3274, 0, 0, 0, 0], ![-1040, 2, 0, 0, 0]] ![![12, 8, 0, 0, -2], ![-136, -60, -46, -60, 150]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1637RS2]  
      rfl
    g := ![![![7864, -4414, -487, -1510, 2996], ![529, 0, 0, 0, 0]], ![![-2507, 1423, 161, 490, -976], ![-167, 0, 0, 0, 0]]]
    h := ![![![-838794090242, 45365341118, -27857369764111, 107146073984, -501101], ![-2640588130906, -30913814037, -87697202854976, 6510336, 0]], ![![8011776501916, -433308929667, 266080821202878, -1023410163836, 4786287], ![25221686924770, 295274591467, 837643465640839, -62183744, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1637N2 : Ideal.span {2} * I1637N2 =  Ideal.span {B.equivFun.symm ![6, 4, 0, 0, -1]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1637RS2
                    

def R1637RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-877, -407, -205, -251, 640] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-1754, -814, -410, -502, 1280], ![8048, 4184, 2312, 2984, -7750]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1637RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1637N3) (Ideal.span {B.equivFun.symm ![-877, -407, -205, -251, 640]} * (J0 ^ 1*J1^ 0)) 
      ![![3274, 0, 0, 0, 0], ![-742, 2, 0, 0, 0]] ![![-1754, -814, -410, -502, 1280], ![8048, 4184, 2312, 2984, -7750]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1637RS3]  
      rfl
    g := ![![![-23152, 6187, 5424, 3742, -9903], ![-2567, 0, 0, 0, 0]], ![![5270, -1424, -1228, -845, 2243], ![577, 0, 0, 0, 0]]]
    h := ![![![36754558602841991, -218412369341886, 49072333913394728, -264540435286483, -189849880], ![162175774851348964, 57038868741369, 216526866722284910, 2466541700, 0]], ![![-171196322838298842, 1017326718511617, -228570371633196209, 1232183203516516, 884287625], ![-755386470777967718, -265677101246311, -1008544376198398600, -11488721000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1637N3 : Ideal.span {2} * I1637N3 =  Ideal.span {B.equivFun.symm ![-877, -407, -205, -251, 640]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1637RS3
                    

def R1699RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![6914, -8408, -2080, -3794, 8617] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![13828, -16816, -4160, -7588, 17234], ![6620, -7980, -2002, -3600, 8198]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1699RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1699N1) (Ideal.span {B.equivFun.symm ![6914, -8408, -2080, -3794, 8617]} * (J0 ^ 0*J1^ 1)) 
      ![![3398, 0, 0, 0, 0], ![976, 2, 0, 0, 0]] ![![13828, -16816, -4160, -7588, 17234], ![6620, -7980, -2002, -3600, 8198]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1699RS1]  
      rfl
    g := ![![![-221714, -30081, 22069, 52533, -159255], ![3329, 0, 0, 0, 0]], ![![-63991, -8725, 6361, 15172, -46002], ![865, 0, 0, 0, 0]]]
    h := ![![![-1518863607742396826, -5668485178253298, -1471651950555149963, -6031369210498214, -1411514237], ![5288010797682042326, -1600199043271871, 5123643985599585216, 19033037280, 0]], ![![-725948662118153126, -2709281603965734, -703383608089110965, -2882723890929144, -674640479], ![2527431919676819868, -764823351263850, 2448871957663371408, 9096937920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1699N1 : Ideal.span {2} * I1699N1 =  Ideal.span {B.equivFun.symm ![6914, -8408, -2080, -3794, 8617]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1699RS1
                    

def R1699RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-50, -28, -16, -21, 55] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-200, -112, -64, -84, 220], ![120, 52, 24, 28, -72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1699RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1699N2) (Ideal.span {B.equivFun.symm ![-50, -28, -16, -21, 55]} * (J0 ^ 1*J1^ 1)) 
      ![![6796, 0, 0, 0, 0], ![-1636, 4, 0, 0, 0]] ![![-200, -112, -64, -84, 220], ![120, 52, 24, 28, -72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1699RS2]  
      rfl
    g := ![![![-195604051, 190105252, 52632432, 111549378, -216814267], ![208958863, -39277990, 0, 0, 0]], ![![47039725, -45717353, -12657281, -26825889, 52140457], ![-50251351, 9445745, 0, 0, 0]]]
    h := ![![![404081229349062, -1459019689568, 215440014764848, -1053661617303, 45051745], ![1678567236067982, 231494205474, 894945822705388, -607483450, 0]], ![![-204845210623280, 739636424435, -109215306216488, 534143930077, -22838562], ![-850934005451300, -117353827984, -453684438244308, 307958070, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1699N2 : Ideal.span {4} * I1699N2 =  Ideal.span {B.equivFun.symm ![-50, -28, -16, -21, 55]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1699RS2
                    

def R1723RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-2381, -262, 313, 693, -2071] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-4762, -524, 626, 1386, -4142], ![114916, 58934, 32432, 41692, -108194]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1723RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1723N1) (Ideal.span {B.equivFun.symm ![-2381, -262, 313, 693, -2071]} * (J0 ^ 0*J1^ 1)) 
      ![![3446, 0, 0, 0, 0], ![742, 2, 0, 0, 0]] ![![-4762, -524, 626, 1386, -4142], ![114916, 58934, 32432, 41692, -108194]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1723RS1]  
      rfl
    g := ![![![-2877659, 1628493, 179571, 554839, -1098170], ![-195703, 0, 0, 0, 0]], ![![-612095, 346400, 38200, 118023, -233601], ![-41626, 0, 0, 0, 0]]]
    h := ![![![8949796954720, 211839724329, 76408570008741, 411924436911, 7135409], ![-41564686494276, 84677363547, -354857290574000, -97573903, 0]], ![![-877200898447564, -20763151615441, -7489070904383244, -40374153253478, -699367243], ![4073900281864350, -8299524138600, 34780802856827000, 9563569092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1723N1 : Ideal.span {2} * I1723N1 =  Ideal.span {B.equivFun.symm ![-2381, -262, 313, 693, -2071]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1723RS1
                    

def R1747RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-811, 499, 207, 155, -464] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-1622, 998, 414, 310, -928], ![-664, 1740, 1628, 1716, -4150]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1747RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1747N1) (Ideal.span {B.equivFun.symm ![-811, 499, 207, 155, -464]} * (J0 ^ 1*J1^ 0)) 
      ![![3494, 0, 0, 0, 0], ![828, 2, 0, 0, 0]] ![![-1622, 998, 414, 310, -928], ![-664, 1740, 1628, 1716, -4150]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1747RS1]  
      rfl
    g := ![![![-20617, 20191, 1487, 1434, 5327], ![33127, 0, 0, 0, 0]], ![![-4926, 4825, 358, 347, 1260], ![7914, 0, 0, 0, 0]]]
    h := ![![![-650683999073113, -3320370145726, -809759922410066, -3911996027161, -38135192], ![2745760720892550, -874564314125, 3417032562061221, 528747460, 0]], ![![-6160325815755536, -31435477066146, -7666371026056967, -37036672434234, -361043465], ![25995384359991490, -8279904139669, 32350624801129008, 5005896280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1747N1 : Ideal.span {2} * I1747N1 =  Ideal.span {B.equivFun.symm ![-811, 499, 207, 155, -464]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1747RS1
                    

def R1783RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![2085, -2537, -626, -1145, 2599] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![4170, -5074, -1252, -2290, 5198], ![1936, -2386, -592, -1080, 2454]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1783RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1783N1) (Ideal.span {B.equivFun.symm ![2085, -2537, -626, -1145, 2599]} * (J0 ^ 0*J1^ 1)) 
      ![![3566, 0, 0, 0, 0], ![100, 2, 0, 0, 0]] ![![4170, -5074, -1252, -2290, 5198], ![1936, -2386, -592, -1080, 2454]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1783RS1]  
      rfl
    g := ![![![21, -280, 144, 113, -60], ![-37, 0, 0, 0, 0]], ![![12, -4, 6, 6, -9], ![1, 0, 0, 0, 0]]]
    h := ![![![2012622873675, 12252426722916, 611567568589265, 24462717771695, -68929715], ![-71770424298267, 685485236233, -21808512405761568, 975410194, 0]], ![![913746676036, 5562698475855, 277656505003821, 11106267023040, -31294635], ![-32584339320604, 311215711273, -9901236829618464, 442843932, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1783N1 : Ideal.span {2} * I1783N1 =  Ideal.span {B.equivFun.symm ![2085, -2537, -626, -1145, 2599]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1783RS1
                    

def R1783RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![44319, 22972, 12752, 16465, -42794] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![88638, 45944, 25504, 32930, -85588], ![-277184, -151150, -87538, -115280, 301758]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1783RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1783N2) (Ideal.span {B.equivFun.symm ![44319, 22972, 12752, 16465, -42794]} * (J0 ^ 1*J1^ 0)) 
      ![![3566, 0, 0, 0, 0], ![934, 2, 0, 0, 0]] ![![88638, 45944, 25504, 32930, -85588], ![-277184, -151150, -87538, -115280, 301758]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1783RS2]  
      rfl
    g := ![![![-1407459, 603928, 257328, 154422, -495297], ![-56899, 0, 0, 0, 0]], ![![-369473, 157448, 67901, 40889, -130537], ![-15411, 0, 0, 0, 0]]]
    h := ![![![1191785605809951, 202882779139826, 107333501135672188, 459604510346509, -20630479382], ![-4550231507974182, 112695537353419, -409798144006417437, 291937656312, 0]], ![![-3849094769506706, -655247923966878, -346653639551916132, -1484378824694302, 66629996121], ![14695824661756298, -363971339529212, 1323519838618513125, -942867324864, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1783N2 : Ideal.span {2} * I1783N2 =  Ideal.span {B.equivFun.symm ![44319, 22972, 12752, 16465, -42794]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1783RS2
                    

def R1783RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![185012, 112154, 69952, 95159, -251855] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![740048, 448616, 279808, 380636, -1007420], ![-1508640, -801556, -454384, -592564, 1545672]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1783RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1783N3) (Ideal.span {B.equivFun.symm ![185012, 112154, 69952, 95159, -251855]} * (J0 ^ 1*J1^ 1)) 
      ![![7132, 0, 0, 0, 0], ![-3444, 4, 0, 0, 0]] ![![740048, 448616, 279808, 380636, -1007420], ![-1508640, -801556, -454384, -592564, 1545672]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1783RS3]  
      rfl
    g := ![![![35792964, -34959610, -9640557, -20640856, 39981937], ![-38903969, 7302656, 0, 0, 0]], ![![-17267919, 16865379, 4651167, 9958059, -19288959], ![18768863, -3522961, 0, 0, 0]]]
    h := ![![![90916003721212784, -129790238971892, 35311825272911886, -81959514507807, -9072801737], ![188273213194811100, 34812638566846, 73125451812264016, 128387343216, 0]], ![![-159149945792993274, 227199927948760, -61813925381155913, 143471465292701, 15882087198], ![-329575327201008902, -60940090839761, -128007294634357908, -224744135616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1783N3 : Ideal.span {4} * I1783N3 =  Ideal.span {B.equivFun.symm ![185012, 112154, 69952, 95159, -251855]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1783RS3
                    

def R1787RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![1571, 1137, 783, 1105, -2960] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![3142, 2274, 1566, 2210, -5920], ![8372, 2912, 956, 816, -1726]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1787RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1787N1) (Ideal.span {B.equivFun.symm ![1571, 1137, 783, 1105, -2960]} * (J0 ^ 1*J1^ 0)) 
      ![![3574, 0, 0, 0, 0], ![680, 2, 0, 0, 0]] ![![3142, 2274, 1566, 2210, -5920], ![8372, 2912, 956, 816, -1726]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1787RS1]  
      rfl
    g := ![![![-593626433, 301753297, 30424185, 98742376, -197468309], ![-58029889, 0, 0, 0, 0]], ![![-111448729, 56651831, 5711905, 18538113, -37073140], ![-10894658, 0, 0, 0, 0]]]
    h := ![![![-48143471856102007, -332838987094093, -69903557444003582, -411198853631857, -526447456], ![253036423808408410, -75463906049111, 367405096830768498, 7466361912, 0]], ![![-103729047156636682, -717128816365334, -150612931037015816, -885961556880216, -1134274093], ![545187667728254250, -162593156819242, 791604326517254304, 16086887328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1787N1 : Ideal.span {2} * I1787N1 =  Ideal.span {B.equivFun.symm ![1571, 1137, 783, 1105, -2960]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1787RS1
                    

def R1823RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![90, -37, 1, 7, -7] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![360, -148, 4, 28, -28], ![-408, -256, -364, -476, 1056]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1823RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1823N1) (Ideal.span {B.equivFun.symm ![90, -37, 1, 7, -7]} * (J0 ^ 1*J1^ 1)) 
      ![![7292, 0, 0, 0, 0], ![924, 4, 0, 0, 0]] ![![360, -148, 4, 28, -28], ![-408, -256, -364, -476, 1056]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1823RS1]  
      rfl
    g := ![![![236612762, -229928598, -63663096, -134918325, 262238464], ![-252693557, 47511414, 0, 0, 0]], ![![29994204, -29146828, -8070242, -17102884, 33242592], ![-32032559, 6022779, 0, 0, 0]]]
    h := ![![![-10538847714246, -1150237723454, -263493765647306, -2281334888041, -1559705], ![83170212314188, -284502087938, 2079434719490655, 22566208, 0]], ![![31809499807422, 3471772970160, 795305626677411, 6885773818357, 4707672], ![-251033407477288, 858715239919, -6276376705371185, -68111792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1823N1 : Ideal.span {4} * I1823N1 =  Ideal.span {B.equivFun.symm ![90, -37, 1, 7, -7]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1823RS1
                    

def R1831RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![9267, -11293, -2788, -5098, 11573] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![37068, -45172, -11152, -20392, 46292], ![213060, -259596, -64084, -117184, 266016]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1831RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1831N1) (Ideal.span {B.equivFun.symm ![9267, -11293, -2788, -5098, 11573]} * (J0 ^ 1*J1^ 1)) 
      ![![7324, 0, 0, 0, 0], ![956, 4, 0, 0, 0]] ![![37068, -45172, -11152, -20392, 46292], ![213060, -259596, -64084, -117184, 266016]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1831RS1]  
      rfl
    g := ![![![-56020250, 54446340, 15073949, 31947613, -62095375], ![59846641, -11248896, 0, 0, 0]], ![![-7367245, 7160260, 1982381, 4201444, -8166188], ![7870459, -1479347, 0, 0, 0]]]
    h := ![![![759028985281096236, 6361508197018748, 787762857921136454, 6592162764368566, 729948881], ![-5814987748496132736, 845981217219355, -6035124013680848400, -10607431663, 0]], ![![4359896316918139766, 36540786578730939, 4524944961862434222, 37865676692506492, 4192858902], ![-33401548767209918224, 4859353812114402, -34666021284611050872, -60929560183, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1831N1 : Ideal.span {4} * I1831N1 =  Ideal.span {B.equivFun.symm ![9267, -11293, -2788, -5098, 11573]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1831RS1
                    

def R1831RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![23, -27, -10, -14, 33] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![92, -108, -40, -56, 132], ![276, -388, -76, -176, 384]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1831RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1831N2) (Ideal.span {B.equivFun.symm ![23, -27, -10, -14, 33]} * (J0 ^ 1*J1^ 1)) 
      ![![7324, 0, 0, 0, 0], ![2172, 4, 0, 0, 0]] ![![92, -108, -40, -56, 132], ![276, -388, -76, -176, 384]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1831RS2]  
      rfl
    g := ![![![187024112, -181768676, -50324015, -106657957, 207307107], ![-199799807, 37554908, 0, 0, 0]], ![![55509105, -53949289, -14936263, -31656285, 61529145], ![-59300969, 11146367, 0, 0, 0]]]
    h := ![![![34607595978451790, 91420055028683, 17932247023341861, 66048880355474, 13354323], ![-116697068570228919, 18001172108051, -60467702226275474, -194061630, 0]], ![![118798042759413240, 313819070620669, 61556308331214482, 226727037543082, 45841596], ![-400587875290042847, 61792908560268, -207568438995717813, -666158430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1831N2 : Ideal.span {4} * I1831N2 =  Ideal.span {B.equivFun.symm ![23, -27, -10, -14, 33]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1831RS2
                    

def R1847RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-83, 94, 22, 41, -92] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-166, 188, 44, 82, -184], ![-1008, 1194, 294, 540, -1226]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1847RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1847N1) (Ideal.span {B.equivFun.symm ![-83, 94, 22, 41, -92]} * (J0 ^ 1*J1^ 0)) 
      ![![3694, 0, 0, 0, 0], ![-1338, 2, 0, 0, 0]] ![![-166, 188, 44, 82, -184], ![-1008, 1194, 294, 540, -1226]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1847RS1]  
      rfl
    g := ![![![154, -562, 143, 140, -191], ![-291, 0, 0, 0, 0]], ![![-47, 206, -51, -49, 65], ![107, 0, 0, 0, 0]]]
    h := ![![![-638963699494768, 17611164903602, -14508190336258355, 43372830164991, -7236676], ![-1764074665733377, -13887938688805, -40054770468396368, 106080480, 0]], ![![-4783616224726770, 131846385378702, -108615895924699680, 324711676506396, -54177539], ![-13206784985288094, -103972367913372, -299870947351045371, 794173920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1847N1 : Ideal.span {2} * I1847N1 =  Ideal.span {B.equivFun.symm ![-83, 94, 22, 41, -92]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1847RS1
                    

def R1861RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-197, 218, 64, 99, -232] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-394, 436, 128, 198, -464], ![-1856, 2354, 654, 1128, -2570]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1861RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1861N1) (Ideal.span {B.equivFun.symm ![-197, 218, 64, 99, -232]} * (J0 ^ 1*J1^ 0)) 
      ![![3722, 0, 0, 0, 0], ![278, 2, 0, 0, 0]] ![![-394, 436, 128, 198, -464], ![-1856, 2354, 654, 1128, -2570]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1861RS1]  
      rfl
    g := ![![![67232, 2996, -5779, -13904, 39465], ![-10451, 0, 0, 0, 0]], ![![5105, 248, -437, -1055, 3003], ![-767, 0, 0, 0, 0]]]
    h := ![![![2954448719456, 1127662371106, 155515551766151, 2237628429871, -9520300], ![-39555619971997, 166224685303, -2082119440980908, 140613318, 0]], ![![26312535095266, 10043043076279, 1385032812499423, 19928481507828, -84788497], ![-352285227316406, 1480409129756, -18543507144789480, 1252312632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1861N1 : Ideal.span {2} * I1861N1 =  Ideal.span {B.equivFun.symm ![-197, 218, 64, 99, -232]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1861RS1
                    

def R1861RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![67, -86, -47, -55, 133] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![134, -172, -94, -110, 266], ![204, -306, -232, -244, 598]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1861RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1861N2) (Ideal.span {B.equivFun.symm ![67, -86, -47, -55, 133]} * (J0 ^ 0*J1^ 1)) 
      ![![3722, 0, 0, 0, 0], ![-608, 2, 0, 0, 0]] ![![134, -172, -94, -110, 266], ![204, -306, -232, -244, 598]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1861RS2]  
      rfl
    g := ![![![-12435, -12598, -967, 5382, -18287], ![-23995, 0, 0, 0, 0]], ![![2034, 2040, 157, -869, 2954], ![3871, 0, 0, 0, 0]]]
    h := ![![![-77625322871791, 2271505333288, -646524623383605, 4253435250611, 6600853], ![-475199760943442, -676843147844, -3957838805798688, -97493550, 0]], ![![-149828053380447, 4384332454297, -1247885640889995, 8209742648183, 12740597], ![-917203980801516, -1306404758134, -7639198935479600, -188176593, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1861N2 : Ideal.span {2} * I1861N2 =  Ideal.span {B.equivFun.symm ![67, -86, -47, -55, 133]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1861RS2
                    

def R1879RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-14665, -9273, -5951, -8185, 21746] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-29330, -18546, -11902, -16370, 43492], ![-5040, 6196, 7436, 12172, -33994]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1879RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1879N2) (Ideal.span {B.equivFun.symm ![-14665, -9273, -5951, -8185, 21746]} * (J0 ^ 1*J1^ 0)) 
      ![![3758, 0, 0, 0, 0], ![-772, 2, 0, 0, 0]] ![![-29330, -18546, -11902, -16370, 43492], ![-5040, 6196, 7436, 12172, -33994]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1879RS2]  
      rfl
    g := ![![![854125, 59119, -291027, -229208, 498223], ![219321, 0, 0, 0, 0]], ![![-178552, -10727, 60328, 47403, -103410], ![-45142, 0, 0, 0, 0]]]
    h := ![![![437425725057259625, -20367977593550477, 8078863190882570330, -41859445277617911, 7998528950], ![2129334030034704930, 8250868541573563, 39326922775718541118, -119279649804, 0]], ![![-16603789991999388, 773126963387550, -306657199405190578, 1588899323357254, -303607883], ![-80825184785110512, -313186172340840, -1492769925010770880, 4527612660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1879N2 : Ideal.span {2} * I1879N2 =  Ideal.span {B.equivFun.symm ![-14665, -9273, -5951, -8185, 21746]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1879RS2
                    

def R1889RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-2861, 3512, 871, 1590, -3613] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-11444, 14048, 3484, 6360, -14452], ![-66300, 80400, 19808, 36256, -82272]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1889RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1889N1) (Ideal.span {B.equivFun.symm ![-2861, 3512, 871, 1590, -3613]} * (J0 ^ 1*J1^ 1)) 
      ![![7556, 0, 0, 0, 0], ![2252, 4, 0, 0, 0]] ![![-11444, 14048, 3484, 6360, -14452], ![-66300, 80400, 19808, 36256, -82272]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1889RS1]  
      rfl
    g := ![![![-254184069, 247047590, 68393111, 144960458, -281751968], ![271552435, -51044958, 0, 0, 0]], ![![-75773670, 73646239, 20388360, 43213495, -83991791], ![80951235, -15216777, 0, 0, 0]]]
    h := ![![![-41564677623242, -1370270568853, -874138627732579, -3099365721506, 1457468923], ![139460042250979, -862332351294, 2932944643428172, -21850466660, 0]], ![![-241986050428090, -7977599777970, -5089161426353143, -18044246044776, 8485261248], ![811924613556445, -5020426280413, 17075356552633704, -127211575540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1889N1 : Ideal.span {4} * I1889N1 =  Ideal.span {B.equivFun.symm ![-2861, 3512, 871, 1590, -3613]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1889RS1
                    

def R1889RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![4318115, -5261536, -1298890, -2375131, 5391734] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![8636230, -10523072, -2597780, -4750262, 10783468], ![53678496, -65406170, -16146502, -29525260, 67024658]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1889RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1889N2) (Ideal.span {B.equivFun.symm ![4318115, -5261536, -1298890, -2375131, 5391734]} * (J0 ^ 1*J1^ 0)) 
      ![![3778, 0, 0, 0, 0], ![1254, 2, 0, 0, 0]] ![![8636230, -10523072, -2597780, -4750262, 10783468], ![53678496, -65406170, -16146502, -29525260, 67024658]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1889RS2]  
      rfl
    g := ![![![493727, -207626, -39452, -71206, 99521], ![-405921, 0, 0, 0, 0]], ![![164668, -69196, -13156, -23751, 33221], ![-135313, 0, 0, 0, 0]]]
    h := ![![![718654910169301228, 5238240685909244, 3200864786123918993, 10210243749346903, 31401961852], ![-2165134159885332146, 3051840807270283, -9643439636572373577, -470780163069, 0]], ![![4466801652263439522, 32558299984707466, 19894984244888748176, 63461799264477376, 195178983821], ![-13457397571345420480, 18968725277535624, -59938826678296147427, -2926135451790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1889N2 : Ideal.span {2} * I1889N2 =  Ideal.span {B.equivFun.symm ![4318115, -5261536, -1298890, -2375131, 5391734]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1889RS2
                    

def R1901RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-8925, 10875, 2681, 4907, -11138] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-17850, 21750, 5362, 9814, -22276], ![-111044, 135276, 33384, 61052, -138594]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E1901RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1901N2) (Ideal.span {B.equivFun.symm ![-8925, 10875, 2681, 4907, -11138]} * (J0 ^ 1*J1^ 0)) 
      ![![3802, 0, 0, 0, 0], ![-78, 2, 0, 0, 0]] ![![-17850, 21750, 5362, 9814, -22276], ![-111044, 135276, 33384, 61052, -138594]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1901RS2]  
      rfl
    g := ![![![47361, -72513, -3093, 254, -34065], ![-114359, 0, 0, 0, 0]], ![![-846, 1364, 56, -11, 657], ![2139, 0, 0, 0, 0]]]
    h := ![![![7674608584794, -47051443988880, 1828869982222371, -93788241611773, -19821202], ![374088087318661, 1923313852064, 89145737109169070, 299048364, 0]], ![![47746175960470, -292721967390846, 11377980650809528, -583486419868666, -123313989], ![2327320728411048, 11965545939940, 554603925806547936, 1860474792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1901N2 : Ideal.span {2} * I1901N2 =  Ideal.span {B.equivFun.symm ![-8925, 10875, 2681, 4907, -11138]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1901RS2
                    

def R1913RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-22, 3, 5, 14, -45] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-44, 6, 10, 28, -90], ![2104, 1052, 538, 696, -1822]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1913RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1913N1) (Ideal.span {B.equivFun.symm ![-22, 3, 5, 14, -45]} * (J0 ^ 0*J1^ 1)) 
      ![![3826, 0, 0, 0, 0], ![1056, 2, 0, 0, 0]] ![![-44, 6, 10, 28, -90], ![2104, 1052, 538, 696, -1822]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1913RS1]  
      rfl
    g := ![![![40210490, -22753194, -2509224, -7754071, 15345887], ![2735759, 0, 0, 0, 0]], ![![11003663, -6226444, -686652, -2121912, 4199422], ![748645, 0, 0, 0, 0]]]
    h := ![![![63640184190415, 655574168620, 329092143886628, 1246563766237, 523413], ![-230575136812619, 319692316438, -1192336347108432, -7946739, 0]], ![![-9259112186492516, -95380534371731, -47880142374606879, -181364556143934, -76152199], ![33546745445866340, -46512546329020, 173474922201842469, 1156183776, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1913N1 : Ideal.span {2} * I1913N1 =  Ideal.span {B.equivFun.symm ![-22, 3, 5, 14, -45]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1913RS1
                    

def R1931RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![1981, 475, 1350, 1643, -3663] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![3962, 950, 2700, 3286, -7326], ![13568, 1110, 6900, 8696, -19022]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E1931RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I1931N1) (Ideal.span {B.equivFun.symm ![1981, 475, 1350, 1643, -3663]} * (J0 ^ 0*J1^ 1)) 
      ![![3862, 0, 0, 0, 0], ![-810, 2, 0, 0, 0]] ![![3962, 950, 2700, 3286, -7326], ![13568, 1110, 6900, 8696, -19022]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1931RS1]  
      rfl
    g := ![![![-300271, -45478, 28920, 72205, -219744], ![-6075, 0, 0, 0, 0]], ![![62623, 9435, -6038, -15040, 45764], ![1148, 0, 0, 0, 0]]]
    h := ![![![-7655721777196954, 42188497434779, -10300703997114239, 50866719843911, 270782451], ![-36501725466703823, -10242495322250, -49112764174763281, -4149848544, 0]], ![![-25082620687195036, 138223162924988, -33748437925343421, 166655826397790, 887170891], ![-119591458644240276, -33557727481546, -160909300331159367, -13596246032, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1931N1 : Ideal.span {2} * I1931N1 =  Ideal.span {B.equivFun.symm ![1981, 475, 1350, 1643, -3663]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1931RS1
                    

def R1987RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![32, -49, -13, -23, 53] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![128, -196, -52, -92, 212], ![888, -1056, -260, -476, 1080]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E1987RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I1987N1) (Ideal.span {B.equivFun.symm ![32, -49, -13, -23, 53]} * (J0 ^ 1*J1^ 1)) 
      ![![7948, 0, 0, 0, 0], ![-256, 4, 0, 0, 0]] ![![128, -196, -52, -92, 212], ![888, -1056, -260, -476, 1080]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R1987RS1]  
      rfl
    g := ![![![-44486558, 43236070, 11970302, 25369871, -49310504], ![47524049, -8932990, 0, 0, 0]], ![![1345679, -1307853, -362091, -767416, 1491599], ![-1437560, 270215, 0, 0, 0]]]
    h := ![![![55733600144318, -42054658791807, 2641238110611106, -82538726058099, -7223773], ![1730354143680096, 2655781861079, 82002230888992200, 113917754, 0]], ![![582223286966136, -439325678059640, 27591799748168976, -862244108819527, -75463434], ![18076213891443870, 27743731618121, 856639590539866750, 1190046378, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R1987N1 : Ideal.span {4} * I1987N1 =  Ideal.span {B.equivFun.symm ![32, -49, -13, -23, 53]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E1987RS1
                    

def R2003RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-6, 3, -3, -2, 5] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-12, 6, -6, -4, 10], ![-16, -16, -26, -28, 66]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E2003RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2003N1) (Ideal.span {B.equivFun.symm ![-6, 3, -3, -2, 5]} * (J0 ^ 0*J1^ 1)) 
      ![![4006, 0, 0, 0, 0], ![860, 2, 0, 0, 0]] ![![-12, 6, -6, -4, 10], ![-16, -16, -26, -28, 66]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2003RS1]  
      rfl
    g := ![![![1754, 492, -122, -469, 1471], ![537, 0, 0, 0, 0]], ![![379, 107, -26, -101, 317], ![117, 0, 0, 0, 0]]]
    h := ![![![3612415095318, 19168401704, 5076564988774, 23612234964, 97543], ![-16827133517820, 4837385661, -23647359473199, -1550624, 0]], ![![12788422697184, 67858653771, 17971705127401, 83590405148, 345315], ![-59570257163066, 17124976542, -83714750512155, -5489412, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2003N1 : Ideal.span {2} * I2003N1 =  Ideal.span {B.equivFun.symm ![-6, 3, -3, -2, 5]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2003RS1
                    

def R2017RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![1650, 931, 553, 737, -1937] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![6600, 3724, 2212, 2948, -7748], ![-7176, -3584, -1932, -2460, 6360]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2017RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2017N1) (Ideal.span {B.equivFun.symm ![1650, 931, 553, 737, -1937]} * (J0 ^ 1*J1^ 1)) 
      ![![8068, 0, 0, 0, 0], ![-760, 4, 0, 0, 0]] ![![6600, 3724, 2212, 2948, -7748], ![-7176, -3584, -1932, -2460, 6360]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2017RS1]  
      rfl
    g := ![![![199226918, -193726326, -53695806, -113783127, 221124724], ![-213449329, 40143880, 0, 0, 0]], ![![-18655586, 18140790, 5028316, 10655107, -20706916], ![19989104, -3759455, 0, 0, 0]]]
    h := ![![![-4343961595566085, 52225436286461, -5677105813718552, 59760891709922, -967823687], ![-46114580557178386, -5494486670566, -60266992399811870, 15492860117, 0]], ![![4377916513116818, -52633660516775, 5721481357768735, -60228017419673, 975388758], ![46475038803932654, 5537434759436, 60738074085403745, -15613961296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2017N1 : Ideal.span {4} * I2017N1 =  Ideal.span {B.equivFun.symm ![1650, 931, 553, 737, -1937]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2017RS1
                    

def R2027RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![300, -367, -91, -166, 377] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![600, -734, -182, -332, 754], ![284, -344, -86, -156, 354]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E2027RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2027N1) (Ideal.span {B.equivFun.symm ![300, -367, -91, -166, 377]} * (J0 ^ 0*J1^ 1)) 
      ![![4054, 0, 0, 0, 0], ![60, 2, 0, 0, 0]] ![![600, -734, -182, -332, 754], ![284, -344, -86, -156, 354]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2027RS1]  
      rfl
    g := ![![![736, -624, -206, -11, -67], ![-1391, 0, 0, 0, 0]], ![![21, -4, 0, 4, -12], ![-21, 0, 0, 0, 0]]]
    h := ![![![27903314220, 132500365781, 3948841409044, 263256167118, 378859], ![-1885330883380, 3895072585, -266810189369744, -6094816, 0]], ![![12809293196, 60825607028, 1812754812738, 120850354444, 173919], ![-865479844662, 1788071785, -122481863606836, -2797886, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2027N1 : Ideal.span {2} * I2027N1 =  Ideal.span {B.equivFun.symm ![300, -367, -91, -166, 377]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2027RS1
                    

def R2053RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![7, -23, -11, -17, 38] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![14, -46, -22, -34, 76], ![160, -228, -44, -104, 226]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2053RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2053N3) (Ideal.span {B.equivFun.symm ![7, -23, -11, -17, 38]} * (J0 ^ 1*J1^ 0)) 
      ![![4106, 0, 0, 0, 0], ![968, 2, 0, 0, 0]] ![![14, -46, -22, -34, 76], ![160, -228, -44, -104, 226]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2053RS3]  
      rfl
    g := ![![![174, -4897, 52, 628, -3973], ![-7059, 0, 0, 0, 0]], ![![50, -1159, 14, 151, -948], ![-1676, 0, 0, 0, 0]]]
    h := ![![![-800517777324, -19298351787, -9545082021533, -39442318350, 54416], ![3395584731706, -8809632893, 40487731742744, -886635, 0]], ![![19348288168248, 466435700608, 230701931551067, 953309673784, -1315219], ![-82070322171196, 212926340035, -978577019673682, 21429720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2053N3 : Ideal.span {2} * I2053N3 =  Ideal.span {B.equivFun.symm ![7, -23, -11, -17, 38]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2053RS3
                    

def R2063RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-512085, -243041, -124415, -154005, 394090] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-1024170, -486082, -248830, -308010, 788180], ![4472920, 2326060, 1295372, 1674972, -4355826]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2063RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2063N1) (Ideal.span {B.equivFun.symm ![-512085, -243041, -124415, -154005, 394090]} * (J0 ^ 1*J1^ 0)) 
      ![![4126, 0, 0, 0, 0], ![-476, 2, 0, 0, 0]] ![![-1024170, -486082, -248830, -308010, 788180], ![4472920, 2326060, 1295372, 1674972, -4355826]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2063RS1]  
      rfl
    g := ![![![-629777, 1489399, -271225, -319028, 344579], ![503853, 0, 0, 0, 0]], ![![62992, -169531, 33644, 38455, -44014], ![-59322, 0, 0, 0, 0]]]
    h := ![![![1108962927979974811, -14592253604768275, 2427615722118814906, -20400346204489713, 89116280090], ![9612565119899809106, 2317623277627713, 21042746269653721772, -1459102265330, 0]], ![![-5077536185775127774, 66812599268061412, -11115165677069488772, 93405733809701524, -408030895491], ![-44012424584217000694, -10611550449743632, -96347049064089724748, 6680696311270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2063N1 : Ideal.span {2} * I2063N1 =  Ideal.span {B.equivFun.symm ![-512085, -243041, -124415, -154005, 394090]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2063RS1
                    

def R2069RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![-325499, 396614, 97910, 179037, -406428] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![-650998, 793228, 195820, 358074, -812856], ![-4046284, 4930314, 1217122, 2225612, -5052314]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2069RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2069N2) (Ideal.span {B.equivFun.symm ![-325499, 396614, 97910, 179037, -406428]} * (J0 ^ 1*J1^ 0)) 
      ![![4138, 0, 0, 0, 0], ![-254, 2, 0, 0, 0]] ![![-650998, 793228, 195820, 358074, -812856], ![-4046284, 4930314, 1217122, 2225612, -5052314]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2069RS2]  
      rfl
    g := ![![![5095, 12642, -628, -2714, 13327], ![17263, 0, 0, 0, 0]], ![![-317, -752, 39, 165, -803], ![-1025, 0, 0, 0, 0]]]
    h := ![![![-238594121642610036, 82605074023092600, -10329796459847727659, 162674002194699887, 23642232360], ![-3887017665369030565, -9947891009422852, -168286289822038730685, -388220469518, 0]], ![![-1482984818738014678, 513432895511448586, -64204982189603457114, 1011102344002640964, 146948598019], ![-24159808080029841330, -61831243971444150, -1045985589626779240257, -2412989300218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2069N2 : Ideal.span {2} * I2069N2 =  Ideal.span {B.equivFun.symm ![-325499, 396614, 97910, 179037, -406428]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2069RS2
                    

def R2087RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![1301, -1584, -391, -715, 1623] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![2602, -3168, -782, -1430, 3246], ![1216, -1486, -368, -672, 1526]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E2087RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2087N1) (Ideal.span {B.equivFun.symm ![1301, -1584, -391, -715, 1623]} * (J0 ^ 0*J1^ 1)) 
      ![![4174, 0, 0, 0, 0], ![278, 2, 0, 0, 0]] ![![2602, -3168, -782, -1430, 3246], ![1216, -1486, -368, -672, 1526]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2087RS1]  
      rfl
    g := ![![![-403, 324, 159, 14, 113], ![1295, 0, 0, 0, 0]], ![![-19, 28, 14, 5, -3], ![90, 0, 0, 0, 0]]]
    h := ![![![62750106742305, 7211541704712, 948027401251257, 13640703195779, 21232833], ![-942154442416126, 904320840530, -14234058310442432, -351689848, 0]], ![![30281274082818, 3480068517326, 457488904277875, 6582584375072, 10246313], ![-454654794713092, 436397460165, -6868919327940208, -169714718, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2087N1 : Ideal.span {2} * I2087N1 =  Ideal.span {B.equivFun.symm ![1301, -1584, -391, -715, 1623]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2087RS1
                    

def R2087RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-8598, -9929, -8095, -12079, 32915] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-34392, -39716, -32380, -48316, 131660], ![504000, 282696, 167116, 222172, -583440]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2087RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2087N2) (Ideal.span {B.equivFun.symm ![-8598, -9929, -8095, -12079, 32915]} * (J0 ^ 1*J1^ 1)) 
      ![![8348, 0, 0, 0, 0], ![-3732, 4, 0, 0, 0]] ![![-34392, -39716, -32380, -48316, 131660], ![504000, 282696, 167116, 222172, -583440]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2087RS2]  
      rfl
    g := ![![![-175230388, 170316336, 47149394, 99932327, -194236418], ![187208075, -35193060, 0, 0, 0]], ![![78221760, -76028208, -21047200, -44609210, 86705994], ![-83568655, 15709995, 0, 0, 0]]]
    h := ![![![344079151900434900, -452053234830215, 116172515148397137, -249041090678585, 1402356229], ![769660439086590466, 92272147844034, 259862949988421472, -23227916008, 0]], ![![-4259585353075129896, 5596268554074151, -1438177062518396864, 3083045794274771, -17360703228], ![-9528140008096986264, -1142298471958512, -3217016809822159575, 287553868976, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2087N2 : Ideal.span {4} * I2087N2 =  Ideal.span {B.equivFun.symm ![-8598, -9929, -8095, -12079, 32915]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2087RS2
                    

def R2087RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![49, -74, -61, -62, 153] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![196, -296, -244, -248, 612], ![-1068, 912, 544, 504, -1320]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2087RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2087N3) (Ideal.span {B.equivFun.symm ![49, -74, -61, -62, 153]} * (J0 ^ 1*J1^ 1)) 
      ![![8348, 0, 0, 0, 0], ![-364, 4, 0, 0, 0]] ![![196, -296, -244, -248, 612], ![-1068, 912, 544, 504, -1320]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2087RS3]  
      rfl
    g := ![![![-208356835, 202482830, 56061921, 118813850, -230935998], ![222548053, -41837670, 0, 0, 0]], ![![9062597, -8807130, -2438449, -5167888, 10044714], ![-9679897, 1819755, 0, 0, 0]]]
    h := ![![![-1396639553374789, 61301261311607, -4197716104313894, 92257479432454, 52613847], ![-32030623746870552, -4017275261335, -96270741662067336, -871469036, 0]], ![![1836036222277825, -80587246703749, 5518359264678941, -121282598372674, -69166686], ![42107775967895042, 5281149941735, 126558472742456874, 1145641852, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2087N3 : Ideal.span {4} * I2087N3 =  Ideal.span {B.equivFun.symm ![49, -74, -61, -62, 153]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2087RS3
                    

def R2089RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![5, -5, -5, -5, 12] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![10, -10, -10, -10, 24], ![-44, 4, -8, -12, 26]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2089RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2089N1) (Ideal.span {B.equivFun.symm ![5, -5, -5, -5, 12]} * (J0 ^ 1*J1^ 0)) 
      ![![4178, 0, 0, 0, 0], ![102, 2, 0, 0, 0]] ![![10, -10, -10, -10, 24], ![-44, 4, -8, -12, 26]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2089RS1]  
      rfl
    g := ![![![-587, 479, 39, 68, 7], ![547, 0, 0, 0, 0]], ![![-12, 14, 2, 3, -3], ![15, 0, 0, 0, 0]]]
    h := ![![![12962435683433, 3692292584082, 175553574680044, 6884457081475, 1522308], ![-530951524786432, 167960225819, -7190815421600640, -25238900, 0]], ![![20778590875658, 5918689888189, 281409759285109, 11035681920106, 2440237], ![-851107367301684, 269237733235, -11526769765550720, -40457580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2089N1 : Ideal.span {2} * I2089N1 =  Ideal.span {B.equivFun.symm ![5, -5, -5, -5, 12]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2089RS1
                    

def R2089RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![92, 38, 23, 30, -76] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![184, 76, 46, 60, -152], ![-558, -346, -200, -254, 662]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2089RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2089N2) (Ideal.span {B.equivFun.symm ![92, 38, 23, 30, -76]} * (J0 ^ 1*J1^ 0)) 
      ![![4178, 0, 0, 0, 0], ![1864, 2, 0, 0, 0]] ![![184, 76, 46, 60, -152], ![-558, -346, -200, -254, 662]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2089RS2]  
      rfl
    g := ![![![-720227, 366123, 36913, 119803, -239585], ![-70401, 0, 0, 0, 0]], ![![-319769, 162559, 16391, 53194, -106380], ![-31256, 0, 0, 0, 0]]]
    h := ![![![-188108889804388, -293918683406, -128079802287837, -274874255338, -3545068], ![421630332531912, -101620555764, 287080269323628, 58774976, 0]], ![![815677291209381, 1274489447088, 555379314013935, 1191909049225, 15372115], ![-1828272379306329, 440646802869, -1244836736127864, -254859904, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2089N2 : Ideal.span {2} * I2089N2 =  Ideal.span {B.equivFun.symm ![92, 38, 23, 30, -76]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2089RS2
                    

def R2111RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-37708, 26529, 13277, 11183, -31009] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-150832, 106116, 53108, 44732, -124036], ![416376, -181640, -24572, 9412, 27072]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2111RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2111N1) (Ideal.span {B.equivFun.symm ![-37708, 26529, 13277, 11183, -31009]} * (J0 ^ 1*J1^ 1)) 
      ![![8444, 0, 0, 0, 0], ![-2784, 4, 0, 0, 0]] ![![-150832, 106116, 53108, 44732, -124036], ![416376, -181640, -24572, 9412, 27072]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2111RS1]  
      rfl
    g := ![![![151464731, -141631974, -40118205, -82691591, 160739276], ![-146132699, 30565470, 0, 0, 0]], ![![-49789752, 46563054, 13188376, 27185461, -52843680], ![48049342, -10047765, 0, 0, 0]]]
    h := ![![![-275431706536428980, 3472290865923732, -2663583809048120822, 7653982511722975, -497619071], ![-835397029272047602, -2276102043279713, -8078775427219033329, 8337093872, 0]], ![![-435857973363050382, 5494740162140641, -4214998540170826052, 12112074342776273, -787459248], ![-1321977272372849786, -3601826515514859, -12784289541189719919, 13193067296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2111N1 : Ideal.span {4} * I2111N1 =  Ideal.span {B.equivFun.symm ![-37708, 26529, 13277, 11183, -31009]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2111RS1
                    

def R2111RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![285, 16, 137, 174, -379] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![1140, 64, 548, 696, -1516], ![-396, -2192, -2568, -2832, 6672]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2111RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2111N2) (Ideal.span {B.equivFun.symm ![285, 16, 137, 174, -379]} * (J0 ^ 1*J1^ 1)) 
      ![![8444, 0, 0, 0, 0], ![-324, 4, 0, 0, 0]] ![![1140, 64, 548, 696, -1516], ![-396, -2192, -2568, -2832, 6672]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2111RS2]  
      rfl
    g := ![![![336564260, -327085112, -90559290, -191927774, 373045066], ![-359507289, 67581774, 0, 0, 0]], ![![-12867144, 12504768, 3462162, 7337574, -14261850], ![13744315, -2583711, 0, 0, 0]]]
    h := ![![![126292643630508, -104324792820647, 8348559604216277, -206137348114368, -17470469], ![3291404630796263, 7897984571941, 217577990252894391, 292699680, 0]], ![![-660471682566042, 545586579469034, -43660398979053063, 1078034929356192, 91365180], ![-17213033887134003, -41304030130203, -1137865968963595602, -1530729312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2111N2 : Ideal.span {4} * I2111N2 =  Ideal.span {B.equivFun.symm ![285, 16, 137, 174, -379]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2111RS2
                    

def R2113RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![149, 26, 90, 111, -246] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![298, 52, 180, 222, -492], ![1000, -678, -322, -264, 746]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2113RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2113N1) (Ideal.span {B.equivFun.symm ![149, 26, 90, 111, -246]} * (J0 ^ 1*J1^ 0)) 
      ![![4226, 0, 0, 0, 0], ![1256, 2, 0, 0, 0]] ![![298, 52, 180, 222, -492], ![1000, -678, -322, -264, 746]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2113RS1]  
      rfl
    g := ![![![-121015, 61534, 6226, 20098, -40065], ![-10899, 0, 0, 0, 0]], ![![-35708, 18162, 1839, 5933, -11828], ![-3212, 0, 0, 0, 0]]]
    h := ![![![-4634478296608777, -13989186414884, -4954725906251775, -15779448715369, -13177002], ![15593395919458125, -4307569064677, 16670923816145049, 220976230, 0]], ![![-5596217391851582, -16892198712300, -5982922243832767, -19053973216860, -15911471], ![18829311058885192, -5201468509288, 20130445722336453, 266832846, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2113N1 : Ideal.span {2} * I2113N1 =  Ideal.span {B.equivFun.symm ![149, 26, 90, 111, -246]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2113RS1
                    

def R2137RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-2, 12, 16, 17, -39] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-8, 48, 64, 68, -156], ![264, -236, -200, -196, 480]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2137RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2137N1) (Ideal.span {B.equivFun.symm ![-2, 12, 16, 17, -39]} * (J0 ^ 1*J1^ 1)) 
      ![![8548, 0, 0, 0, 0], ![-2440, 4, 0, 0, 0]] ![![-8, 48, 64, 68, -156], ![264, -236, -200, -196, 480]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2137RS1]  
      rfl
    g := ![![![-66469112, 64591169, 17876889, 37890251, -73648776], ![70948661, -13334100, 0, 0, 0]], ![![18833189, -18301060, -5065158, -10735662, 20867343], ![-20102166, 3777995, 0, 0, 0]]]
    h := ![![![20001888403732509, -46866856348854, 10111061637359957, -33150962250940, -13901169], ![70072189380840812, 8753413026386, 35421881086532388, 235768239, 0]], ![![-41121894549565067, 96353598508633, -20787337777608951, 68155083479738, 28579422], ![-144061456819166048, -17996147168612, -72823866896760882, -484716069, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2137N1 : Ideal.span {4} * I2137N1 =  Ideal.span {B.equivFun.symm ![-2, 12, 16, 17, -39]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2137RS1
                    

def R2143RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![156928, -191216, -47206, -86319, 195951] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![627712, -764864, -188824, -345276, 783804], ![3607536, -4395700, -1085128, -1984268, 4504440]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2143RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2143N1) (Ideal.span {B.equivFun.symm ![156928, -191216, -47206, -86319, 195951]} * (J0 ^ 1*J1^ 1)) 
      ![![8572, 0, 0, 0, 0], ![1724, 4, 0, 0, 0]] ![![627712, -764864, -188824, -345276, 783804], ![3607536, -4395700, -1085128, -1984268, 4504440]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2143RS1]  
      rfl
    g := ![![![294875809, -286427900, -79325816, -168065852, 326669469], ![-314600265, 59211922, 0, 0, 0]], ![![59333756, -57633636, -15961600, -33817404, 65730882], ![-63302001, 11914385, 0, 0, 0]]]
    h := ![![![3045343144104, 210268871709, 94964627246113, 440664097643, -2389695], ![-15141927998464, 85192306705, -472179303281474, 40645336, 0]], ![![17531770174830, 1210499235198, 546702931382599, 2536864103225, -13757262], ![-87170735484066, 490444542968, -2718294345253061, 233991576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2143N1 : Ideal.span {4} * I2143N1 =  Ideal.span {B.equivFun.symm ![156928, -191216, -47206, -86319, 195951]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2143RS1
                    

def R2161RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-77, -38, -23, -30, 79] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-308, -152, -92, -120, 316], ![156, 160, 64, 88, -216]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2161RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2161N0) (Ideal.span {B.equivFun.symm ![-77, -38, -23, -30, 79]} * (J0 ^ 1*J1^ 1)) 
      ![![8644, 0, 0, 0, 0], ![1208, 4, 0, 0, 0]] ![![-308, -152, -92, -120, 316], ![156, 160, 64, 88, -216]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2161RS0]  
      rfl
    g := ![![![-337987582, 328485463, 90944516, 192747647, -374636437], ![361062103, -67868762, 0, 0, 0]], ![![-47263166, 45934415, 12717406, 26953249, -52388027], ![50489838, -9490563, 0, 0, 0]]]
    h := ![![![6191397088416837, 39174790824163, 5864037253410782, 38834704692842, 2298211], ![-44303341415488552, 5322878010703, -41960893473889975, -39416142, 0]], ![![-3390133360952933, -21450371117520, -3210885691672562, -21264155094862, -1258398], ![24258537061905796, -2914570985298, 22975916871391640, 21582524, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2161N0 : Ideal.span {4} * I2161N0 =  Ideal.span {B.equivFun.symm ![-77, -38, -23, -30, 79]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2161RS0
                    

def R2161RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![80, -96, -22, -42, 95] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![160, -192, -44, -84, 190], ![72, -80, -10, -28, 62]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E2161RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2161N1) (Ideal.span {B.equivFun.symm ![80, -96, -22, -42, 95]} * (J0 ^ 0*J1^ 1)) 
      ![![4322, 0, 0, 0, 0], ![1718, 2, 0, 0, 0]] ![![160, -192, -44, -84, 190], ![72, -80, -10, -28, 62]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2161RS1]  
      rfl
    g := ![![![5142, -332, -721, -986, 2798], ![-2399, 0, 0, 0, 0]], ![![2059, -126, -284, -389, 1105], ![-954, 0, 0, 0, 0]]]
    h := ![![![29599792018584, 228384970228, 229004699618366, 533279023646, 13997219], ![-74464664669626, 182792711290, -576110999430268, -240063414, 0]], ![![8045746452340, 62079069918, 62247523620893, 144954661086, 3804691], ![-20240811530506, 49686289402, -156597148901550, -65253470, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2161N1 : Ideal.span {2} * I2161N1 =  Ideal.span {B.equivFun.symm ![80, -96, -22, -42, 95]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2161RS1
                    

def R2161RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 0) ![318, -210, -155, -112, 320] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![636, -420, -310, -224, 640], ![-1378, 766, -460, -258, 654]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

def E2161RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2161N2) (Ideal.span {B.equivFun.symm ![318, -210, -155, -112, 320]} * (J0 ^ 1*J1^ 0)) 
      ![![4322, 0, 0, 0, 0], ![1724, 2, 0, 0, 0]] ![![636, -420, -310, -224, 640], ![-1378, 766, -460, -258, 654]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2161RS2]  
      rfl
    g := ![![![-18558, -267179, 5090, 39701, -231711], ![-379055, 0, 0, 0, 0]], ![![-7208, -107021, 2020, 15858, -92692], ![-151884, 0, 0, 0, 0]]]
    h := ![![![-14206030104927042, -58183174956953, -49551346045994368, -114968597194586, -36416848], ![35613957131529780, -39563095512225, 124223316002432753, 624577848, 0]], ![![118854447895097991, 486788292378490, 414570279890498504, 961882316442749, 304680783], ![-297963412787614850, 331003794826732, -1039311723969151161, -5225517236, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2161N2 : Ideal.span {2} * I2161N2 =  Ideal.span {B.equivFun.symm ![318, -210, -155, -112, 320]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2161RS2
                    

def R2161RS3 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-1129, 1370, 333, 614, -1393] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-4516, 5480, 1332, 2456, -5572], ![-26052, 31744, 7888, 14360, -32616]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2161RS3 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2161N3) (Ideal.span {B.equivFun.symm ![-1129, 1370, 333, 614, -1393]} * (J0 ^ 1*J1^ 1)) 
      ![![8644, 0, 0, 0, 0], ![4016, 4, 0, 0, 0]] ![![-4516, 5480, 1332, 2456, -5572], ![-26052, 31744, 7888, 14360, -32616]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2161RS3]  
      rfl
    g := ![![![78477754, -76349954, -21125862, -44788438, 87040972], ![-83976953, 15765744, 0, 0, 0]], ![![36571322, -35579736, -9844836, -20871798, 40561844], ![-39133964, 7346975, 0, 0, 0]]]
    h := ![![![14627114543206495, 17726717106382, 4911672618875099, 9784330481690, 15684095], ![-31483261477922626, 3732717022810, -10571840909496906, -268994688, 0]], ![![78627824132613511, 95289688956406, 26402618898978723, 52595514590486, 84309606], ![-169237776821601746, 20065161629041, -56828764507111248, -1445976720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2161N3 : Ideal.span {4} * I2161N3 =  Ideal.span {B.equivFun.symm ![-1129, 1370, 333, 614, -1393]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2161RS3
                    

def R2161RS4 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 1*J1^ 1) ![-276, 220, 126, 113, -301] ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]]
  ![![-1104, 880, 504, 452, -1204], ![3408, -1788, -520, -276, 1056]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

def E2161RS4 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I2161N4) (Ideal.span {B.equivFun.symm ![-276, 220, 126, 113, -301]} * (J0 ^ 1*J1^ 1)) 
      ![![8644, 0, 0, 0, 0], ![-3464, 4, 0, 0, 0]] ![![-1104, 880, 504, 452, -1204], ![3408, -1788, -520, -276, 1056]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2161RS4]  
      rfl
    g := ![![![248960488, -241955941, -66988793, -141970285, 275939864], ![-265926573, 49994004, 0, 0, 0]], ![![-99601415, 96799128, 26800152, 56797944, -110395051], ![106389070, -20001059, 0, 0, 0]]]
    h := ![![![176116747956390351, -770843839703332, 679470210167566931, -1569217112850812, 174186509], ![439478397562295607, 541827701823870, 1695537720695495235, -2987436875, 0]], ![![-621670836089759621, 2720985595543187, -2398447726036444336, 5539146764133082, -614857326], ![-1551305631214539463, -1912586306057627, -5985043243629814323, 10545291125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2161N4 : Ideal.span {4} * I2161N4 =  Ideal.span {B.equivFun.symm ![-276, 220, 126, 113, -301]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2161RS4
                    

def R2179RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J0 ^ 0*J1^ 1) ![-7578, 5514, 2866, 2464, -6745] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![-15156, 11028, 5732, 4928, -13490], ![-42688, 33332, 18642, 16596, -44442]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

def E2179RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2179N2) (Ideal.span {B.equivFun.symm ![-7578, 5514, 2866, 2464, -6745]} * (J0 ^ 0*J1^ 1)) 
      ![![4358, 0, 0, 0, 0], ![-1138, 2, 0, 0, 0]] ![![-15156, 11028, 5732, 4928, -13490], ![-42688, 33332, 18642, 16596, -44442]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2179RS2]  
      rfl
    g := ![![![1663734, 47951, -201559, -354569, 1042755], ![-418979, 0, 0, 0, 0]], ![![-432481, -12280, 52436, 92137, -270929], ![109310, 0, 0, 0, 0]]]
    h := ![![![27700429211430538, -609208619530609, 365614553932823669, -1285121482575588, 1688054765], ![106079498794055720, 314141943535737, 1400130805550903558, -29192629680, 0]], ![![72254955344364590, -1589085182171526, 953684257600931113, -3352164496335380, 4403192481], ![276702190778842466, 819420952968145, 3652159613102671459, -76147273320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2179N2 : Ideal.span {2} * I2179N2 =  Ideal.span {B.equivFun.symm ![-7578, 5514, 2866, 2464, -6745]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2179RS2
                    
