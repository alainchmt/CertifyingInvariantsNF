import IdealArithmetic.Examples.NF6.PrimesBelow4
import IdealArithmetic.Examples.NF6.NonPrincipalExample6

noncomputable section

def R2RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![0, 1, -1, 0, -1] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![0, 2, -2, 0, -2], ![0, 4, -2, 0, -2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E2RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2N0) (Ideal.span {B.equivFun.symm ![0, 1, -1, 0, -1]} * J ^ 1)
      ![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]] ![![0, 2, -2, 0, -2], ![0, 4, -2, 0, -2]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS0
    g := ![![![2, -3, 0, 0, 0], ![-1, 1, 0, 0, 1]], ![![-1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
    h := ![![![0, 0, 0, -3, -5], ![1, -1, 0, 0, -3]], ![![0, 0, 0, -3, -5], ![2, -1, 0, 0, -3]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![0, 1, -1, 0, -1]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS0


def R2RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![1, 0, 0, 0, 0] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E2RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {1} * I2N1) (Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * J ^ 1)
      ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS1
    g := ![![![18, 0, 7, 4, 12], ![-2, 8, 2, 0, 0]], ![![-11, 0, -1, -3, -6], ![3, -4, -2, 2, 0]]]
    h := ![![![18, 0, 7, 4, 12], ![-2, 8, 2, 0, 0]], ![![-11, 0, -1, -3, -6], ![3, -4, -2, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS1


def R2RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![4, -1, 5, 2, 7] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![8, -2, 10, 4, 14], ![-4, -18, -8, -6, -10]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E2RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I2N2) (Ideal.span {B.equivFun.symm ![4, -1, 5, 2, 7]} * J ^ 1)
      ![![4, 0, 0, 0, 0], ![8, -4, -2, -2, -4]] ![![8, -2, 10, 4, 14], ![-4, -18, -8, -6, -10]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R2RS2
    g := ![![![2513, -622, 851, 431, 1292], ![-488, 1329, 21, 0, 0]], ![![3358, -831, 1138, 576, 1728], ![-651, 1776, 28, 0, 0]]]
    h := ![![![2470, -3732, 3905, 902, 5953], ![320, 1866, 0, -192, 21]], ![![-1418, 2135, -2236, -518, -3410], ![-181, -1068, 0, 108, -15]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![4, -1, 5, 2, 7]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E2RS2


def R3RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 4) ![45, 34, 44, 23, 57] ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![180, 136, 176, 92, 228], ![120, 96, 96, 52, 120]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
    hmul := by decide

def E3RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I3N0) (Ideal.span {B.equivFun.symm ![45, 34, 44, 23, 57]} * J ^ 4)
      ![![12, 0, 0, 0, 0], ![0, 4, 0, 0, 0]] ![![180, 136, 176, 92, 228], ![120, 96, 96, 52, 120]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS0
    g := ![![![-27628, 35992, -2623, 9817, -5175], ![-5599, -44445, -141, 0, 0]], ![![-27623, 35979, -2621, 9814, -5173], ![-5594, -44430, -141, 0, 0]]]
    h := ![![![15, -66, 0, -161, 19], ![-21, 44, 253, 0, 0]], ![![10, -36, 0, -91, 10], ![-11, 24, 143, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![45, 34, 44, 23, 57]} * J ^ 4 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS0


def R3RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 4) ![15, 4, -6, -3, -11] ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![60, 16, -24, -12, -44], ![56, 52, -52, -20, -88]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
    hmul := by decide

def E3RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I3N1) (Ideal.span {B.equivFun.symm ![15, 4, -6, -3, -11]} * J ^ 4)
      ![![12, 0, 0, 0, 0], ![8, 12, -12, -4, -20]] ![![60, 16, -24, -12, -44], ![56, 52, -52, -20, -88]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS1
    g := ![![![-39963245, 51699868, -3912756, 13972640, -7825747], ![-7824337, -63716306, 470, 0, 0]], ![![-75949131, 98254293, -7436096, 26554647, -14872639], ![-14869959, -121091227, 893, 0, 0]]]
    h := ![![![1, 1, -1, 2, 2], ![-1, -2, 0, 0, -4]], ![![-2, 3, -3, 6, 5], ![-3, 0, 0, 0, -13]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4} * I3N1 =  Ideal.span {B.equivFun.symm ![15, 4, -6, -3, -11]} * J ^ 4 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS1


def R3RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![1, 0, 2, 1, 3] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![2, 0, 4, 2, 6], ![4, -2, 6, 2, 8]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E3RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I3N2) (Ideal.span {B.equivFun.symm ![1, 0, 2, 1, 3]} * J ^ 2)
      ![![6, 0, 0, 0, 0], ![2, 2, 0, 0, 0]] ![![2, 0, 4, 2, 6], ![4, -2, 6, 2, 8]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R3RS2
    g := ![![![-85, 142, -6, 43, -5], ![-19, -88, -6, 0, 0]], ![![-15, 18, -1, 5, -2], ![-1, -11, 0, 0, 0]]]
    h := ![![![0, 39, 40, 87, -9], ![1, 27, -145, 0, -15]], ![![0, 52, 54, 117, -12], ![2, 36, -195, 0, -20]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {2} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 2, 1, 3]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E3RS2



def R5RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 3) ![-4, 3, -1, 0, -1] ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]]
  ![![-16, 12, -4, 0, -4], ![-28, -20, 20, 8, 32]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
    hmul := by decide

def E5RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I5N) (Ideal.span {B.equivFun.symm ![-4, 3, -1, 0, -1]} * J ^ 3)
      ![![20, 0, 0, 0, 0], ![8, 4, 0, 0, 0]] ![![-16, 12, -4, 0, -4], ![-28, -20, 20, 8, 32]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R5RS0
    g := ![![![-440, 1668, 1300, 898, 1240], ![-565, -1365, -9, 0, 0]], ![![-244, 912, 716, 494, 685], ![-308, -750, -5, 0, 0]]]
    h := ![![![-2200, -1291, -288, -276, -365], ![5270, 515, 310, 152, 0]], ![![-1645, -964, -204, -194, -272], ![3938, 395, 201, 114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N =  Ideal.span {B.equivFun.symm ![-4, 3, -1, 0, -1]} * J ^ 3 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E5RS0


def R11RS0 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![-1, -9, 9, 3, 14] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![-2, -18, 18, 6, 28], ![12, -48, 36, 10, 56]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E11RS0 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N0) (Ideal.span {B.equivFun.symm ![-1, -9, 9, 3, 14]} * J ^ 2)
      ![![22, 0, 0, 0, 0], ![-6, 18, -6, -2, -10]] ![![-2, -18, 18, 6, 28], ![12, -48, 36, 10, 56]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS0
    g := ![![![4433, -4705, 793, -883, 1886], ![41, 2709, -301, 0, 0]], ![![4388, -4648, 789, -866, 1879], ![36, 2673, -301, 0, 0]]]
    h := ![![![-1406, -854, 2206, 206, 535], ![-1164, -3944, 47, 0, 0]], ![![-2955, -1785, 4629, 428, 1117], ![-2455, -8280, 102, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-1, -9, 9, 3, 14]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS0


def R11RS1 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![-1, 4, -2, -1, -3] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![-2, 8, -4, -2, -6], ![-16, 14, -6, 2, -8]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E11RS1 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N1) (Ideal.span {B.equivFun.symm ![-1, 4, -2, -1, -3]} * J ^ 2)
      ![![22, 0, 0, 0, 0], ![-2, 8, -4, -2, -6]] ![![-2, 8, -4, -2, -6], ![-16, 14, -6, 2, -8]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS1
    g := ![![![9, 6, 10, 5, 13], ![-1, 0, 0, 0, 0]], ![![20, -31, 4, -7, 8], ![4, 18, 0, 0, 0]]]
    h := ![![![-12, -8, 8, -4, -12], ![1, -44, 0, 0, 0]], ![![-15885, -10655, 10325, -4770, -15803], ![449, -57708, -684, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![-1, 4, -2, -1, -3]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS1


def R11RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![0, -9, 7, 2, 11] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![0, -18, 14, 4, 22], ![6, -30, 18, 4, 28]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E11RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I11N2) (Ideal.span {B.equivFun.symm ![0, -9, 7, 2, 11]} * J ^ 1)
      ![![22, 0, 0, 0, 0], ![8, 2, 0, 0, 0]] ![![0, -18, 14, 4, 22], ![6, -30, 18, 4, 28]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R11RS2
    g := ![![![6, 3, -4, -2, -7], ![-5, 0, 0, 0, -1]], ![![0, 4, -5, -3, -7], ![-4, -3, 0, 0, -3]]]
    h := ![![![-489, -128, -105, -141, -179], ![1221, 36, 199, 165, 0]], ![![-561, -148, -124, -164, -206], ![1401, 41, 238, 190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![0, -9, 7, 2, 11]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E11RS2


def R19RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 3) ![-2, -3, -3, -2, -5] ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]]
  ![![-8, -12, -12, -8, -20], ![-20, -20, -36, -16, -44]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
    hmul := by decide

def E19RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I19N2) (Ideal.span {B.equivFun.symm ![-2, -3, -3, -2, -5]} * J ^ 3)
      ![![76, 0, 0, 0, 0], ![36, 4, 0, 0, 0]] ![![-8, -12, -12, -8, -20], ![-20, -20, -36, -16, -44]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R19RS2
    g := ![![![-2649, 8793, 6799, 4637, 6283], ![-2931, -7290, 54, 0, 0]], ![![-1370, 4540, 3512, 2395, 3246], ![-1513, -3765, 28, 0, 0]]]
    h := ![![![18437023, 2471558, 6186479, 1376950, -4619], ![-38925042, 566406, -13124904, 7313, 0]], ![![45998794, 6166335, 15434748, 3435374, -11525], ![-97114648, 1413118, -32745537, 18247, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {4} * I19N2 =  Ideal.span {B.equivFun.symm ![-2, -3, -3, -2, -5]} * J ^ 3 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E19RS2


def R23RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![-8, -7, -3, -2, -3] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![-16, -14, -6, -4, -6], ![14, 6, 34, 16, 48]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E23RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I23N2) (Ideal.span {B.equivFun.symm ![-8, -7, -3, -2, -3]} * J ^ 1)
      ![![46, 0, 0, 0, 0], ![-8, 2, 0, 0, 0]] ![![-16, -14, -6, -4, -6], ![14, 6, 34, 16, 48]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R23RS2
    g := ![![![-59074, 7967, -18965, -10279, -30840], ![11295, -28665, -3185, 0, 0]], ![![8444, -1140, 2712, 1470, 4410], ![-1614, 4098, 455, 0, 0]]]
    h := ![![![-6025, 6727, -22044, 11059, -537], ![-33870, -1709, -126665, 1029, 0]], ![![4835, -5371, 17593, -8826, 432], ![27180, 1390, 101090, -826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {2} * I23N2 =  Ideal.span {B.equivFun.symm ![-8, -7, -3, -2, -3]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E23RS2


def R31RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 3) ![-8, 3, 7, 4, 11] ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]]
  ![![-32, 12, 28, 16, 44], ![4, -52, 100, 40, 152]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
    hmul := by decide

def E31RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I31N2) (Ideal.span {B.equivFun.symm ![-8, 3, 7, 4, 11]} * J ^ 3)
      ![![124, 0, 0, 0, 0], ![-16, 4, 0, 0, 0]] ![![-32, 12, 28, 16, 44], ![4, -52, 100, 40, 152]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R31RS2
    g := ![![![-3522066, 12845581, 9964227, 6856802, 9402088], ![-4332799, -10537005, -21285, 0, 0]], ![![409540, -1493671, -1158627, -797300, -1093261], ![503814, 1225230, 2475, 0, 0]]]
    h := ![![![862368, -3306709, 12756375, -6391236, 5333], ![6673022, 809022, 99057272, -13776, 0]], ![![2610436, -10009552, 38614093, -19346545, 16142], ![20199606, 2448952, 299850604, -41697, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {4} * I31N2 =  Ideal.span {B.equivFun.symm ![-8, 3, 7, 4, 11]} * J ^ 3 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E31RS2


def R47RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![1, 1, -1, 1, 2] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![2, 2, -2, 2, 4], ![-4, 12, -8, -6, -24]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E47RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I47N2) (Ideal.span {B.equivFun.symm ![1, 1, -1, 1, 2]} * J ^ 2)
      ![![94, 0, 0, 0, 0], ![36, 2, 0, 0, 0]] ![![2, 2, -2, 2, 4], ![-4, 12, -8, -6, -24]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R47RS2
    g := ![![![155210, -224543, 19068, -59054, 36502], ![23341, 136323, 1683, 0, 0]], ![![86240, -124739, 10602, -32804, 20290], ![12968, 75738, 935, 0, 0]]]
    h := ![![![-2101, -100, 2388, 221, -26], ![5469, 311, -6264, 102, 0]], ![![-35929, -1379, 42696, 3966, -456], ![93517, 4724, -111945, 1785, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {2} * I47N2 =  Ideal.span {B.equivFun.symm ![1, 1, -1, 1, 2]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E47RS2


def R59RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 4) ![-3, -4, -2, -1, -1] ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![-12, -16, -8, -4, -4], ![-8, -12, -4, -4, -8]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
    hmul := by decide

def E59RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I59N2) (Ideal.span {B.equivFun.symm ![-3, -4, -2, -1, -1]} * J ^ 4)
      ![![236, 0, 0, 0, 0], ![-76, 4, 0, 0, 0]] ![![-12, -16, -8, -4, -4], ![-8, -12, -4, -4, -8]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R59RS2
    g := ![![![-36, 0, 13, 9, 55], ![59, 0, 0, 0, 34]], ![![7, 0, -5, -3, -22], ![-19, 1, 0, 0, -16]]]
    h := ![![![-10322753, 1754642, -28080952, 2976685, -14675], ![-32043472, -832986, -87234992, 72152, 0]], ![![-6937186, 1179165, -18871161, 2000413, -9862], ![-21534132, -559798, -58624280, 48488, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![-3, -4, -2, -1, -1]} * J ^ 4 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E59RS2


def R67RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 3) ![-2, -1, -1, -2, -3] ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]]
  ![![-8, -4, -4, -8, -12], ![-20, -20, -12, 0, -12]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
    hmul := by decide

def E67RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I67N2) (Ideal.span {B.equivFun.symm ![-2, -1, -1, -2, -3]} * J ^ 3)
      ![![268, 0, 0, 0, 0], ![116, 4, 0, 0, 0]] ![![-8, -4, -4, -8, -12], ![-20, -20, -12, 0, -12]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R67RS2
    g := ![![![2928177, -13434524, -10501462, -7358269, -10329201], ![4627249, 10793670, 239904, 0, 0]], ![![1281076, -5877598, -4594384, -3219239, -4519020], ![2024419, 4722225, 104958, 0, 0]]]
    h := ![![![773995120, 33745942, 301548916, 20786250, -6849], ![-1788199578, 7731411, -696951216, 38240, 0]], ![![2394554474, 104401846, 932919641, 64307646, -21189], ![-5532258782, 23919049, -2156199021, 118305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {4} * I67N2 =  Ideal.span {B.equivFun.symm ![-2, -1, -1, -2, -3]} * J ^ 3 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E67RS2


def R71RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![-5, 9, -5, -1, -8] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![-10, 18, -10, -2, -16], ![-36, 28, -8, 2, -8]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E71RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I71N2) (Ideal.span {B.equivFun.symm ![-5, 9, -5, -1, -8]} * J ^ 2)
      ![![142, 0, 0, 0, 0], ![12, 2, 0, 0, 0]] ![![-10, 18, -10, -2, -16], ![-36, 28, -8, 2, -8]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R71RS2
    g := ![![![2462709, -119871, -687905, -609863, -1335880], ![-787623, 551767, -39903, 0, 0]], ![![227050, -11056, -63421, -56227, -123160], ![-72614, 50872, -3679, 0, 0]]]
    h := ![![![103136, 1356624, 8143385, 2710654, -7036], ![-1241258, 229690, -96415548, 41629, 0]], ![![180267, 2370959, 14232085, 4737374, -12296], ![-2169538, 401395, -168504156, 72751, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![-5, 9, -5, -1, -8]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E71RS2


def R79RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![-7, 21, -13, -3, -20] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![-14, 42, -26, -6, -40], ![-68, 78, -34, -2, -48]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E79RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I79N2) (Ideal.span {B.equivFun.symm ![-7, 21, -13, -3, -20]} * J ^ 2)
      ![![158, 0, 0, 0, 0], ![-30, 2, 0, 0, 0]] ![![-14, 42, -26, -6, -40], ![-68, 78, -34, -2, -48]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R79RS2
    g := ![![![5974006, -8162115, 804300, -2047762, 1640744], ![723999, 4915890, -32130, 0, 0]], ![![-1054235, 1440367, -141934, 361369, -289540], ![-127763, -867507, 5670, 0, 0]]]
    h := ![![![14631014, -1762246, 12443669, -1671187, 11908], ![77040995, 229563, 65541509, -78396, 0]], ![![29442044, -3546169, 25040247, -3362911, 23964], ![155029881, 461910, 131888394, -157765, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {2} * I79N2 =  Ideal.span {B.equivFun.symm ![-7, 21, -13, -3, -20]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E79RS2


def R83RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 3) ![2, -3, 5, 2, 7] ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]]
  ![![8, -12, 20, 8, 28], ![44, 4, 20, 8, 28]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
    hmul := by decide

def E83RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I83N2) (Ideal.span {B.equivFun.symm ![2, -3, 5, 2, 7]} * J ^ 3)
      ![![332, 0, 0, 0, 0], ![92, 4, 0, 0, 0]] ![![8, -12, 20, 8, 28], ![44, 4, 20, 8, 28]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R83RS2
    g := ![![![15702, -52153, -40304, -27488, -37244], ![17423, 43200, -320, 0, 0]], ![![4509, -14976, -11573, -7893, -10694], ![5003, 12405, -92, 0, 0]]]
    h := ![![![1112124, 57625, 131751, 13158, 797], ![-4012598, -13104, -474400, -5512, 0]], ![![1982829, 102762, 234652, 23438, 1421], ![-7154144, -23479, -844912, -9828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {4} * I83N2 =  Ideal.span {B.equivFun.symm ![2, -3, 5, 2, 7]} * J ^ 3 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E83RS2


def R103RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 2) ![-15, -5, -15, -7, -20] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]]
  ![![-30, -10, -30, -14, -40], ![-52, -12, -32, -14, -40]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
    hmul := by decide

def E103RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I103N2) (Ideal.span {B.equivFun.symm ![-15, -5, -15, -7, -20]} * J ^ 2)
      ![![206, 0, 0, 0, 0], ![68, 2, 0, 0, 0]] ![![-30, -10, -30, -14, -40], ![-52, -12, -32, -14, -40]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R103RS2
    g := ![![![-8455492, 11435263, -1155332, 2843191, -2380140], ![-981689, -6876441, 69459, 0, 0]], ![![-2851848, 3856859, -389668, 958945, -802768], ![-331102, -2319270, 23427, 0, 0]]]
    h := ![![![88970558, 4417887, 76386978, 4491370, -896], ![-269529134, 1351243, -231447805, 7689, 0]], ![![124749337, 6194524, 107105301, 6297534, -1256], ![-377918061, 1894567, -324522416, 10779, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {2} * I103N2 =  Ideal.span {B.equivFun.symm ![-15, -5, -15, -7, -20]} * J ^ 2 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E103RS2


def R127RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![2, 1, 1, 0, 3] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![4, 2, 2, 0, 6], ![-2, 0, -4, -4, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E127RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I127N2) (Ideal.span {B.equivFun.symm ![2, 1, 1, 0, 3]} * J ^ 1)
      ![![254, 0, 0, 0, 0], ![-48, 2, 0, 0, 0]] ![![4, 2, 2, 0, 6], ![-2, 0, -4, -4, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R127RS2
    g := ![![![216321, -29298, 69476, 37631, 112971], ![-41425, 104949, 11661, 0, 0]], ![![-28225, 3832, -9066, -4909, -14742], ![5410, -13692, -1521, 0, 0]]]
    h := ![![![-9872845, 721076, -7809283, 656855, -3471], ![-52239213, -84328, -41324575, 36735, 0]], ![![9873140, -721058, 7809593, -656881, 3471], ![52240774, 84557, 41326225, -36735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {2} * I127N2 =  Ideal.span {B.equivFun.symm ![2, 1, 1, 0, 3]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E127RS2


def R131RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 3) ![-2, 5, -3, -2, -9] ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]]
  ![![-8, 20, -12, -8, -36], ![-20, 0, 8, 16, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      exact ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
    hmul := by decide

def E131RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {4} * I131N2) (Ideal.span {B.equivFun.symm ![-2, 5, -3, -2, -9]} * J ^ 3)
      ![![524, 0, 0, 0, 0], ![244, 4, 0, 0, 0]] ![![-8, 20, -12, -8, -36], ![-20, 0, 8, 16, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R131RS2
    g := ![![![36921, -136294, -105756, -72869, -100050], ![46025, 111675, 367, 0, 0]], ![![17303, -63872, -49561, -34149, -46887], ![21569, 52335, 172, 0, 0]]]
    h := ![![![-105816473, -4734057, -279726540, -9273182, -18951], ![227235038, -3403933, 600773228, 206881, 0]], ![![-81932786, -3665557, -216590510, -7180164, -14673], ![175946138, -2635622, 465174952, 160181, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {4} * I131N2 =  Ideal.span {B.equivFun.symm ![-2, 5, -3, -2, -9]} * J ^ 3 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E131RS2


def R139RS2 : IdealMulPrincipalCertificate O ℤ timesTableO (J ^ 1) ![4, 3, 3, 2, 5] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![8, 6, 6, 4, 10], ![-10, -8, -16, -8, -20]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by
      simp only [pow_succ, pow_one, pow_zero, one_mul]
      rfl
    hmul := by decide

def E139RS2 : IdealEqCertificateO O ℤ timesTableO (Ideal.span {2} * I139N2) (Ideal.span {B.equivFun.symm ![4, 3, 3, 2, 5]} * J ^ 1)
      ![![278, 0, 0, 0, 0], ![-30, 2, 0, 0, 0]] ![![8, 6, 6, 4, 10], ![-10, -8, -16, -8, -20]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe O ℤ  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by
      exact ideal_eq_principal_mul_of_IdealMulPrincipalCertificate O ℤ _ _ _ _ _ R139RS2
    g := ![![![7054238, -1557429, 2357573, 1212624, 3637924], ![-1366527, 3656340, 135420, 0, 0]], ![![-751689, 165958, -251217, -129214, -387648], ![145617, -389613, -14430, 0, 0]]]
    h := ![![![56512588, -11324512, 115850792, -15462250, 14303], ![523650180, 1556067, 1073632320, -165676, 0]], ![![-78318368, 15694161, -160552546, 21428456, -19822], ![-725704289, -2156372, -1487900070, 229604, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {2} * I139N2 =  Ideal.span {B.equivFun.symm ![4, 3, 3, 2, 5]} * J ^ 1 := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ _ _ E139RS2
