import IdealArithmetic.Examples.NF2_0_231_1.PrimesBelow2_0_231_1F0
import IdealArithmetic.Examples.NF2_0_231_1.ClassGroupSaturated2_0_231_1_3

noncomputable section

noncomputable def R2RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 5*J1^ 0) ![2, 1] ![![32, 0], ![29, 1]]
  ![![64, 32], ![0, 32]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_0
    hmul := by decide

noncomputable def E2RS0 : IdealEqCertificateO timesTableO (Ideal.span {32} * I2N0) (Ideal.span {B.equivFun.symm ![2, 1]} * (J0 ^ 5*J1^ 0))
      ![![64, 0], ![0, 32]] ![![64, 32], ![0, 32]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 32 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R2RS0]
      rfl
    g := ![![![1, 0], ![-1, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![1, 0], ![1, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![2, 1]} * (J0 ^ 5*J1^ 0) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E2RS0


noncomputable def R2RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![1, 0] ![![2, 0], ![1, 1]]
  ![![2, 0], ![1, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E2RS1 : IdealEqCertificateO timesTableO (Ideal.span {1} * I2N1) (Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 1*J1^ 0))
      ![![2, 0], ![1, 1]] ![![2, 0], ![1, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R2RS1]
      rfl
    g := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 1*J1^ 0) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E2RS1


noncomputable def R3RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 3*J1^ 1) ![10, 1] ![![56, 0], ![45, 1]]
  ![![560, 56], ![392, 56]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_3J1_1
    hmul := by decide

noncomputable def E3RS0 : IdealEqCertificateO timesTableO (Ideal.span {56} * I3N0) (Ideal.span {B.equivFun.symm ![10, 1]} * (J0 ^ 3*J1^ 1))
      ![![168, 0], ![56, 56]] ![![560, 56], ![392, 56]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 56 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS0]
      rfl
    g := ![![![-44, -1], ![55, 0]], ![![-2, 0], ![3, 0]]]
    h := ![![![3, 0], ![1, 0]], ![![2, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {56} * I3N0 =  Ideal.span {B.equivFun.symm ![10, 1]} * (J0 ^ 3*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS0


noncomputable def R5RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![-4, 1] ![![14, 0], ![3, 1]]
  ![![-56, 14], ![-70, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E5RS0 : IdealEqCertificateO timesTableO (Ideal.span {14} * I5N0) (Ideal.span {B.equivFun.symm ![-4, 1]} * (J0 ^ 1*J1^ 1))
      ![![70, 0], ![14, 14]] ![![-56, 14], ![-70, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 14 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS0]
      rfl
    g := ![![![-3, -1], ![13, 0]], ![![-2, -1], ![13, 0]]]
    h := ![![![-1, 0], ![1, 0]], ![![-1, 0], ![0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {14} * I5N0 =  Ideal.span {B.equivFun.symm ![-4, 1]} * (J0 ^ 1*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS0


noncomputable def R5RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 5*J1^ 1) ![26, -3] ![![224, 0], ![157, 1]]
  ![![5824, -672], ![4256, -448]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_5J1_1
    hmul := by decide

noncomputable def E5RS1 : IdealEqCertificateO timesTableO (Ideal.span {224} * I5N1) (Ideal.span {B.equivFun.symm ![26, -3]} * (J0 ^ 5*J1^ 1))
      ![![1120, 0], ![672, 224]] ![![5824, -672], ![4256, -448]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 224 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS1]
      rfl
    g := ![![![-2, 0], ![3, 0]], ![![-5, 0], ![7, 0]]]
    h := ![![![1, -2], ![7, 0]], ![![2, -1], ![3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {224} * I5N1 =  Ideal.span {B.equivFun.symm ![26, -3]} * (J0 ^ 5*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS1


noncomputable def R7RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![1, 0] ![![7, 0], ![3, 1]]
  ![![7, 0], ![3, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E7RS0 : IdealEqCertificateO timesTableO (Ideal.span {1} * I7N0) (Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 0*J1^ 1))
      ![![7, 0], ![3, 1]] ![![7, 0], ![3, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R7RS0]
      rfl
    g := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 0*J1^ 1) := by
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E7RS0
