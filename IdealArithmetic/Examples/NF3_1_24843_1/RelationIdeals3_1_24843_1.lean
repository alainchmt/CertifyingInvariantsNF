import IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F0
import IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F1
import IdealArithmetic.Examples.NF3_1_24843_1.ClassGroupData3_1_24843_1

set_option linter.all false

noncomputable section

noncomputable def R2RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![0, -2, 1] ![![4, 0, 0], ![1, 1, 0]]
  ![![0, -8, 4], ![32, 0, -4]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E2RS0 : IdealEqCertificateO timesTableO (Ideal.span {4} * I2N0) (Ideal.span {B.equivFun.symm ![0, -2, 1]} * (J0 ^ 2*J1^ 0)) 
      ![![8, 0, 0], ![0, 0, 4]] ![![0, -8, 4], ![32, 0, -4]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R2RS0]  
      rfl
    g := ![![![0, -10, -11], ![39, 15, -1]], ![![0, -10, 0], ![35, 0, -2]]]
    h := ![![![0, -1, 0], ![1, 0, 0]], ![![4, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![0, -2, 1]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E2RS0
                    

noncomputable def R2RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![1, 1, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E2RS1 : IdealEqCertificateO timesTableO (Ideal.span {1} * I2N1) (Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0)) 
      ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R2RS1]  
      rfl
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E2RS1
                    

noncomputable def R3RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![1, 0, 0] ![![3, 0, 0], ![0, 0, 1]]
  ![![3, 0, 0], ![0, 0, 1]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E3RS0 : IdealEqCertificateO timesTableO (Ideal.span {1} * I3N0) (Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1)) 
      ![![3, 0, 0], ![0, 0, 1]] ![![3, 0, 0], ![0, 0, 1]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 1 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS0]  
      rfl
    g := ![![![-9, 10, 0], ![0, 3, -3]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-9, 10, 0], ![0, 3, -3]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS0
                    

noncomputable def R3RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![-4, 1, 0] ![![3, 0, 0], ![0, 0, 1]]
  ![![-12, 3, 0], ![30, 0, -3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E3RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I3N1) (Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 0*J1^ 1)) 
      ![![9, 0, 0], ![-3, 0, 3]] ![![-12, 3, 0], ![30, 0, -3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R3RS1]  
      rfl
    g := ![![![-1385, -693, -63], ![-18, 0, 208]], ![![525, 261, 24], ![8, 0, -78]]]
    h := ![![![8, 0, 1], ![-2, -1, 0]], ![![3, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E3RS1
                    

noncomputable def R5RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-10, 0, 1] ![![6, 0, 0], ![2, 1, 1]]
  ![![-60, 0, 6], ![30, 0, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E5RS0 : IdealEqCertificateO timesTableO (Ideal.span {6} * I5N0) (Ideal.span {B.equivFun.symm ![-10, 0, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![30, 0, 0], ![0, 0, 6]] ![![-60, 0, 6], ![30, 0, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS0]  
      rfl
    g := ![![![-3, -1, -1], ![5, 0, 0]], ![![-3, -1, -1], ![4, 0, 0]]]
    h := ![![![-2, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![-10, 0, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS0
                    

noncomputable def R5RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![-16, -2, 3] ![![12, 0, 0], ![-3, 0, 1]]
  ![![-192, -24, 36], ![48, 36, -24]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E5RS1 : IdealEqCertificateO timesTableO (Ideal.span {12} * I5N1) (Ideal.span {B.equivFun.symm ![-16, -2, 3]} * (J0 ^ 2*J1^ 1)) 
      ![![60, 0, 0], ![-12, 12, 0]] ![![-192, -24, 36], ![48, 36, -24]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R5RS1]  
      rfl
    g := ![![![-472, 55, -28], ![127, 205, -4]], ![![5, 0, 0], ![4, -1, 0]]]
    h := ![![![743, 1411, -2157], ![135, 3596, 0]], ![![-155, -296, 452], ![-25, -754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {12} * I5N1 =  Ideal.span {B.equivFun.symm ![-16, -2, 3]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E5RS1
                    

noncomputable def R7RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 1) ![20, 4, 3] ![![6, 0, 0], ![3, 0, 1]]
  ![![120, 24, 18], ![240, 42, 36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_1
    hmul := by decide

noncomputable def E7RS0 : IdealEqCertificateO timesTableO (Ideal.span {6} * I7N0) (Ideal.span {B.equivFun.symm ![20, 4, 3]} * (J0 ^ 1*J1^ 1)) 
      ![![42, 0, 0], ![0, 6, 0]] ![![120, 24, 18], ![240, 42, 36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R7RS0]  
      rfl
    g := ![![![32765019, 4087538, -1330692], ![16160731, -8167577, -2250]], ![![-1, 0, -1], ![5, 0, 0]]]
    h := ![![![0, -3, 9], ![5, -20, 0]], ![![0, -5, 18], ![2, -40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {6} * I7N0 =  Ideal.span {B.equivFun.symm ![20, 4, 3]} * (J0 ^ 1*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E7RS0
                    

noncomputable def R11RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![2, 1, 0] ![![3, 0, 0], ![0, 0, 1]]
  ![![6, 3, 0], ![30, 0, 3]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E11RS1 : IdealEqCertificateO timesTableO (Ideal.span {3} * I11N1) (Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 0*J1^ 1)) 
      ![![33, 0, 0], ![6, 3, 0]] ![![6, 3, 0], ![30, 0, 3]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 3 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R11RS1]  
      rfl
    g := ![![![67, 33, 3], ![2, 0, -10]], ![![21, 10, 0], ![3, 0, -3]]]
    h := ![![![-30, 30, 90], ![1, -330, 0]], ![![-162, 164, 491], ![-4, -1800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E11RS1
                    

noncomputable def R13RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-4, 2, -1] ![![12, 0, 0], ![2, 1, 1]]
  ![![-48, 24, -12], ![0, -12, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E13RS0 : IdealEqCertificateO timesTableO (Ideal.span {12} * I13N0) (Ideal.span {B.equivFun.symm ![-4, 2, -1]} * (J0 ^ 2*J1^ 2)) 
      ![![156, 0, 0], ![0, 12, 0]] ![![-48, 24, -12], ![0, -12, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R13RS0]  
      rfl
    g := ![![![-32, -1, -4], ![-5, 13, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    h := ![![![0, 0, -1], ![6, 4, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {12} * I13N0 =  Ideal.span {B.equivFun.symm ![-4, 2, -1]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E13RS0
                    

noncomputable def R17RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![8, 2, 1] ![![4, 0, 0], ![1, 1, 0]]
  ![![32, 8, 4], ![36, 8, 8]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E17RS1 : IdealEqCertificateO timesTableO (Ideal.span {4} * I17N1) (Ideal.span {B.equivFun.symm ![8, 2, 1]} * (J0 ^ 2*J1^ 0)) 
      ![![68, 0, 0], ![-20, 4, 0]] ![![32, 8, 4], ![36, 8, 8]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 4 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R17RS1]  
      rfl
    g := ![![![-64, 3, 203], ![-15, -270, 0]], ![![-3826, 225, 12155], ![-899, -16207, 0]]]
    h := ![![![-297, -1761, 881], ![-13, -4992, 0]], ![![-334, -1987, 994], ![-11, -5632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![8, 2, 1]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E17RS1
                    

noncomputable def R23RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![-8, 0, 1] ![![2, 0, 0], ![1, 1, 0]]
  ![![-16, 0, 2], ![22, -8, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E23RS1 : IdealEqCertificateO timesTableO (Ideal.span {2} * I23N1) (Ideal.span {B.equivFun.symm ![-8, 0, 1]} * (J0 ^ 1*J1^ 0)) 
      ![![46, 0, 0], ![2, 2, 0]] ![![-16, 0, 2], ![22, -8, 2]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R23RS1]  
      rfl
    g := ![![![9, 0, 2], ![5, 0, 0]], ![![1, 0, 5], ![1, -3, 0]]]
    h := ![![![0, 0, -1], ![0, 8, 0]], ![![0, 0, 2], ![-4, -15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-8, 0, 1]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E23RS1
                    

noncomputable def R29RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![0, 2, 1] ![![12, 0, 0], ![2, 1, 1]]
  ![![0, 24, 12], ![108, 12, 12]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E29RS1 : IdealEqCertificateO timesTableO (Ideal.span {12} * I29N1) (Ideal.span {B.equivFun.symm ![0, 2, 1]} * (J0 ^ 2*J1^ 2)) 
      ![![348, 0, 0], ![-108, 12, 0]] ![![0, 24, 12], ![108, 12, 12]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R29RS1]  
      rfl
    g := ![![![0, -267, 93], ![12, -667, 386]], ![![0, 87, -39], ![95, 230, -137]]]
    h := ![![![5, 3, -1], ![15, 10, 0]], ![![-20, -247, 74], ![14, -715, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {12} * I29N1 =  Ideal.span {B.equivFun.symm ![0, 2, 1]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E29RS1
                    

noncomputable def R31RS0 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-2, -2, 1] ![![6, 0, 0], ![2, 1, 1]]
  ![![-12, -12, 6], ![-12, 6, -6]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E31RS0 : IdealEqCertificateO timesTableO (Ideal.span {6} * I31N0) (Ideal.span {B.equivFun.symm ![-2, -2, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![186, 0, 0], ![24, 6, 0]] ![![-12, -12, 6], ![-12, 6, -6]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R31RS0]  
      rfl
    g := ![![![-1482, 28, -143], ![-511, 341, 0]], ![![-193, 3, -19], ![-63, 44, 0]]]
    h := ![![![74, -234, -233], ![28, 2408, 0]], ![![90, -284, -283], ![33, 2924, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {6} * I31N0 =  Ideal.span {B.equivFun.symm ![-2, -2, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E31RS0
                    

noncomputable def R31RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-4, 0, 1] ![![6, 0, 0], ![2, 1, 1]]
  ![![-24, 0, 6], ![42, 6, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E31RS1 : IdealEqCertificateO timesTableO (Ideal.span {6} * I31N1) (Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![186, 0, 0], ![42, 6, 0]] ![![-24, 0, 6], ![42, 6, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R31RS1]  
      rfl
    g := ![![![-1478, 29, -142], ![-510, 341, 0]], ![![-287, 5, -28], ![-95, 66, 0]]]
    h := ![![![207, -1283, -641], ![29, 6624, 0]], ![![-368, 2208, 1104], ![1, -11408, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {6} * I31N1 =  Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E31RS1
                    

noncomputable def R31RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![6, 2, 1] ![![6, 0, 0], ![2, 1, 1]]
  ![![36, 12, 6], ![120, 18, 18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E31RS2 : IdealEqCertificateO timesTableO (Ideal.span {6} * I31N2) (Ideal.span {B.equivFun.symm ![6, 2, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![186, 0, 0], ![-66, 6, 0]] ![![36, 12, 6], ![120, 18, 18]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 6 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R31RS2]  
      rfl
    g := ![![![1475, -29, 143], ![511, -341, 0]], ![![-523, 10, -51], ![-180, 121, 0]]]
    h := ![![![-450, -5428, 1357], ![6, -14022, 0]], ![![-1533, -18335, 4584], ![-16, -47367, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {6} * I31N2 =  Ideal.span {B.equivFun.symm ![6, 2, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E31RS2
                    

noncomputable def R41RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-28, -6, -5] ![![12, 0, 0], ![2, 1, 1]]
  ![![-336, -72, -60], ![-480, -84, -72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E41RS1 : IdealEqCertificateO timesTableO (Ideal.span {12} * I41N1) (Ideal.span {B.equivFun.symm ![-28, -6, -5]} * (J0 ^ 2*J1^ 2)) 
      ![![492, 0, 0], ![108, 12, 0]] ![![-336, -72, -60], ![-480, -84, -72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 12 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R41RS1]  
      rfl
    g := ![![![-4517, -94, -576], ![-803, 1927, 0]], ![![-993, -21, -127], ![-170, 423, 0]]]
    h := ![![![10599, -85273, -31975], ![267, 436990, 0]], ![![15161, -121969, -45735], ![378, 625043, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {12} * I41N1 =  Ideal.span {B.equivFun.symm ![-28, -6, -5]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E41RS1
                    
