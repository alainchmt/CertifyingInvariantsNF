import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F3
import IdealArithmetic.Examples.NF5_1_3790297_2.ClassGroupData5_1_3790297_2

    set_option linter.all false

    noncomputable section

noncomputable def R113RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 1) ![-4, -1, 2, 1, -5] ![![2, 0, 0, 0, 0], ![-2, 0, 1, 1, -4]]
  ![![-8, -2, 4, 2, -10], ![12, -4, 0, 0, 2]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_1
    hmul := by decide

noncomputable def E113RS1 : IdealEqCertificateO timesTableO (Ideal.span {2} * I113N1) (Ideal.span {B.equivFun.symm ![-4, -1, 2, 1, -5]} * (J0 ^ 0*J1^ 1)) 
      ![![226, 0, 0, 0, 0], ![78, 2, 0, 0, 0]] ![![-8, -2, 4, 2, -10], ![12, -4, 0, 0, 2]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R113RS1]  
      rfl
    g := ![![![-256, 170, -216, -44, 187], ![-236, -339, 0, 0, 0]], ![![-90, 60, -77, -16, 68], ![-83, -120, 0, 0, 0]]]
    h := ![![![-4610847, 73400843, 2078891, 26319, 9195], ![13352973, -213024947, -571266, -64940, 0]], ![![5286654, -84161638, -2383729, -30179, -10543], ![-15310104, 244255064, 655207, 74460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {2} * I113N1 =  Ideal.span {B.equivFun.symm ![-4, -1, 2, 1, -5]} * (J0 ^ 0*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E113RS1
                    

noncomputable def R113RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 0) ![-1, 0, 0, 1, -2] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![-2, 0, 0, 2, -4], ![-2, -2, -4, -2, 10]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_0
    hmul := by decide

noncomputable def E113RS2 : IdealEqCertificateO timesTableO (Ideal.span {2} * I113N2) (Ideal.span {B.equivFun.symm ![-1, 0, 0, 1, -2]} * (J0 ^ 1*J1^ 0)) 
      ![![226, 0, 0, 0, 0], ![-8, 2, 0, 0, 0]] ![![-2, 0, 0, 2, -4], ![-2, -2, -4, -2, 10]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 2 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R113RS2]  
      rfl
    g := ![![![-49001, -78294, -97786, -146787, 146734], ![-39147, 97754, 293601, 0, -97867]], ![![1581, 2525, 3154, 4735, -4733], ![1264, -3153, -9471, 0, 3157]]]
    h := ![![![-63413, 852161, -209412, 6, 158], ![-1790301, 23627368, -7373, -1116, 0]], ![![-188165, 2528588, -621382, 18, 469], ![-5312349, 70108664, -21907, -3312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {2} * I113N2 =  Ideal.span {B.equivFun.symm ![-1, 0, 0, 1, -2]} * (J0 ^ 1*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E113RS2
                    
