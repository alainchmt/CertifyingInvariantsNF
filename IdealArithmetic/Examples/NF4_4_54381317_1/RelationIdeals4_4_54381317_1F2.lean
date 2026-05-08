import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F2
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R97RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![102, 83, 14, -2] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![918, 747, 126, -18], ![-5013, -2826, -207, 45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E97RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I97N1) (Ideal.span {B.equivFun.symm ![102, 83, 14, -2]} * (J0 ^ 2*J1^ 2)) 
      ![![873, 0, 0, 0], ![-378, 9, 0, 0]] ![![918, 747, 126, -18], ![-5013, -2826, -207, 45]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R97RS1]  
      rfl
    g := ![![![22, 646, 189, -1], ![-4850, -1620, 0, 0]], ![![51, -242, -78, 0], ![2064, 688, 0, 0]]]
    h := ![![![86754, -1062553, 29365, -98], ![200358, -2449223, 9504, 0]], ![![-474071, 5864779, -161837, 535], ![-1094865, 13518786, -51890, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {9} * I97N1 =  Ideal.span {B.equivFun.symm ![102, 83, 14, -2]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E97RS1
                    

noncomputable def R97RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![-40, -4, 1, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![-360, -36, 9, 0], ![2439, 1251, 72, -18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E97RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I97N2) (Ideal.span {B.equivFun.symm ![-40, -4, 1, 0]} * (J0 ^ 2*J1^ 2)) 
      ![![873, 0, 0, 0], ![-225, 9, 0, 0]] ![![-360, -36, 9, 0], ![2439, 1251, 72, -18]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R97RS2]  
      rfl
    g := ![![![-1689, -451046, -131808, 1010], ![3440787, 1149971, 0, 0]], ![![442, 111608, 32612, -250], ![-851317, -284526, 0, 0]]]
    h := ![![![-9970, 174, -105241, 4210], ![-38682, -872, -408370, 0]], ![![67793, 804, 1462509, -58506], ![263026, 13635, 5675080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {9} * I97N2 =  Ideal.span {B.equivFun.symm ![-40, -4, 1, 0]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E97RS2
                    
