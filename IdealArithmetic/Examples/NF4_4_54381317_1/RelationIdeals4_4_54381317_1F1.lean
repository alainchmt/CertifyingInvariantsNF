import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F1
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R43RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![611, 285, 14, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![5499, 2565, 126, -36], ![-2754, -1287, -63, 18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E43RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I43N1) (Ideal.span {B.equivFun.symm ![611, 285, 14, -4]} * (J0 ^ 0*J1^ 2)) 
      ![![387, 0, 0, 0], ![9, 9, 0, 0]] ![![5499, 2565, 126, -36], ![-2754, -1287, -63, 18]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R43RS1]  
      rfl
    g := ![![![-108350, -4605715, 2330108, -77], ![-487659, -20969586, 692, 0]], ![![-5637, -239602, 121218, -4], ![-25364, -1090890, 36, 0]]]
    h := ![![![42, 26, -9, -1], ![-1195, 362, 39, 0]], ![![-24, -18, 2, 0], ![726, -95, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![611, 285, 14, -4]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E43RS1
                    

noncomputable def R43RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![-617, -331, -21, 5] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![-5553, -2979, -189, 45], ![4383, 2367, 153, -36]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E43RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I43N2) (Ideal.span {B.equivFun.symm ![-617, -331, -21, 5]} * (J0 ^ 2*J1^ 0)) 
      ![![387, 0, 0, 0], ![-162, 9, 0, 0]] ![![-5553, -2979, -189, 45], ![4383, 2367, 153, -36]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R43RS2]  
      rfl
    g := ![![![345227441000655577, 8371765444265898356, -2114518076140398309, 2845685], ![776761742251475126, 19030662685161140120, -25611163, 0]], ![![-148528042290053000, -3601805025533785602, 909734259031471940, -1224306], ![-334188095152619287, -8187608331239172444, 11018753, 0]]]
    h := ![![![-8525, 92672, -5895, 43], ![-20331, 220272, -1844, 0]], ![![6799, -73096, 4669, -35], ![16215, -173732, 1501, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {9} * I43N2 =  Ideal.span {B.equivFun.symm ![-617, -331, -21, 5]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E43RS2
                    

noncomputable def R53RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![-167, -81, -5, 1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![-1503, -729, -45, 9], ![2268, 891, 45, -9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E53RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I53N1) (Ideal.span {B.equivFun.symm ![-167, -81, -5, 1]} * (J0 ^ 1*J1^ 2)) 
      ![![477, 0, 0, 0], ![-90, 9, 0, 0]] ![![-1503, -729, -45, 9], ![2268, 891, 45, -9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R53RS1]  
      rfl
    g := ![![![77585103533, -217994268778, 57711631980, 9519425026], ![1828088918345, 672548226768, -144, 0]], ![![-14546639313, 40872331201, -10820508922, -1784822574], ![-342753302590, -126097873886, 27, 0]]]
    h := ![![![-619, 21, -13566, 1357], ![-3264, -207, -71920, 0]], ![![964, -35, 17884, -1789], ![5084, 313, 94816, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {9} * I53N1 =  Ideal.span {B.equivFun.symm ![-167, -81, -5, 1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E53RS1
                    

noncomputable def R53RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![440, 280, 27, -5] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![3960, 2520, 243, -45], ![-27180, -17928, -1980, 342]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E53RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I53N2) (Ideal.span {B.equivFun.symm ![440, 280, 27, -5]} * (J0 ^ 2*J1^ 1)) 
      ![![477, 0, 0, 0], ![-9, 9, 0, 0]] ![![3960, 2520, 243, -45], ![-27180, -17928, -1980, 342]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R53RS2]  
      rfl
    g := ![![![42050648969782676, -42483001075558431, -8955645521145908, 1130415901898480], ![-29534810293286745, -4889587746948478, 52, 0]], ![![1617318077361816, -1633946854647971, -344444800511923, 43477142871004], ![-1135944004885864, -188059372393260, 2, 0]]]
    h := ![![![27, -439, 427, -1], ![991, -22556, 48, 0]], ![![-174, 3002, -2927, 1], ![-6202, 154896, -15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {9} * I53N2 =  Ideal.span {B.equivFun.symm ![440, 280, 27, -5]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E53RS2
                    

noncomputable def R61RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 2) ![53, 17, -2, 0] ![![9, 0, 0, 0], ![-128, -67, -4, 1]]
  ![![477, 153, -18, 0], ![2025, 1143, 81, -18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_2
    hmul := by decide

noncomputable def E61RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I61N1) (Ideal.span {B.equivFun.symm ![53, 17, -2, 0]} * (J0 ^ 2*J1^ 2)) 
      ![![549, 0, 0, 0], ![-72, 9, 0, 0]] ![![477, 153, -18, 0], ![2025, 1143, 81, -18]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R61RS1]  
      rfl
    g := ![![![53, -179, -51, 1], ![1147, 399, 0, 0]], ![![99, 80, 10, -1], ![-134, -50, 0, 0]]]
    h := ![![![193, -8, 5150, -644], ![1465, 120, 39284, 0]], ![![1533, -25470, 3216, -7], ![11661, -192767, 425, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![53, 17, -2, 0]} * (J0 ^ 2*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E61RS1
                    
