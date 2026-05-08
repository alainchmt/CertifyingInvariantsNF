import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F10
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

    set_option linter.all false

    noncomputable section

noncomputable def R557RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![-988, -512, -24, 7] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![-8892, -4608, -216, 63], ![6633, 3384, 144, -45]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E557RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I557N1) (Ideal.span {B.equivFun.symm ![-988, -512, -24, 7]} * (J0 ^ 2*J1^ 0)) 
      ![![5013, 0, 0, 0], ![1026, 9, 0, 0]] ![![-8892, -4608, -216, 63], ![6633, 3384, 144, -45]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R557RS1]  
      rfl
    g := ![![![213423323381151619, 5175515591992912020, -1307217855713868168, 1079578], ![480202477607589509, 11764960701385948688, -9716242, 0]], ![![43489344581652394, 1054616606105067538, -266372235563500078, 219986], ![97851025308717559, 2397350120063581203, -1979882, 0]]]
    h := ![![![-1559216, 377746010, 3446718, 1167], ![7618266, -1845720582, -650012, 0]], ![![1162603, -281784697, -2571292, -872], ![-5680431, 1376839974, 485699, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R557N1 : Ideal.span {9} * I557N1 =  Ideal.span {B.equivFun.symm ![-988, -512, -24, 7]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E557RS1
                    

noncomputable def R557RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![2471, 1140, 56, -16] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![22239, 10260, 504, -144], ![-11070, -5121, -252, 72]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E557RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I557N2) (Ideal.span {B.equivFun.symm ![2471, 1140, 56, -16]} * (J0 ^ 0*J1^ 2)) 
      ![![5013, 0, 0, 0], ![-2457, 9, 0, 0]] ![![22239, 10260, 504, -144], ![-11070, -5121, -252, 72]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R557RS2]  
      rfl
    g := ![![![-1192477948263, -50680312797355, 25638286462864, -5288596], ![-5366150766753, -230744482971120, 47597380, 0]], ![![580979777645, 24691640547881, -12491070371564, 2576624], ![2614408999186, 112419586964880, -23189624, 0]]]
    h := ![![![438886, 38869, 57061758, -209018], ![895447, 82580, 116423010, 0]], ![![-218214, -19166, -28461811, 104256], ![-445216, -40733, -58070584, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R557N2 : Ideal.span {9} * I557N2 =  Ideal.span {B.equivFun.symm ![2471, 1140, 56, -16]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E557RS2
                    

noncomputable def R587RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 0) ![91, 50, 6, -1] ![![9, 0, 0, 0], ![-4, 1, 0, 0]]
  ![![819, 450, 54, -9], ![-747, -441, -54, 9]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_0
    hmul := by decide

noncomputable def E587RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I587N1) (Ideal.span {B.equivFun.symm ![91, 50, 6, -1]} * (J0 ^ 2*J1^ 0)) 
      ![![5283, 0, 0, 0], ![72, 9, 0, 0]] ![![819, 450, 54, -9], ![-747, -441, -54, 9]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R587RS1]  
      rfl
    g := ![![![-142376725173925, -3452635585468477, 872057442783375, -273221], ![-320347631641411, -7848516975214424, 2458990, 0]], ![![-2182906294251, -52935477635685, 13370301069068, -4189], ![-4911539162066, -120332709470808, 37701, 0]]]
    h := ![![![12393, -2299611, -287701, -7], ![-909325, 168847629, 4108, 0]], ![![-11313, 2097194, 262374, 6], ![830081, -153985376, -3521, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R587N1 : Ideal.span {9} * I587N1 =  Ideal.span {B.equivFun.symm ![91, 50, 6, -1]} * (J0 ^ 2*J1^ 0) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E587RS1
                    

noncomputable def R587RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 0*J1^ 2) ![-638, -285, -14, 4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![-5742, -2565, -126, 36], ![2808, 1260, 63, -18]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_0J1_2
    hmul := by decide

noncomputable def E587RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I587N2) (Ideal.span {B.equivFun.symm ![-638, -285, -14, 4]} * (J0 ^ 0*J1^ 2)) 
      ![![5283, 0, 0, 0], ![-2088, 9, 0, 0]] ![![-5742, -2565, -126, 36], ![2808, 1260, 63, -18]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R587RS2]  
      rfl
    g := ![![![139834021474, 5942945898148, -3006436610346, 2578047], ![629253095028, 27057883088313, -23202448, 0]], ![![-53870483701, -2289495551590, 1158217383008, -993182], ![-242417176012, -10423938569814, 8938648, 0]]]
    h := ![![![-3026266, 267170917, -1307445, 672], ![-7656972, 675955481, -394460, 0]], ![![1480536, -130652026, 639687, -330], ![3746010, -330556006, 193708, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R587N2 : Ideal.span {9} * I587N2 =  Ideal.span {B.equivFun.symm ![-638, -285, -14, 4]} * (J0 ^ 0*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E587RS2
                    

noncomputable def R593RS1 : IdealMulPrincipalCertificate timesTableO (J0 ^ 1*J1^ 2) ![77, 63, 5, -1] ![![9, 0, 0, 0], ![-564, -280, -15, 4]]
  ![![693, 567, 45, -9], ![20916, 10557, 585, -153]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_1J1_2
    hmul := by decide

noncomputable def E593RS1 : IdealEqCertificateO timesTableO (Ideal.span {9} * I593N1) (Ideal.span {B.equivFun.symm ![77, 63, 5, -1]} * (J0 ^ 1*J1^ 2)) 
      ![![5337, 0, 0, 0], ![1944, 9, 0, 0]] ![![693, 567, 45, -9], ![20916, 10557, 585, -153]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R593RS1]  
      rfl
    g := ![![![22654906368, -63654484002, 16851837621, 2779678865], ![533803276982, 196384563682, -593, 0]], ![![8252044278, -23186130283, 6138277767, 1012497351], ![194437714087, 71533029658, -216, 0]]]
    h := ![![![7429, -638326, -3387, -2], ![-20395, 1752536, 1185, 0]], ![![224044, -19291714, -99896, -49], ![-615073, 52965753, 29040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R593N1 : Ideal.span {9} * I593N1 =  Ideal.span {B.equivFun.symm ![77, 63, 5, -1]} * (J0 ^ 1*J1^ 2) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E593RS1
                    

noncomputable def R593RS2 : IdealMulPrincipalCertificate timesTableO (J0 ^ 2*J1^ 1) ![239, 130, 9, -2] ![![9, 0, 0, 0], ![-114, -104, -12, 2]]
  ![![2151, 1170, 81, -18], ![2628, 774, -90, 0]] where
    T := Table
    heq := timesTableT_eq_Table
    hI := by exact PowJ0_2J1_1
    hmul := by decide

noncomputable def E593RS2 : IdealEqCertificateO timesTableO (Ideal.span {9} * I593N2) (Ideal.span {B.equivFun.symm ![239, 130, 9, -2]} * (J0 ^ 2*J1^ 1)) 
      ![![5337, 0, 0, 0], ![-2178, 9, 0, 0]] ![![2151, 1170, 81, -18], ![2628, 774, -90, 0]] where 
    T := Table
    heq := timesTableT_eq_Table
    hieq1 := by convert ideal_mul_span_singleton_coe (R := ℤ)  _ _ _ rfl 9 ; decide ; exact {out := by decide}
    hieq2 := by 
      rw [← ideal_eq_principal_mul_of_IdealMulPrincipalCertificate _ _ _ _ _ R593RS2]  
      rfl
    g := ![![![-340785428920066581785, 344289282045299049673, 72578035653457003895, -9161077829343143003], ![239354997852924315112, 39626029524249164804, 15897930, 0]], ![![138304660496277051101, -139726667353934576139, -29455134312366717469, 3717939945326892934], ![-97140044458592611030, -16081862940953997906, -6452030, 0]]]
    h := ![![![36875, 4978, 8371726, -34594], ![90358, 12571, 20514240, 0]], ![![45028, 4408, 7635565, -31552], ![110336, 11257, 18710336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R593N2 : Ideal.span {9} * I593N2 =  Ideal.span {B.equivFun.symm ![239, 130, 9, -2]} * (J0 ^ 2*J1^ 1) := by 
  refine ideal_eq_of_IdealEqCertificateO _ _ _ _ _ E593RS2
                    
