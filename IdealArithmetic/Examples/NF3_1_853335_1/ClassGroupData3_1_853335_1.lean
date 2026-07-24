import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_853335_1.RI3_1_853335_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![14791, -938, -57]

def alpha1 := B.equivFun.symm ![-27, -2, -2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![683074293, 403526284, -316232396]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-3, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-3, 0, 1]] ![![2, 0, 0], ![-3, 0, 1]]
  ![![4, 0, 0], ![-1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-6, 0, 2]], ![![-6, 0, 2], ![101, 16, -1]]]
 hmul := by decide
 f := ![![![![-1002, 0, -641], ![1184, 32, 0]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![252, 0, 160], ![-295, -8, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![2, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![-2018, -32, -153], ![467, 48, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-1, 0, 1]] ![![2, 0, 0], ![-3, 0, 1]]
  ![![8, 0, 0], ![-1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-12, 0, 4]], ![![-2, 0, 2], ![95, 16, 1]]]
 hmul := by decide
 f := ![![![![-8484, 0, 1629], ![13544, 320, 0]], ![![-34944, -192, 0], ![-8, 0, 0]]], ![![![1062, 0, -204], ![-1692, -40, 0]], ![![4368, 24, 0], ![1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![4, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-1052, -16, -34], ![129, 48, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![-1, 0, 1]] ![![2, 0, 0], ![-3, 0, 1]]
  ![![16, 0, 0], ![-1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![-24, 0, 8]], ![![-2, 0, 2], ![95, 16, 1]]]
 hmul := by decide
 f := ![![![![16407, 0, -5708], ![-27462, -640, 0]], ![![160512, 896, 0], ![-16, 0, 0]]], ![![![-1023, 0, 356], ![1718, 40, 0]], ![![-10032, -56, 0], ![1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![8, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-1966, -32, -41], ![129, 176, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-1, 0, 1]] ![![2, 0, 0], ![-3, 0, 1]]
  ![![32, 0, 0], ![-17, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![-48, 0, 16]], ![![-2, 0, 2], ![95, 16, 1]]]
 hmul := by decide
 f := ![![![![6450, 0, -2773], ![-11060, -256, 0]], ![![136704, 768, 0], ![-32, 0, 0]]], ![![![-3426, 0, 1473], ![5876, 136, 0]], ![![-72624, -408, 0], ![17, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![7, 0, 0], ![16, 0, 0]]], ![![![1, 0, 0], ![2, 0, 0]], ![![360, -32, 13], ![-175, -80, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-17, 0, 1]] ![![2, 0, 0], ![-3, 0, 1]]
  ![![14791, -938, -57]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![-96, 0, 32]], ![![-34, 0, 2], ![143, 16, -15]]]
 hmul := by decide
 f := ![![![![104060683707, 0, 48700277284], ![-131740886918, -78567440, 0]], ![![553492683576, -98209300, 0], ![-2457343, 938, 0]]]]
 g := ![![![![149876356, 11232944, 11709015]], ![![1324765116, 99288592, 103496609]]], ![![![17226914, 1291124, 1345844]], ![![152269613, 11412314, 11895987]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![10, -7, 12]]]
 hmul := by decide
 f := ![![![![-1525, 6425, -13632], ![1900, 3250, 0]], ![![0, 0, 0], ![11850, -75, 0]]], ![![![-510, 2076, -4416], ![621, 1062, 0]], ![![0, 0, 0], ![3794, -24, 0]]]]
 g := ![![![![1417, 1299, 3168], ![525, -6600, 0]], ![![-586, -532, -1296], ![-195, 2700, 0]]], ![![![-586, -532, -1296], ![-195, 2700, 0]], ![![586, 536, 1308], ![213, -2724, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![8, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![-27, -2, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![40, 5, 0], ![-10, 3, 12]]]
 hmul := by decide
 f := ![![![![-161823683, 139036671, -380810530], ![92536811, 158634528, 0]], ![![26347351, 183474, 0], ![-4702, 81, 0]]]]
 g := ![![![![-47, 6, -2]], ![![-46, -17, 14]]], ![![![-28, -1, 2]], ![![82, -3, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![12855782501060657405, 963516119329946340, 1004351547918197852])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-3, 0, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![10, 0, 0], ![-7, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![-4, 2, 0]], ![![-15, 0, 5], ![186, 1, 1]]]
 hmul := by decide
 f := ![![![![326, -283, 763], ![-185, -320, 0]], ![![10, 0, 0], ![0, 0, 0]]], ![![![-226, 197, -534], ![135, 224, 0]], ![![-7, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![176, -4, 15], ![-108, -14, 0]]], ![![![2, 0, 0], ![5, 0, 0]], ![![104, -2, 8], ![-58, -7, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-7, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![-3, 0, 1]] ![![25, 0, 0], ![8, 1, 0]]
  ![![50, 0, 0], ![-7, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![16, 2, 0]], ![![-75, 0, 25], ![156, 1, 11]]]
 hmul := by decide
 f := ![![![![108116, 98777, 240743], ![38575, -501600, 0]], ![![50, 0, 0], ![0, 0, 0]]], ![![![-15138, -13829, -33704], ![-5395, 70224, 0]], ![![-7, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![123, -2, 2], ![2, -34, 0]]], ![![![2, 0, 0], ![25, 0, 0]], ![![66, -1, 1], ![12, -17, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-7, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-1, 0, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![20, 0, 0], ![3, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![-8, 4, 0]], ![![-5, 0, 5], ![182, 3, 1]]]
 hmul := by decide
 f := ![![![![326, -283, 753], ![-185, -320, 0]], ![![60, 0, 0], ![0, 0, 0]]], ![![![50, -43, 113], ![-25, -48, 0]], ![![9, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-2, 0, -1], ![20, 0, 0]], ![![-109, -4, -2], ![4, 12, 0]]], ![![![-1, 0, 0], ![5, 0, 0]], ![![-71, -3, -1], ![-6, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-1, 0, 1]] ![![25, 0, 0], ![8, 1, 0]]
  ![![100, 0, 0], ![43, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![32, 4, 0]], ![![-25, 0, 25], ![172, 3, 11]]]
 hmul := by decide
 f := ![![![![108116, 98777, 240693], ![38575, -501600, 0]], ![![300, 0, 0], ![0, 0, 0]]], ![![![46489, 42474, 103498], ![16590, -215688, 0]], ![![129, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-42, 0, -1], ![100, 0, 0]], ![![-513, -156, -8], ![-196, 332, 0]]], ![![![-11, 0, 0], ![25, 0, 0]], ![![-388, -117, -6], ![-136, 249, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![43, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![-1, 0, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![40, 0, 0], ![-17, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![40, 0, 0], ![-16, 8, 0]], ![![-5, 0, 5], ![182, 3, 1]]]
 hmul := by decide
 f := ![![![![-488, 424, -1127], ![280, 480, 0]], ![![-200, 0, 0], ![0, 0, 0]]], ![![![209, -181, 479], ![-115, -204, 0]], ![![85, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1131, -96, 34], ![-472, -296, 0]]], ![![![2, 0, 0], ![5, 0, 0]], ![![442, -36, 12], ![-146, -111, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![40, 0, 0], ![-17, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![-1, 0, 1]] ![![25, 0, 0], ![8, 1, 0]]
  ![![200, 0, 0], ![-57, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![200, 0, 0], ![64, 8, 0]], ![![-25, 0, 25], ![172, 3, 11]]]
 hmul := by decide
 f := ![![![![250384, 228748, 557393], ![89300, -1161600, 0]], ![![1400, 0, 0], ![0, 0, 0]]], ![![![-71366, -65194, -158857], ![-25430, 331056, 0]], ![![-399, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![788, -248, 15], ![-192, -936, 0]]], ![![![7, 0, 0], ![25, 0, 0]], ![![335, -93, 5], ![64, -351, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![200, 0, 0], ![-57, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![-1, 0, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![80, 0, 0], ![-17, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![80, 0, 0], ![-32, 16, 0]], ![![-5, 0, 5], ![182, 3, 1]]]
 hmul := by decide
 f := ![![![![-1300, 1130, -3007], ![750, 1280, 0]], ![![-1040, 0, 0], ![0, 0, 0]]], ![![![278, -241, 639], ![-155, -272, 0]], ![![221, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1284, -96, 25], ![-224, -592, 0]]], ![![![1, 0, 0], ![5, 0, 0]], ![![255, -18, 4], ![14, -111, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![80, 0, 0], ![-17, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![-1, 0, 1]] ![![25, 0, 0], ![8, 1, 0]]
  ![![400, 0, 0], ![143, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![400, 0, 0], ![128, 16, 0]], ![![-25, 0, 25], ![172, 3, 11]]]
 hmul := by decide
 f := ![![![![250384, 228748, 557393], ![89300, -1161600, 0]], ![![2800, 0, 0], ![0, 0, 0]]], ![![![89509, 81777, 199268], ![31935, -415272, 0]], ![![1001, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-142, 0, -1], ![400, 0, 0]], ![![-1900, -1664, -33], ![-384, 4528, 0]]], ![![![-9, 0, 0], ![25, 0, 0]], ![![-476, -312, -7], ![264, 849, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![400, 0, 0], ![143, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-17, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![-17, 0, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![160, 0, 0], ![-17, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![160, 0, 0], ![-64, 32, 0]], ![![-85, 0, 5], ![214, -13, 1]]]
 hmul := by decide
 f := ![![![![5206, -4523, 12273], ![-2985, -5120, 0]], ![![480, 0, 0], ![0, 0, 0]]], ![![![-552, 480, -1304], ![320, 544, 0]], ![![-51, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1318, -96, 23], ![-128, -1184, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![-523, 39, -10], ![158, 481, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![160, 0, 0], ![-17, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![-17, 0, 1]] ![![25, 0, 0], ![8, 1, 0]]
  ![![800, 0, 0], ![143, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![800, 0, 0], ![256, 32, 0]], ![![-425, 0, 25], ![44, -13, 11]]]
 hmul := by decide
 f := ![![![![4233896, 3867937, 9427793], ![1509575, -19641600, 0]], ![![5600, 0, 0], ![0, 0, 0]]], ![![![756803, 691393, 1685218], ![269855, -3510936, 0]], ![![1001, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-142, 0, -1], ![800, 0, 0]], ![![-2043, -1664, -34], ![32, 9056, 0]]], ![![![-5, 0, 0], ![25, 0, 0]], ![![712, 676, 13], ![648, -3679, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![800, 0, 0], ![143, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
