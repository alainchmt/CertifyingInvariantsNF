import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_466627_2.RI3_1_466627_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![5, -3, 0]

def alpha1 := B.equivFun.symm ![-33, -11, -2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-6, 1, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2, -1], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, -47, -17], ![0, -32, 0]], ![![0, 0, 0], ![134, -1, 0]]]]
 g := ![![![![0, -1, 0], ![4, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, 0, 1], ![0, 0, 0]], ![![0, -8, 0], ![8, 0, 0]]], ![![![0, -3, 12], ![0, 6, 0]], ![![0, -126, 0], ![134, -1, 0]]]]
 g := ![![![![0, -1, 0], ![8, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![-7, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, 0, 1], ![0, 0, 0]], ![![0, -16, 0], ![16, 0, 0]]], ![![![0, -2, 5], ![0, 4, 0]], ![![0, -118, 0], ![126, -1, 0]]]]
 g := ![![![![78, -11, 0], ![176, 0, 0]], ![![46, -6, 0], ![104, 0, 0]]], ![![![22, -3, 0], ![50, 0, 0]], ![![11, -1, 0], ![25, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-7, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![-14, 2, 0], ![-7, -6, 1]]]
 hmul := by decide
 f := ![![![![-1110, -132, -221], ![556, 380, 0]], ![![-1920, 480, 0], ![32, 0, 0]]], ![![![-4924, -605, -972], ![2464, 1676, 0]], ![![-8520, 2070, 0], ![142, -1, 0]]]]
 g := ![![![![118, 13, 0], ![-416, 0, 0]], ![![68, 8, 0], ![-240, 0, 0]]], ![![![-64, -16, -1], ![226, 32, 0]], ![![-41, -14, -1], ![145, 33, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![9, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![64, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![18, 2, 0], ![9, 10, 1]]]
 hmul := by decide
 f := ![![![![-2988, 13345, -1666], ![1496, 7334, 0]], ![![8000, -64000, 0], ![-64, 0, 0]]], ![![![-5134, 22870, -2857], ![2568, 12574, 0]], ![![13750, -109700, 0], ![-110, -1, 0]]]]
 g := ![![![![1128, -49, 0], ![3136, 0, 0]], ![![564, -24, 0], ![1568, 0, 0]]], ![![![346, -15, 0], ![962, 0, 0]], ![![196, -8, 0], ![545, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![-23, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![128, 0, 0], ![41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![64, 64, 0]], ![![-46, 2, 0], ![-23, -22, 1]]]
 hmul := by decide
 f := ![![![![-5120, 76461, -19554], ![2560, 31014, 0]], ![![-10752, 258944, 0], ![128, 0, 0]]], ![![![3680, -54967, 14057], ![-1840, -22295, 0]], ![![7728, -186151, 0], ![-92, 1, 0]]]]
 g := ![![![![862, 21, 0], ![-2688, 0, 0]], ![![390, 10, 0], ![-1216, 0, 0]]], ![![![-370, -50, -1], ![1154, 128, 0]], ![![-226, -47, -1], ![705, 129, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![41, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![256, 0, 0], ![-87, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![256, 0, 0], ![128, 128, 0]], ![![82, 2, 0], ![41, 42, 1]]]
 hmul := by decide
 f := ![![![![-57344, 834455, -158200], ![28672, 366802, 0]], ![![134400, -3225600, 0], ![-256, 0, 0]]], ![![![-10304, 149755, -28394], ![5152, 65834, 0]], ![![24150, -578900, 0], ![-46, -1, 0]]]]
 g := ![![![![12268, -141, 0], ![36096, 0, 0]], ![![6134, -70, 0], ![18048, 0, 0]]], ![![![3916, -45, 0], ![11522, 0, 0]], ![![2045, -23, 0], ![6017, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![256, 0, 0], ![-87, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![512, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![512, 0, 0], ![256, 256, 0]], ![![-174, 2, 0], ![-87, -86, 1]]]
 hmul := by decide
 f := ![![![![-2357932, 34618390, -7785933], ![1178968, 14595196, 0]], ![![-5203968, 125013504, 0], ![512, 0, 0]]], ![![![-165792, 2431679, -546937], ![82896, 1025269, 0]], ![![-365904, 8781465, 0], ![36, 1, 0]]]]
 g := ![![![![35998, 213, 0], ![-109056, 0, 0]], ![![17830, 106, 0], ![-54016, 0, 0]]], ![![![-12338, -242, -1], ![37378, 512, 0]], ![![-6507, -208, -1], ![19713, 513, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![512, 0, 0], ![169, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![1024, 0, 0], ![-343, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![1024, 0, 0], ![512, 512, 0]], ![![338, 2, 0], ![169, 170, 1]]]
 hmul := by decide
 f := ![![![![-15667200, 1480711106, -290820813], ![7833600, 602778748, 0]], ![![35599360, -5411102720, 0], ![-1024, 0, 0]]], ![![![3213000, -303671796, 59642995], ![-1606500, -123620898, 0]], ![![-7300650, 1109736428, 0], ![210, -1, 0]]]]
 g := ![![![![261710, -763, 0], ![781312, 0, 0]], ![![131198, -382, 0], ![391680, 0, 0]]], ![![![86780, -253, 0], ![259074, 0, 0]], ![![43390, -126, 0], ![129537, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![1024, 0, 0], ![-343, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2048, 0, 0], ![681, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![2048, 0, 0], ![1024, 1024, 0]], ![![-686, 2, 0], ![-343, -342, 1]]]
 hmul := by decide
 f := ![![![![-16203776, 4128501527, -840506232], ![8101888, 1652099538, 0]], ![![-36282368, 14803417088, 0], ![2048, 0, 0]]], ![![![-4335776, 1104691951, -224900119], ![2167888, 442063805, 0]], ![![-9708368, 3961053593, 0], ![548, 1, 0]]]]
 g := ![![![![244480, 359, 0], ![-735232, 0, 0]], ![![122240, 180, 0], ![-367616, 0, 0]]], ![![![-82402, -802, -1], ![247810, 2048, 0]], ![![-41882, -743, -1], ![125953, 2049, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![2048, 0, 0], ![681, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![5, -3, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![4096, 0, 0], ![2048, 2048, 0]], ![![1362, 2, 0], ![681, 682, 1]]]
 hmul := by decide
 f := ![![![![24362858, -6201450066, 1236404969], ![-12181428, -2494703976, 0]], ![![-54950786, 22419493692, 0], ![394, 3, 0]]]]
 g := ![![![![101, -15, -9]], ![![-548, -20, -12]]], ![![![33, -5, -3]], ![![-183, -7, -4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow12 : J0 ^ 12 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![24, 0, 0], ![1, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![576, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![576, 0, 0], ![24, 24, 0]], ![![24, 24, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -39066, -56455], ![-462567, 1587057, 2930]], ![![0, -235008, 1172], ![408, -14976, 0]]], ![![![0, -11430, -16537], ![-135852, 464792, 860]], ![![0, -68748, 344], ![122, -4381, 0]]]]
 g := ![![![![42420, 251, 0], ![-144576, 0, 0]], ![![1514, 9, 0], ![-5160, 0, 0]]], ![![![1514, 9, 0], ![-5160, 0, 0]], ![![-120, -1, 0], ![409, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![576, 0, 0], ![169, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![-33, -11, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![13824, 0, 0], ![576, 576, 0]], ![![4056, 24, 0], ![169, 170, 1]]]
 hmul := by decide
 f := ![![![![-2590923325, -2590923325, -2568970176], ![-215910264, 61653060403, 0]], ![![8861173200, 53275475, 0], ![2187944, 715, 0]]]]
 g := ![![![![899, -169, 1]], ![![43, 31, -7]]], ![![![264, -48, 0]], ![![11, 9, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![22, 6, 1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![576, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![48, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![48, 0, 0], ![2, 2, 0]], ![![24, 24, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2, -1], ![0, 0, 0]], ![![0, 0, 0], ![48, 0, 0]]], ![![![0, -5, -3], ![0, 18, 0]], ![![0, 0, 0], ![110, -1, 0]]]]
 g := ![![![![760, -33, 0], ![1584, 0, 0]], ![![70, -3, 0], ![146, 0, 0]]], ![![![380, -16, 0], ![792, 0, 0]], ![![35, -1, 0], ![73, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![1152, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1152, 0, 0], ![338, 2, 0]], ![![576, 576, 0], ![169, 170, 1]]]
 hmul := by decide
 f := ![![![![17468686, 116716, 79], ![-59537664, -44928, 0]], ![![0, 0, 0], ![-1152, 0, 0]]], ![![![4579356, 30452, 20], ![-15607594, -11284, 0]], ![![0, 0, 0], ![-302, -1, 0]]]]
 g := ![![![![62024, 367, 0], ![-422784, 0, 0]], ![![17914, 106, 0], ![-122110, 0, 0]]], ![![![31012, 184, 0], ![-211392, 0, 0]], ![![8788, 52, 0], ![-59903, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1152, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![1, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![96, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![96, 0, 0], ![4, 4, 0]], ![![24, 24, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -503, -262], ![0, -24, 0]], ![![0, 0, 0], ![25632, -192, 0]]], ![![![0, 123, 64], ![0, 9, 0]], ![![0, 0, 0], ![-6274, 47, 0]]]]
 g := ![![![![1864, -81, 0], ![7776, 0, 0]], ![![116, -5, 0], ![484, 0, 0]]], ![![![466, -20, 0], ![1944, 0, 0]], ![![29, -1, 0], ![121, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![1, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![2304, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![2304, 0, 0], ![676, 4, 0]], ![![576, 576, 0], ![169, 170, 1]]]
 hmul := by decide
 f := ![![![![30238714474, 202026420, 137019], ![-103061665152, -78265728, 0]], ![![0, 0, 0], ![-1845504, -4608, 0]]], ![![![2211493036, 14774962, 10020], ![-7537362574, -5723455, 0]], ![![0, 0, 0], ![-134970, -337, 0]]]]
 g := ![![![![67094, 397, 0], ![-914688, 0, 0]], ![![19604, 116, 0], ![-267260, 0, 0]]], ![![![16520, 98, 0], ![-225216, 0, 0]], ![![4732, 28, 0], ![-64511, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2304, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![1, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![192, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![192, 0, 0], ![8, 8, 0]], ![![24, 24, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2506, -1305], ![0, -144, 0]], ![![0, 0, 0], ![255552, -1920, 0]]], ![![![0, 306, 159], ![0, 35, 0]], ![![0, 0, 0], ![-31278, 235, 0]]]]
 g := ![![![![3980, -173, 0], ![33216, 0, 0]], ![![208, -9, 0], ![1736, 0, 0]]], ![![![532, -23, 0], ![4440, 0, 0]], ![![26, -1, 0], ![217, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![192, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![1, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![4608, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4608, 0, 0], ![1352, 8, 0]], ![![576, 576, 0], ![169, 170, 1]]]
 hmul := by decide
 f := ![![![![730118313800, 4876397391, 3292640], ![-2488445213184, -1890214848, 0]], ![![0, 0, 0], ![-42932736, -46080, 0]]], ![![![26698179252, 178314722, 120401], ![-90994781400, -69118930, 0]], ![![0, 0, 0], ![-1569918, -1685, 0]]]]
 g := ![![![![68446, 405, 0], ![-1866240, 0, 0]], ![![19942, 118, 0], ![-543736, 0, 0]]], ![![![8260, 49, 0], ![-225216, 0, 0]], ![![2197, 13, 0], ![-59903, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4608, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-7, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![-7, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![384, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![384, 0, 0], ![16, 16, 0]], ![![-168, 24, 0], ![-7, -6, 1]]]
 hmul := by decide
 f := ![![![![-40237504, -14735713, -396848], ![481173504, 1046040, 0]], ![![-45999360, 5800320, 0], ![-3577728, -3840, 0]]], ![![![-17656340, -6466076, -174139], ![211140408, 459024, 0]], ![![-20184660, 2545200, 0], ![-1569918, -1685, 0]]]]
 g := ![![![![3888, 23, 0], ![-8832, 0, 0]], ![![162, 1, 0], ![-368, 0, 0]]], ![![![-1870, -180, -1], ![4248, 384, 0]], ![![-261, -2, 0], ![593, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![384, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![-7, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![9216, 0, 0], ![-4439, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![9216, 0, 0], ![2704, 16, 0]], ![![-4032, 576, 0], ![-1183, 162, 1]]]
 hmul := by decide
 f := ![![![![3859448679932, 25773827206, 17382219], ![-13154083317504, -10011724416, 0]], ![![0, 0, 0], ![31878144, -239616, 0]]], ![![![-1859160357932, -12415679689, -8373304], ![6336539821348, 4822814170, 0]], ![![0, 0, 0], ![-15356230, 115427, 0]]]]
 g := ![![![![40452608, -9113, 0], ![83985408, 0, 0]], ![![11869894, -2674, 0], ![24643600, 0, 0]]], ![![![-17689138, 8424, -1], ![-36725184, 9216, 0]], ![![-5191414, 5609, -1], ![-10778119, 9217, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9216, 0, 0], ![-4439, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![9, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![768, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![768, 0, 0], ![32, 32, 0]], ![![216, 24, 0], ![9, 10, 1]]]
 hmul := by decide
 f := ![![![![2376898, 2376898, 1848433], ![198096, -43544832, 0]], ![![-8177664, -788736, 0], ![-7155456, -7680, 0]]], ![![![521495, 521495, 405549], ![43464, -9553802, 0]], ![![-1794192, -173050, 0], ![-1569918, -1685, 0]]]]
 g := ![![![![53574, 317, 0], ![-243456, 0, 0]], ![![2190, 13, 0], ![-9952, 0, 0]]], ![![![15036, 89, 0], ![-68328, 0, 0]], ![![542, 3, 0], ![-2463, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![768, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![9, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![18432, 0, 0], ![4777, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18432, 0, 0], ![5408, 32, 0]], ![![5184, 576, 0], ![1521, 178, 1]]]
 hmul := by decide
 f := ![![![![1351250537050844, 9023663674715, 6083461816], ![-4605443197173504, -3503781111744, 0]], ![![0, 0, 0], ![-8604887040, -4313088, 0]]], ![![![350197957271562, 2338625221090, 1576625387], ![-1193573475649014, -908060314727, 0]], ![![0, 0, 0], ![-2230092630, -1117805, 0]]]]
 g := ![![![![1925132, 403, 0], ![-7428096, 0, 0]], ![![563678, 118, 0], ![-2174944, 0, 0]]], ![![![539652, 113, 0], ![-2082240, 0, 0]], ![![154056, 32, 0], ![-594423, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18432, 0, 0], ![4777, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![-23, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![1536, 0, 0], ![169, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![1536, 0, 0], ![64, 64, 0]], ![![-552, 24, 0], ![-23, -22, 1]]]
 hmul := by decide
 f := ![![![![13242722, 5783289, 36104], ![-158360880, -309288, 0]], ![![18399744, -1585152, 0], ![2044416, -15360, 0]]], ![![![1452736, 634430, 3960], ![-17372292, -33914, 0]], ![![2018466, -173892, 0], ![224274, -1685, 0]]]]
 g := ![![![![65066, 385, 0], ![-591360, 0, 0]], ![![2528, 15, 0], ![-22976, 0, 0]]], ![![![-23494, -308, -1], ![213528, 1536, 0]], ![![-993, -6, 0], ![9025, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1536, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![-23, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![36864, 0, 0], ![-13655, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36864, 0, 0], ![10816, 64, 0]], ![![-13248, 576, 0], ![-3887, 146, 1]]]
 hmul := by decide
 f := ![![![![217857050371874112, 1454876581597186, 980956646243], ![-742518509965627392, -565039285080192, 0]], ![![0, 0, 0], ![540547854336, -82944000, 0]]], ![![![-80697764213172688, -538909744443091, -363362158842], ![275040828556348992, 209299661961227, 0]], ![![0, 0, 0], ![-200227641110, 30723795, 0]]]]
 g := ![![![![328061376, -24025, 0], ![885657600, 0, 0]], ![![96267774, -7050, 0], ![259891264, 0, 0]]], ![![![-117883402, 22288, -1], ![-318246336, 36864, 0]], ![![-34569348, 16187, -1], ![-93325847, 36865, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36864, 0, 0], ![-13655, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![128, 0, 0], ![41, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![3072, 0, 0], ![-1367, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![3072, 0, 0], ![128, 128, 0]], ![![984, 24, 0], ![41, 42, 1]]]
 hmul := by decide
 f := ![![![![11747313372, -40927422913, -1053495084], ![-140478289056, -2238676296, 0]], ![![-18399744000, 146788224000, 0], ![-28621824, -30720, 0]]], ![![![-5229312054, 18218826648, 468962933], ![62533856664, 996545910, 0]], ![![8190639000, -65342721750, 0], ![12740994, 13675, 0]]]]
 g := ![![![![4001210, -2927, 0], ![8991744, 0, 0]], ![![168198, -123, 0], ![377984, 0, 0]]], ![![![1283624, -939, 0], ![2884632, 0, 0]], ![![55307, -40, 0], ![124289, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3072, 0, 0], ![-1367, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![128, 0, 0], ![41, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![73728, 0, 0], ![23209, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![73728, 0, 0], ![21632, 128, 0]], ![![23616, 576, 0], ![6929, 210, 1]]]
 hmul := by decide
 f := ![![![![-4708876744352498708742, -31450931945881811438, -21218239492948519], ![16049187279648426086784, 12230085400811214336, 0]], ![![1921294802681856, -1862100906541056, 0], ![139731886080, 70041600, 0]]], ![![![-1482316435837088749536, -9900499817007834617, -6679330729488033], ![5052154765992218353536, 3849932284393765800, 0]], ![![604808114274672, -586174352994771, 0], ![43986471210, 22048531, 0]]]]
 g := ![![![![373223930, 16081, 0], ![-1185619968, 0, 0]], ![![109500022, 4718, 0], ![-347848576, 0, 0]]], ![![![119549378, 5151, 0], ![-379772352, 0, 0]], ![![35076039, 1511, 0], ![-111426007, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![73728, 0, 0], ![23209, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![-87, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![256, 0, 0], ![-87, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![6144, 0, 0], ![-1367, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![6144, 0, 0], ![256, 256, 0]], ![![-2088, 24, 0], ![-87, -86, 1]]]
 hmul := by decide
 f := ![![![![14806042672, -170891429620, 2370018893], ![-177055593600, -7638643872, 0]], ![![21858895872, -525246529536, 0], ![8177664, -61440, 0]]], ![![![-3295452116, 38036127259, -527506502], ![39408114900, 1700169704, 0]], ![![-4865239566, 116906645844, 0], ![-1820142, 13675, 0]]]]
 g := ![![![![8061200, -5897, 0], ![36231168, 0, 0]], ![![337706, -247, 0], ![1517824, 0, 0]]], ![![![-2738096, 3370, -1], ![-12306408, 6144, 0]], ![![-113176, 1450, -1], ![-508671, 6145, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6144, 0, 0], ![-1367, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![256, 0, 0], ![-87, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![147456, 0, 0], ![-50519, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![147456, 0, 0], ![43264, 256, 0]], ![![-50112, 576, 0], ![-14703, 82, 1]]]
 hmul := by decide
 f := ![![![![2589226478964836250634, 17293984258308700592, 11678225059218743], ![-8824818665825979527808, -6725533594562264448, 0]], ![![496730383368192, -499576838897664, 0], ![2162191417344, -331776000, 0]]], ![![![-887079428949524567862, -5924988719509729092, -4001006980593482], ![3023418448043119184296, 2304194920341752828, 0]], ![![-170181831678278, 171157038816830, 0], ![-740775495446, 113667795, 0]]]]
 g := ![![![![7006631668, -138693, 0], ![20451115008, 0, 0]], ![![2055820274, -40694, 0], ![6000574720, 0, 0]]], ![![![-2381111830, 97652, -1], ![-6950043072, 147456, 0]], ![![-698559396, 64347, -1], ![-2038970967, 147457, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![147456, 0, 0], ![-50519, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl

lemma PowJ0_9J1_0 : J0 ^ 9*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![512, 0, 0], ![169, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     
def MulR91_J0_9J1_1 : IdealMulEqCertificate timesTableO (((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![512, 0, 0], ![169, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![12288, 0, 0], ![-1367, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![12288, 0, 0], ![512, 512, 0]], ![![4056, 24, 0], ![169, 170, 1]]]
 hmul := by decide
 f := ![![![![20704826576, -238386999346, -1023063953], ![-247595217792, -10838120400, 0]], ![![-31467651072, 755027619840, 0], ![-114487296, -122880, 0]]], ![![![-2304186408, 26529470380, 113854131], ![27554229144, 1206146306, 0]], ![![3501953208, -84025064006, 0], ![12740994, 13675, 0]]]]
 g := ![![![![8761104, -6409, 0], ![78753792, 0, 0]], ![![365046, -267, 0], ![3281408, 0, 0]]], ![![![2891208, -2115, 0], ![25989144, 0, 0]], ![![121834, -89, 0], ![1095169, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_1 : J0 ^ 9*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12288, 0, 0], ![-1367, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR91_J0_9J1_1]
 rfl
def MulR92_J0_9J1_2 : IdealMulEqCertificate timesTableO (((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![512, 0, 0], ![169, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![294912, 0, 0], ![-50519, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![294912, 0, 0], ![86528, 512, 0]], ![![97344, 576, 0], ![28561, 338, 1]]]
 hmul := by decide
 f := ![![![![-1289741405610519576874512, -8614441918904534795129, -5815597447020461008], ![4395804884014591293981696, 3349925752126789767744, 0]], ![![127459104109166592, -125886794916298752, 0], ![558927544320, 280166400, 0]]], ![![![220935302276849046409732, 1475671263262736563623, 996223564110297888], ![-753010236451302886833096, -573849033171721056406, 0]], ![![-21834001429895172, 21564661696140983, 0], ![-95745414870, -47993069, 0]]]]
 g := ![![![![7717029846, -152755, 0], ![45049282560, 0, 0]], ![![2264261668, -44820, 0], ![13217956352, 0, 0]]], ![![![2547218598, -50421, 0], ![14869758528, 0, 0]], ![![747386798, -14794, 0], ![4362978985, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_2 : J0 ^ 9*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![294912, 0, 0], ![-50519, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR92_J0_9J1_2]
 rfl

lemma PowJ0_10J1_0 : J0 ^ 10*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1024, 0, 0], ![-343, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     
def MulR101_J0_10J1_1 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![1024, 0, 0], ![-343, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![24576, 0, 0], ![-1367, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![24576, 0, 0], ![1024, 1024, 0]], ![![-8232, 24, 0], ![-343, -342, 1]]]
 hmul := by decide
 f := ![![![![47891116838, -552160383502, 2719217725], ![-572697938832, -24888845088, 0]], ![![71734468608, -1722559758336, 0], ![32710656, -245760, 0]]], ![![![-2664839042, 30724247929, -151307342], ![31867033548, 1384907502, 0]], ![![-3991571406, 95849602164, 0], ![-1820142, 13675, 0]]]]
 g := ![![![![8506842, -6223, 0], ![152936448, 0, 0]], ![![356844, -261, 0], ![6415360, 0, 0]]], ![![![-2847460, 3450, -1], ![-51191784, 24576, 0]], ![![-117505, 1453, -1], ![-2112511, 24577, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_1 : J0 ^ 10*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24576, 0, 0], ![-1367, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR101_J0_10J1_1]
 rfl
def MulR102_J0_10J1_2 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![1024, 0, 0], ![-343, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![589824, 0, 0], ![-50519, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![589824, 0, 0], ![173056, 1024, 0]], ![![-197568, 576, 0], ![-57967, -174, 1]]]
 hmul := by decide
 f := ![![![![159008068355080318140288, 1063528451965629658914, 725961956004720451], ![-541944650063096141635584, -418114442189381834880, 0]], ![![7833487125970944, -70479072015482880, 0], ![8648765669376, -1327104000, 0]]], ![![![-13619201296286761170942, -91092283690303556213, -62179373125869877], ![46418105427033038939090, 35811923331750286280, 0]], ![![-670946066599774, 6036603543984154, 0], ![-740775495446, 113667795, 0]]]]
 g := ![![![![7361578162, -145719, 0], ![85948563456, 0, 0]], ![![2159889414, -42754, 0], ![25217336320, 0, 0]]], ![![![-2465781822, 99328, -1], ![-28788719040, 589824, 0]], ![![-723427768, 64839, -1], ![-8446229335, 589825, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_2 : J0 ^ 10*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![589824, 0, 0], ![-50519, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR102_J0_10J1_2]
 rfl

lemma PowJ0_11J1_0 : J0 ^ 11*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2048, 0, 0], ![681, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     
def MulR111_J0_11J1_1 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![2048, 0, 0], ![681, 1, 0]] ![![24, 0, 0], ![1, 1, 0]]
  ![![49152, 0, 0], ![-1367, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![49152, 0, 0], ![2048, 2048, 0]], ![![16344, 24, 0], ![681, 682, 1]]]
 hmul := by decide
 f := ![![![![-30900517073364, 2337027259829082, -649422873953], ![369518683335648, 98636598084528, 0]], ![![46625536278528, -7086971677163520, 0], ![274219008, 294912, 0]]], ![![![859710214910, -65020472085836, 18068159740], ![-10280701319944, -2744254755871, 0]], ![![-1297209678376, 197172815237851, 0], ![-7629286, -8205, 0]]]]
 g := ![![![![42318220, -30957, 0], ![1521598464, 0, 0]], ![![1764854, -1291, 0], ![63457280, 0, 0]]], ![![![14073266, -10295, 0], ![506019864, 0, 0]], ![![587867, -430, 0], ![21137409, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_1 : J0 ^ 11*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49152, 0, 0], ![-1367, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR111_J0_11J1_1]
 rfl
def MulR112_J0_11J1_2 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![2048, 0, 0], ![681, 1, 0]] ![![576, 0, 0], ![169, 1, 0]]
  ![![1179648, 0, 0], ![-50519, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1179648, 0, 0], ![346112, 2048, 0]], ![![392256, 576, 0], ![115089, 850, 1]]]
 hmul := by decide
 f := ![![![![-2370018382895169767762820, -15898038568360397877049, -11092532768474606940], ![8077695721875737952862464, 6389722767757676662080, 0]], ![![60306046321950720, -1507175530168320000, 0], ![2235710177280, 1120665600, 0]]], ![![![101497231450588559805050, 680841512381902765528, 475043305107099654], ![-345931389472650718278036, -273643097177986028129, 0]], ![![-2582636820703380, 64545551513945295, 0], ![-95745414870, -47993069, 0]]]]
 g := ![![![![6992486348, -138413, 0], ![163278618624, 0, 0]], ![![2051677716, -40612, 0], ![47907866624, 0, 0]]], ![![![2325137000, -46025, 0], ![54293299776, 0, 0]], ![![682210776, -13504, 0], ![15930017961, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_2 : J0 ^ 11*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1179648, 0, 0], ![-50519, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR112_J0_11J1_2]
 rfl
