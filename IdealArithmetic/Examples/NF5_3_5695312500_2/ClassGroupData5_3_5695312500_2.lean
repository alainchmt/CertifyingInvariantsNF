import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_3_5695312500_2.RI5_3_5695312500_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-7, 3, -8, -5, 11]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-4629, 546, -3982, -3216, 8528]

def zeta2 := B.equivFun.symm ![24437, -3151, 21323, 16824, -44838]

def zeta3 := B.equivFun.symm ![-474917, -10979, -332883, -369502, 919008]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![2, 0, 0, 0, 0], ![1, 19, 8, 5, -15]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-10, 20, 10, 6, -18]], ![![-10, 20, 10, 6, -18], ![27, -131, -44, -25, 79]]]
 hmul := by decide
 f := ![![![![11070755965, -1863144039, 2599910895, 1766567840, -6375571612], ![847091162, 2541233556, 0, 164497545, 2654544]], ![![0, 0, 0, 0, 0], ![-10616, -21137, 0, -169, 9]]], ![![![98338543214, -16549807848, 23094308449, 15691946328, -56632486526], ![7524482738, 22573092645, 0, 1461187578, 23579535]], ![![0, 0, 0, 0, 0], ![-94305, -187702, 0, -1500, 78]]]]
 g := ![![![![1998, -1798, 384, 704, -1706], ![80, 352, 0, 4, 0]], ![![-14928, 13408, -2884, -5272, 12781], ![-594, -2630, 0, -30, 0]]], ![![![-14928, 13408, -2884, -5272, 12781], ![-594, -2630, 0, -30, 0]], ![![78649, -70698, 15188, 27775, -67330], ![3133, 13860, 0, 158, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![1, 19, 8, 5, -15]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![4, 0, 0, 0, 0], ![-1, 19, 8, 5, -15]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-10, 20, 10, 6, -18]], ![![2, 38, 16, 10, -30], ![-17, -127, -36, -19, 63]]]
 hmul := by decide
 f := ![![![![-52211320624, 8790524624, -12262221724, -8331519339, 30071878060], ![-3995359804, -11983379928, 0, -776350932, -12452760]], ![![0, 0, 0, 0, 0], ![64428, 1808, 0, 4, 0]]], ![![![260820732216, -43912910900, 61255712531, 41619958038, -150223536913], ![19958749509, 59862763284, 0, 3878247399, 62207544]], ![![0, 0, 0, 0, 0], ![-321849, -9032, 0, -20, 0]]]]
 g := ![![![![992746, -682890, 172372, 315783, -750414], ![61764, 388908, -612, 4, 0]], ![![1565336024, -1076739117, 271803284, 497926425, -1183256726], ![97382608, 613220673, -965032, 6291, 147]]], ![![![2815649559, -1936785427, 488906400, 895645598, -2128384085], ![175167050, 1103031228, -1735852, 11316, 264]], ![![-8253849640, 5677530265, -1433189700, -2625512856, 6239186343], ![-513488075, -3233447100, 5088510, -33172, -774]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-1, 19, 8, 5, -15]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![-7, 3, -8, -5, 11]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-20, 40, 20, 12, -36]], ![![-2, 38, 16, 10, -30], ![-7, -147, -46, -25, 81]]]
 hmul := by decide
 f := ![![![![-83885993269078362335, 10710548320910940657, -19384884201272469769, -13570012036853136783, 44600570738640597389], ![-6252072105092958724, -21153203617853426602, 0, -596972155002971048, -4084982552383467]], ![![-62671820339602, 5955512551941, 0, 22587826974, 0], ![-106325555, -4497412, 0, -10426, -112]]]]
 g := ![![![![60, -54, 36, 50, -118]], ![![274, 83, 141, 148, -378]]], ![![![-196, -65, -195, -204, 518]], ![![-663, 438, -212, -330, 764]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-90797, -55698, 15334, -45000, 215896])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1279203, -35191, -888351, -992590, 2479592])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![35218795, 35595917, 8752395, 4943356, -16282674])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 19, 8, 5, -15]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-1, 19, 8, 5, -15]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
