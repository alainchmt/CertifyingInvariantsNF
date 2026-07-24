import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_853335_2.RI3_1_853335_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-9, 5, -2]

def alpha1 := B.equivFun.symm ![-6, 7, -3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-246, -15, 14]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![25, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![1, 2, 7]]]
 hmul := by decide
 f := ![![![![0, -3464, -6391], ![0, -9630, 0]], ![![0, 0, 0], ![71075, -50, 0]]], ![![![0, -70, -133], ![0, -189, 0]], ![![0, 0, 0], ![1422, -1, 0]]]]
 g := ![![![![0, -1, 0], ![25, 0, 0]], ![![0, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![-9, 5, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![25, 25, 0]], ![![5, 5, 0], ![1, 2, 7]]]
 hmul := by decide
 f := ![![![![0, 612, 4936], ![1827, -2314, -9]], ![![0, 477, 0], ![-32692, 23, 0]]]]
 g := ![![![![956, 161, 73]], ![![3155, 530, 240]]], ![![![631, 106, 48]], ![![2075, 349, 158]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![169, 0, 0], ![-74, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![52, 13, 0], ![16, 8, 7]]]
 hmul := by decide
 f := ![![![![2034478585, 568150520, 104201006], ![-6595244760, -189372326, 0]], ![![0, 0, 0], ![-53794052, -9464, 0]]], ![![![-892556522, -249256229, -45714564], ![2893433614, 83080516, 0]], ![![0, 0, 0], ![23600264, 4152, 0]]]]
 g := ![![![![2073, -28, 0], ![4732, 0, 0]], ![![672, -9, 0], ![1534, 0, 0]]], ![![![672, -9, 0], ![1534, 0, 0]], ![![332, -4, 0], ![758, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![169, 0, 0], ![-74, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![-6, 7, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![2197, 0, 0], ![676, 169, 0]], ![![-962, 13, 0], ![-296, -70, 7]]]
 hmul := by decide
 f := ![![![![-10894352492838, -3890274221439, -2195015712523], ![35379667555086, 4062220887744, 0]], ![![-18956003140, 185079620850, 0], ![-5013342, 392, 0]]]]
 g := ![![![![-1821, -303, -136]], ![![-2684, -453, -205]]], ![![![634, 105, 47]], ![![929, 157, 71]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-11859, -1994, -903])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-74, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![1, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![65, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![65, 0, 0], ![20, 5, 0]], ![![13, 13, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![5680, 1610, 77], ![-18330, -650, 0]], ![![-195, 195, 0], ![0, 0, 0]]], ![![![-784, -226, -14], ![2530, 104, 0]], ![![27, -30, 0], ![0, 0, 0]]]]
 g := ![![![![316, -35, 0], ![2275, 0, 0]], ![![100, -11, 0], ![720, 0, 0]]], ![![![74, -8, 0], ![533, 0, 0]], ![![20, -2, 0], ![144, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![65, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![1, 1, 0]] ![![169, 0, 0], ![-74, 1, 0]]
  ![![845, 0, 0], ![-74, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![845, 0, 0], ![-370, 5, 0]], ![![169, 169, 0], ![-74, -73, 7]]]
 hmul := by decide
 f := ![![![![335390, -4974, -1141], ![765570, -1014, 0]], ![![-845, 845, 0], ![0, 0, 0]]], ![![![-29304, 470, 98], ![-66890, 169, 0]], ![![74, -75, 0], ![0, 0, 0]]]]
 g := ![![![![28861, -390, 0], ![329550, 0, 0]], ![![-12506, 243, -7], ![-142800, 845, 0]]], ![![![5861, -79, 0], ![66924, 0, 0]], ![![-2442, 107, -7], ![-27884, 846, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![845, 0, 0], ![-74, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![1, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![325, 0, 0], ![-74, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![325, 0, 0], ![100, 25, 0]], ![![13, 13, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![-18377, -5164, -826], ![59644, 1872, 0]], ![![650, -650, 0], ![0, 0, 0]]], ![![![4178, 1171, 182], ![-13560, -416, 0]], ![![-148, 150, 0], ![0, 0, 0]]]]
 g := ![![![![18945, -256, 0], ![83200, 0, 0]], ![![5852, -79, 0], ![25700, 0, 0]]], ![![![817, -11, 0], ![3588, 0, 0]], ![![240, -3, 0], ![1054, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![325, 0, 0], ![-74, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![1, 1, 0]] ![![169, 0, 0], ![-74, 1, 0]]
  ![![4225, 0, 0], ![-74, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4225, 0, 0], ![-1850, 25, 0]], ![![169, 169, 0], ![-74, -73, 7]]]
 hmul := by decide
 f := ![![![![7001878, -104044, -23947], ![15982668, -21632, 0]], ![![-88725, 88725, 0], ![0, 0, 0]]], ![![![-122544, 1878, 420], ![-279722, 507, 0]], ![![1554, -1575, 0], ![0, 0, 0]]]]
 g := ![![![![91095, -1231, 0], ![5200975, 0, 0]], ![![-39738, 611, -7], ![-2268800, 4225, 0]]], ![![![3703, -50, 0], ![211419, 0, 0]], ![![-1554, 21, 0], ![-88724, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4225, 0, 0], ![-74, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
