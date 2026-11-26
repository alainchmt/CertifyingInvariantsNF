import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_607500000_4.RI5_1_607500000_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1032, 392, 34, 21, -95]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-27037, 23656, 848, -864, -9562]

def zeta2 := B.equivFun.symm ![-1193171, 1499625, -194433, -337974, -1287680]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]] ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]]
  ![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-16, 18, 2, 0, -6]], ![![-16, 18, 2, 0, -6], ![22, -96, 6, 15, 69]]]
 hmul := by decide
 f := ![![![![-245703949571, -124919707692, 42396459188, 137086579335, 291672793042], ![4366153775, -89910931068, -727994466, 0, -12005880]], ![![0, 0, 0, 0, 0], ![-48081, -219, 15, 0, -1]]], ![![![-725475487672, -368843016184, 125181511968, 404767416918, 861204966940], ![12891683438, -265474676640, -2149506108, 0, -35449050]], ![![0, 0, 0, 0, 0], ![-141966, -646, 44, 0, -3]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 3, 0, 0, 0], ![-2, 2, 0, 0, 0]]], ![![![-4, 3, 0, 0, 0], ![-2, 2, 0, 0, 0]], ![![-7, 14, 0, 30, 56], ![-1, -9, -15, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]]
  ![![4, 0, 0, 0, 0], ![-12, 14, 0, -1, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-16, 18, 2, 0, -6]], ![![12, -4, 0, 0, 2], ![-34, 46, 2, 0, -13]]]
 hmul := by decide
 f := ![![![![-10898835, -5541144, 1880606, 6080832, 12937896], ![193670, -3988242, -32292, 0, -531]], ![![0, 0, 0, 0, 0], ![6, 0, 0, 0, 0]]], ![![![-2788395239, -1417664528, 481140590, 1555740539, 3310074604], ![49549047, -1020365358, -8261697, 0, -135828]], ![![0, 0, 0, 0, 0], ![1563, 43, 1, 0, 0]]]]
 g := ![![![![853, 588, 0, 162, 0], ![-528, 504, 168, 0, 0]], ![![-22518, -15611, 0, -4290, 21], ![13985, -13331, -4449, 0, -9]]], ![![![6808, 4712, 0, 1296, -4], ![-4224, 4028, 1344, 0, 2]], ![![-55996, -38816, 0, -10669, 49], ![34774, -33148, -11064, 0, -23]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-12, 14, 0, -1, -7]] ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]]
  ![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-32, 36, 4, 0, -12]], ![![-24, 28, 0, -2, -14], ![-28, -28, 0, 1, 7]]]
 hmul := by decide
 f := ![![![![-5519306255415, -2816596178597, 949978372549, 3089448962355, 6492933226169], ![138131565055, -2045303457862, -7114035999, 0, -50555855]], ![![1058405, -451785, -151655, 0, 0], ![-3195, -117, -87, 0, 3]]], ![![![-5712157704697, -2915011564507, 983171802565, 3197398165080, 6719804417009], ![142958054342, -2116768913448, -7362609296, 0, -52322340]], ![![1095393, -467577, -156954, 0, 0], ![-3306, -120, -90, 0, 3]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 3, 0, 0, 0], ![-4, 4, 0, 0, 0]]], ![![![0, 19, 0, 4, 1], ![-6, -6, -6, 0, 0]], ![![-7, -14, 0, -2, 0], ![1, 3, 3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]]
  ![![-1032, 392, 34, 21, -95]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-32, 36, 4, 0, -12]], ![![12, -4, 0, 0, 2], ![-34, 46, 2, 0, -13]]]
 hmul := by decide
 f := ![![![![-13473080047496, -6875540428474, 2318977406068, 7541603536359, 15849791812062], ![337189246833, -4992756902770, -17365962985, 0, -123440408]], ![![-10542133, -133861, 33570, 0, 0], ![150579, 3849, -21, 0, 0]]]]
 g := ![![![![-22, 23, -13, -1, -2]], ![![-113, 175, 1, -10, -185]]], ![![![-10, 16, 8, -10, -32]], ![![-98, 83, -49, -43, -11]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1237, -12952, -15792, -1268, 39958])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![10676839, -4412835, -348407, -177106, 1177610])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-8, 9, 1, 0, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-12, 14, 0, -1, -7]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
