import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_48600000_1.RI5_1_48600000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![658, 471, 553, 230, 264]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![15, 12, -5, -5, -8]

def zeta2 := B.equivFun.symm ![-26991, -99902, 36483, 33365, 61972]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![12, -4, 2, 0, 2], ![20, -15, 4, 3, 8]]]
 hmul := by decide
 f := ![![![![-15933728, -28565530, 12085710, 10708530, 22581086], ![-1902234, 9998736, -297984, -247086, 0]], ![![0, 0, 0, 0, 0], ![-45985, 3307, 168, 1, 0]]], ![![![-284184, -509476, 215554, 190990, 402741], ![-33924, 178332, -5313, -4407, 0]], ![![0, 0, 0, 0, 0], ![-820, 59, 3, 0, 0]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![10, -21, 3, 0, 13], ![2, 12, -6, 0, 0]]], ![![![10, -21, 3, 0, 13], ![2, 12, -6, 0, 0]], ![![29, -69, 10, 0, 42], ![0, 41, -19, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![4, 0, 0, 0, 0], ![-2, -5, 0, 1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![4, 2, 2, 0, 0], ![2, 1, -1, 0, 0]]]
 hmul := by decide
 f := ![![![![-201, -346, 144, 131, 274], ![-26, 120, -6, -3, 0]], ![![0, 0, 0, 0, 0], ![2, 2, 0, 0, 0]]], ![![![30, 45, -15, -21, -46], ![29, -6, 15, 0, 0]], ![![0, 0, 0, 0, 0], ![-6, -1, -5, 0, 0]]]]
 g := ![![![![-265583, 113140, 43933, 43587, -1383], ![1574, 88566, -304, 6, 0]], ![![-918260, 391181, 151900, 150703, -4781], ![5439, 306219, -1052, 21, 0]]], ![![![-529672, 225645, 87620, 86929, -2758], ![3140, 176634, -606, 12, 0]], ![![-4590, 1959, 759, 753, -25], ![30, 1531, -5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-2, -5, 0, 1, 2]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![24, -8, 4, 0, 4]], ![![-4, -10, 0, 2, 4], ![-18, -19, 8, 7, 12]]]
 hmul := by decide
 f := ![![![![-88652566380, -158279211992, 64983548070, 59608114831, 124808952192], ![-12782237006, 56582156939, -2063884571, -612228477, 0]], ![![-251881686, -41057679, 1201026, 0, 0], ![-100611, 889, -36, 9, 0]]], ![![![-83500668541, -149081076362, 61207136250, 56144087443, 117555885564], ![-12039418334, 53293978122, -1943945304, -576649829, 0]], ![![-237243989, -38671680, 1131231, 0, 0], ![-94767, 838, -35, 9, 0]]]]
 g := ![![![![4, -13, 1, 0, 8], ![4, 16, -8, 0, 0]], ![![2, 3, -1, 0, -3], ![4, -8, 4, 0, 0]]], ![![![-20, 46, -10, 0, -33], ![4, -66, 34, 0, 0]], ![![-47, 114, -21, 0, -80], ![2, -159, 83, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![658, 471, 553, 230, 264]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![24, -8, 4, 0, 4]], ![![4, 2, 2, 0, 0], ![2, 1, -1, 0, 0]]]
 hmul := by decide
 f := ![![![![-293568, -524900, 216686, 197471, 414092], ![-40394, 188419, -5719, -2121, 0]], ![![741, 879, -741, 0, 0], ![247, -224, -82, 0, 0]]]]
 g := ![![![![-156, 21, -95, 29, -13]], ![![229, -11, 126, -53, -18]]], ![![![102, 17, 37, -35, -53]], ![![-113, -35, -27, 47, 91]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1191, 846, 991, 411, 472])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![93249, 16708, 32775, -32563, -50708])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-2, -5, 0, 1, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
