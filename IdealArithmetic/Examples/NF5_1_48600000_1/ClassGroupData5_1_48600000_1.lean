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
  ![![4, 0, 0, 0, 0], ![10, -7, 5, 2, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![4, 2, 2, 0, 0], ![2, 1, -1, 0, 0]]]
 hmul := by decide
 f := ![![![![-201, -346, 144, 131, 274], ![-26, 120, -6, -3, 0]], ![![0, 0, 0, 0, 0], ![2, 2, 0, 0, 0]]], ![![![-102, -227, 110, 71, 148], ![61, 108, 42, -3, 0]], ![![0, 0, 0, 0, 0], ![-7, 0, -12, 0, 0]]]]
 g := ![![![![-42655043, -29151992, 3104905, 12897129, 25529273], ![-6997982, 7516186, -1956, 6, 0]], ![![-63454990, -43367434, 4618958, 19186180, 37978161], ![-10410423, 11181317, -2910, 9, 0]]], ![![![-127707558, -87279960, 9295974, 38613514, 76433676], ![-20951696, 22503174, -5856, 18, 0]], ![![-21589666, -14755154, 1571534, 6527826, 12921531], ![-3541998, 3804285, -990, 3, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![10, -7, 5, 2, 6]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![24, -8, 4, 0, 4]], ![![20, -14, 10, 4, 12], ![2, -37, 9, 12, 20]]]
 hmul := by decide
 f := ![![![![4627644972026026, 8354667141631425, -3478508652527765, -3120665638970361, -6553610806850299], ![512208044757633, -3049845204339808, 16072604534462, 34839528242967, 0]], ![![5090557841817, 44861443908, -449497443, 0, 0], ![6551563, -102017, 1098, 9, 0]]], ![![![3085036122926017, 5569668823507804, -2318960272844912, -2080402944044909, -4368988156383961], ![341465330655820, -2033190247220216, 10714859475621, 23225896494864, 0]], ![![3393638648337, 29907042528, -299659083, 0, 0], ![4367623, -68010, 732, 6, 0]]]]
 g := ![![![![4, -13, 1, 0, 8], ![4, 16, -8, 0, 0]], ![![2, 3, -1, 0, -3], ![4, -8, 4, 0, 0]]], ![![![-14, 40, -8, 0, -29], ![6, -60, 32, 0, 0]], ![![-60, 158, -31, 0, -113], ![3, -224, 118, 0, 0]]]]
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

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![10, -7, 5, 2, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
