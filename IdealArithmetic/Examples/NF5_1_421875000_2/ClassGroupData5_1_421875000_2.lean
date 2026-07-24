import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_421875000_2.RI5_1_421875000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![1, 0, -2, -3, -6]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-4159, -1618, -1024, -1218, -2658]

def zeta2 := B.equivFun.symm ![35154921739646228779, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![3, 1, 1, 1, 2]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![3, 1, 1, 1, 2]] ![![2, 0, 0, 0, 0], ![3, 1, 1, 1, 2]]
  ![![2, 0, 0, 0, 0], ![-1, 0, 0, -1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![6, 2, 2, 2, 4]], ![![6, 2, 2, 2, 4], ![27, 8, 6, 7, 16]]]
 hmul := by decide
 f := ![![![![187268858, 406988672, 18528172, 419113992, 838311010], ![1541529724, -793085946, 0, -7921182, 162924]], ![![0, 0, 0, 0, 0], ![-3080, -54, 0, -3, 0]]], ![![![-58657, -127474, -5804, -131272, -262570], ![-482822, 248403, 0, 2481, -51]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![26, 8, 0, -7, 9], ![-14, 12, 0, 0, -2]]], ![![![26, 8, 0, -7, 9], ![-14, 12, 0, 0, -2]], ![![106, 32, 0, -33, 31], ![-67, 50, 0, 0, -8]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![-1, 0, 0, -1, -2]] ![![2, 0, 0, 0, 0], ![3, 1, 1, 1, 2]]
  ![![1, 0, -2, -3, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![6, 2, 2, 2, 4]], ![![-2, 0, 0, -2, -4], ![3, 2, 4, 5, 12]]]
 hmul := by decide
 f := ![![![![684274, 1487305, 67750, 1531695, 3063735], ![5633526, -2898297, 0, -28944, 603]], ![![0, 0, 0, 0, 0], ![-85, -2, 0, 0, 0]]]]
 g := ![![![![-8, 3, -1, 0, 0]], ![![-12, -2, -4, -3, -8]]], ![![![10, -7, -7, -4, -16]], ![![15, -17, -5, -6, -18]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-16591, 2190, -2496, -6170, -16050])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-254562580901627484259914029, -90153583328982174006199498, -61376839615727282486940874, -71178013699208626681931408, -155481089938211015699303828])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![3, 1, 1, 1, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-1, 0, 0, -1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
