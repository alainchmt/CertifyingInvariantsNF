import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_67500000_1.RI5_1_67500000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![2, 1, 0, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![5, 22, 16, 12, -8]

def zeta2 := B.equivFun.symm ![-15916, 121319, 63617, 104665, -61214]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]], ![![0, 2, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide
 f := ![![![![0, 5142, 3398, 1180, -4565], ![-3856, 1700, 0, 4192, -708]], ![![0, 0, 0, 0, 0], ![-212, -304, 0, 8, 4]]], ![![![0, 2548, 1684, 585, -2263], ![-1909, 844, 0, 2078, -351]], ![![0, 0, 0, 0, 0], ![-106, -151, 0, 4, 2]]]]
 g := ![![![![-2, 7, 0, -28, -13], ![4, -16, 32, 28, -4]], ![![-2, 13, 0, -28, -11], ![4, -28, 38, 24, -4]]], ![![![-2, 13, 0, -28, -11], ![4, -28, 38, 24, -4]], ![![1, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![2, 1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![0, 4, 0, 0, 0]], ![![4, 2, 0, 0, 0], ![0, 2, 1, 0, 0]]]
 hmul := by decide
 f := ![![![![0, -2775964, -1827908, -598422, 2425143], ![2081975, -913952, 0, -2242257, 380814]], ![![-42627, 33228, 0, 16390, -2769], ![1316, -1035, 0, 28, 2]]]]
 g := ![![![![-7, -18, -15, -2, 4]], ![![11, 18, 15, 2, -4]]], ![![![2, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1437, 818, 4, -92, 8])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-125956, -310429, -219097, -245985, -75296])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
