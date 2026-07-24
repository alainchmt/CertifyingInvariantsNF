import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_851175_3.RI3_1_851175_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![10170437, 356223, 270770]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-627229, 276663, -83736]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![49, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![7, 7, 0]], ![![7, 7, 0], ![0, 3, 3]]]
 hmul := by decide
 f := ![![![![263816, -502544, -764154], ![-34104, 1800946, 0]], ![![0, 0, 0], ![-124950, -245, 0]]], ![![![5370, -10230, -15555], ![-692, 36660, 0]], ![![0, 0, 0], ![-2545, -5, 0]]]]
 g := ![![![![-33, 65, 99], ![49, -1617, 0]], ![![0, 0, 0], ![7, 0, 0]]], ![![![0, 0, 0], ![7, 0, 0]], ![![2, -4, -6], ![1, 99, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![10170437, 356223, 270770]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![49, 49, 0]], ![![7, 7, 0], ![0, 3, 3]]]
 hmul := by decide
 f := ![![![![-7899552159414, 15321950161546, 23221567731743], ![1060342571738, -54236522544160, 0]], ![![376191320542, 373770756536, 0], ![-25932833235, -50852185, 0]]]]
 g := ![![![![12565, -3332, -1223]], ![![-17297, 6958, -1428]]], ![![![-2471, 994, -204]], ![![-3759, 951, 426]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-17610516169633, -616814292468, -468849024459])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
