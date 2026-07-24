import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_172019_1.RI3_1_172019_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-9, -2, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-66189, 4702, 452]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![49, 0, 0], ![-20, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![7, 7, 0]], ![![7, 7, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2211, -1286], ![0, -497, 0]], ![![0, 0, 0], ![68257, -588, 0]]], ![![![0, 924, 537], ![0, 215, 0]], ![![0, 0, 0], ![-28556, 246, 0]]]]
 g := ![![![![741, -37, 0], ![1813, 0, 0]], ![![123, -6, 0], ![301, 0, 0]]], ![![![123, -6, 0], ![301, 0, 0]], ![![29, -1, 0], ![71, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![-20, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![-9, -2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![49, 49, 0]], ![![-140, 7, 0], ![-20, -19, 1]]]
 hmul := by decide
 f := ![![![![-27536, -12271, -327], ![92447, 2138, 0]], ![![-33435, 2896, 0], ![-11145, 96, 0]]]]
 g := ![![![![65, 22, -4]], ![![-57, -11, 2]]], ![![![-36, -11, 2]], ![![28, 5, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![666218587, 319062298, 45775072])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-20, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
