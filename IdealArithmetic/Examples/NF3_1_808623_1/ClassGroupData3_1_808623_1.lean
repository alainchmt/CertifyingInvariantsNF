import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_808623_1.RI3_1_808623_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![23, -2, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-23149653, 2092369, -44931]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![25, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![-1, 4, 5]]]
 hmul := by decide
 f := ![![![![1795607, 42207, -10339], ![367565, 0, -52800]], ![![0, 0, 0], ![-2225, 0, 100]]], ![![![-817, -20, 5], ![-163, 0, 24]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![441, 441, 661], ![50, -3325, -100]], ![![0, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![-89, -89, -132], ![14, 665, 20]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![23, -2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![25, 25, 0]], ![![5, 5, 0], ![-1, 4, 5]]]
 hmul := by decide
 f := ![![![![7400679698, 175369400, -43525921], ![1515209822, 0, -217619256]], ![![9354096, 0, -52848], ![-2223, 0, 100]]]]
 g := ![![![![-293, -54, -20]], ![![-745, -135, -50]]], ![![![-149, -27, -10]], ![![-373, -68, -25]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-315108680332078, -57444239462948, -21203745285647])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
