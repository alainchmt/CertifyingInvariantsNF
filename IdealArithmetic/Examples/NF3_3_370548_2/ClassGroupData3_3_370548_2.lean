import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_370548_2.RI3_3_370548_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![511, 19, -12]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![11, -1, 0]

def zeta2 := B.equivFun.symm ![-9587, -361, 224]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![-12, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 2]]]
 hmul := by decide
 f := ![![![![-1086405, 595939, -51816], ![-2674575, 107360, 0]], ![![0, 0, 0], ![110500, -100, 0]]], ![![![532332, -292005, 25388], ![1310526, -52602, 0]], ![![0, 0, 0], ![-54144, 49, 0]]]]
 g := ![![![![301, -25, 0], ![625, 0, 0]], ![![-106, 21, -2], ![-220, 25, 0]]], ![![![-106, 21, -2], ![-220, 25, 0]], ![![52, -4, 0], ![108, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![-12, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![511, 19, -12]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![-60, 5, 0], ![24, -14, 2]]]
 hmul := by decide
 f := ![![![![1105934177, -599380964, 41846940], ![2757842805, -101751365, 0]], ![![5594110, -14223714, 0], ![-559411, -2025, 0]]]]
 g := ![![![![-1033, -227, 58]], ![![2014, 441, -114]]], ![![![816, 179, -46]], ![![-1596, -350, 90]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-25, -11, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![5641, 1237, -318])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-12, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
