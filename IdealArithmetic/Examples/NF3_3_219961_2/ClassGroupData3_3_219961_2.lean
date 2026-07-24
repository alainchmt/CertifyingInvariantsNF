import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_219961_2.RI3_3_219961_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-13, 1, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![47, -10, -14]

def zeta2 := B.equivFun.symm ![283, 62, -24]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-25, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-25, -1, 1]] ![![2, 0, 0], ![-25, -1, 1]]
  ![![4, 0, 0], ![-25, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-50, -2, 2]], ![![-50, -2, 2], ![283, 11, -7]]]
 hmul := by decide
 f := ![![![![675356, 6062912, 1791965], ![-10577312, -1744596, 0]], ![![0, 0, 0], ![-4260, 4, 0]]], ![![![-4052240, -36378888, -10752211], ![63466350, 10467984, 0]], ![![0, 0, 0], ![25561, -24, 0]]]]
 g := ![![![![28, 8, 1], ![-20, -4, 0]], ![![-24, -84, -24], ![290, 48, 0]]], ![![![-24, -84, -24], ![290, 48, 0]], ![![263, 481, 132], ![-1623, -272, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-25, -1, 1]] ![![2, 0, 0], ![-25, -1, 1]]
  ![![-13, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-100, -4, 4]], ![![-50, -2, 2], ![283, 11, -7]]]
 hmul := by decide
 f := ![![![![-91716723477, -825024166799, -243212760644], ![1437364746714, 237382929406, 0]], ![![-2790540402, 6105678, 0], ![14909, -14, 0]]]]
 g := ![![![![394, 51, -23]], ![![1136, 146, -66]]], ![![![568, 73, -33]], ![![1583, 207, -93]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![217111, 7918, -6726])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![12435, 4342, 1192])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-25, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-25, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
