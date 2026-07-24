import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![38, 13, 4]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![4608541970673, 310254517665, -121238679848]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-38, -3, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-38, -3, 1]] ![![5, 0, 0], ![-38, -3, 1]]
  ![![25, 0, 0], ![-28, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-190, -15, 5]], ![![-190, -15, 5], ![-627, -2, 9]]]
 hmul := by decide
 f := ![![![![39, -92, 14], ![-160, 0, 0]], ![![0, 0, 0], ![50, 0, 0]]], ![![![-30, 104, -16], ![181, 0, 0]], ![![0, 0, 0], ![-56, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![5, 0, 0]]], ![![![-2, 0, 0], ![5, 0, 0]], ![![13, 4, -1], ![34, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![-28, -3, 1]] ![![5, 0, 0], ![-38, -3, 1]]
  ![![125, 0, 0], ![-53, -28, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-950, -75, 25]], ![![-140, -15, 5], ![-1007, -32, 19]]]
 hmul := by decide
 f := ![![![![18847, 37981, -12677], ![-168530, 0, 0]], ![![1158625, 0, 0], ![250, 0, 0]]], ![![![-7989, -16104, 5375], ![71457, 0, 0]], ![![-491257, 0, 0], ![-106, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![3, 5, 0], ![25, 0, 0]]], ![![![1, 1, 0], ![5, 0, 0]], ![![0, 4, 0], ![19, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![-53, -28, 1]] ![![5, 0, 0], ![-38, -3, 1]]
  ![![38, 13, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![-4750, -375, 125]], ![![-265, -140, 5], ![-8232, -382, 219]]]
 hmul := by decide
 f := ![![![![-7410, 190113, 3356], ![-56956, 0, 0]], ![![1001072, 0, 0], ![76, 0, 0]]]]
 g := ![![![![48, 2, -1]], ![![-16, -9, 2]]], ![![![59, 1, -1]], ![![-165, -19, 6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![671736446755251389245996, 172350140300096511599791, 32590575387124043189267])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-38, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-28, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![-53, -28, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
