import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.RI2_2_316_1

namespace NF2_2_316_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-17, 2]

def v := B.equivFun.symm ![-1, 0]

def zeta1 := B.equivFun.symm ![80, 9]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0], ![2, 1]] ![![3, 0], ![2, 1]]
  ![![9, 0], ![5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0], ![6, 3]], ![![6, 3], ![83, 4]]]
 hmul := by decide
 f := ![![![![58, -9], ![39, 0]], ![![0, 0], ![-9, 0]]], ![![![32, -5], ![22, 0]], ![![0, 0], ![-5, 0]]]]
 g := ![![![![-4, -1], ![9, 0]], ![![-1, 0], ![3, 0]]], ![![![-1, 0], ![3, 0]], ![![7, 0], ![4, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0], ![5, 1]] ![![3, 0], ![2, 1]]
  ![![-17, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0], ![18, 9]], ![![15, 3], ![89, 7]]]
 hmul := by decide
 f := ![![![![-236, -9], ![-156, 0]], ![![510, 0], ![17, 0]]]]
 g := ![![![![17, 2]], ![![64, 7]]], ![![![27, 3]], ![![97, 11]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![80, -9])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0], ![2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0], ![5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_0 : J0 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1, 0]] i)) := by
 simp only [pow_zero, one_mul, Set.range_unique, Matrix.cons_val_fin_one]
 rw [B_one_repr, Ideal.span_singleton_one, Ideal.one_eq_top]

end

end NF2_2_316_1
