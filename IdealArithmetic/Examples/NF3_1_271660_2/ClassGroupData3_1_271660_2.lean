import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_271660_2.RI3_1_271660_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-11283, -1014, 227]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-770657225, -285356247, 37947100]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-1, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0], ![-44, -7, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-5, 5, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 187, -77], ![0, -48, 0]], ![![0, 0, 0], ![2147, -9, 0]]], ![![![0, -1757, 718], ![0, 499, 0]], ![![0, 0, 0], ![-20274, 85, 0]]]]
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![43, 8, -1], ![5, 0, 0]]], ![![![43, 8, -1], ![5, 0, 0]], ![![9, 1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![5, 0, 0], ![-44, -7, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![-11283, -1014, 227]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-220, -35, 5], ![282, 31, -8]]]
 hmul := by decide
 f := ![![![![-566656, 294388, -3520], ![-1558301, 53751, 0]], ![![0, 0, 0], ![22566, 0, 0]]]]
 g := ![![![![422489, 164588, 17093]], ![![729129, 284045, 29499]]], ![![![-1578902, -615089, -63879]], ![![-2724860, -1061517, -110242]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![315231488148200613, 122803957372145425, 12753591392842509])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-44, -7, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
