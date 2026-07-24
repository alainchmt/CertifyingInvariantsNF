import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_161700_2.RI3_1_161700_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![6126346890646, 750931752259, 594879975324]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![115526649033322, 160539341501629, -160444662248463]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 0, 1]] ![![2, 0, 0], ![1, 0, 1]]
  ![![2, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 0, 2]], ![![2, 0, 2], ![-12, 13, 0]]]
 hmul := by decide
 f := ![![![![-665, 0, 86], ![-289, 21, 0]], ![![0, 0, 0], ![3, 3, 0]]], ![![![225, 0, -45], ![90, -7, 0]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 0, 1], ![0, 0, 0]]], ![![![1, 0, 1], ![0, 0, 0]], ![![-6, 5, 0], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 0, 1]]
  ![![6126346890646, 750931752259, 594879975324]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 0, 2]], ![![0, 2, 0], ![78, -1, 0]]]
 hmul := by decide
 f := ![![![![13454176577454, 0, -2571859320427], ![5441158628516, 0, 0]], ![![0, 0, 0], ![-750931752259, 0, 0]]]]
 g := ![![![![3696505, -352313, -123891]], ![![-11086663, -629135, 1910198]]], ![![![-4831749, 1795987, -1056939]], ![![74497722, -7768097, -1887405]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2578894470136935255381204764894, -316105793210604467870957929259, -250415574916374289476997176897])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
