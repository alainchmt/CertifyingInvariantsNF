import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_138580_1.RI3_1_138580_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![93823, -443985, 259650]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![13908659653857, -3471063367147, 683347577295]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![3, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![3, 0, 1]] ![![2, 0, 0], ![3, 0, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![6, 0, 2]], ![![6, 0, 2], ![43, 17, 2]]]
 hmul := by decide
 f := ![![![![60469, 0, -34193], ![73610, -4583, 0]], ![![0, 0, 0], ![-536, -3, 0]]], ![![![116, 0, -68], ![146, -9, 0]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![1, -1, 0], ![2, 0, 0]], ![![2, -1, 1], ![2, 0, 0]]], ![![![2, -1, 1], ![2, 0, 0]], ![![16, 3, 1], ![11, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![3, 0, 1]]
  ![![93823, -443985, 259650]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![6, 0, 2]], ![![2, 2, 0], ![75, -1, 2]]]
 hmul := by decide
 f := ![![![![-2815835, 0, 1671396], ![-3388048, 268904, 0]], ![![0, 0, 0], ![-93823, 0, 0]]]]
 g := ![![![![-5040650418302, -495320703465, -401620329225]], ![![-32220066549018, -3166112446680, -2567175396271]]], ![![![-17473977764716, -1717084550701, -1392261736155]], ![![-111694459986945, -10975682481967, -8899400289631]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-449476807438560425772390399, -44167944605582718598505795, -35812644877540711929114991])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
