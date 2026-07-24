import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![10652007, -977389, 110766]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-346882673112607, 10608407217225, 16529587380504]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![25, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![-1, 4, 10]]]
 hmul := by decide
 f := ![![![![14605, -245, -61], ![2875, 0, -550]], ![![0, 0, 0], ![-225, 0, 25]]], ![![![-5869, 98, 25], ![-1153, 0, 221]], ![![0, 0, 0], ![89, 0, -10]]]]
 g := ![![![![-1009, -4274, 6089], ![200, -15250, -25]], ![![4, -6, 8], ![15, -20, 0]]], ![![![4, -6, 8], ![15, -20, 0]], ![![205, 850, -1211], ![-28, 3034, 5]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![-9, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![10652007, -977389, 110766]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![25, 25, 0]], ![![-45, 5, 0], ![-11, -6, 10]]]
 hmul := by decide
 f := ![![![![559098872610056, -5764357786618, -4219303471860], ![110666902964690, 0, -20920860385062]], ![![9541266438207, 0, -68086204024], ![64609014620, 0, 11629396]]]]
 g := ![![![![-95607202979839, -12589492842167, -8756981818720]], ![![-255778341655773, -33680721756244, -23427589320590]]], ![![![-12912787139219, -1700347214382, -1182725136630]], ![![-34545632313079, -4548945865777, -3164149401438]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-55297599064360429209841540333, -7281551032892255724981297633, -5064891080723129519366318514])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
