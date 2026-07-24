import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_551980_3.RI3_1_551980_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-173, 51, -7]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1034804052008711, -72450897703919, 14715473850469]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -577, -228], ![0, -267, 0]], ![![0, 0, 0], ![2799, 18, 0]]], ![![![0, 160, 63], ![0, 75, 0]], ![![0, 0, 0], ![-777, -5, 0]]]]
 g := ![![![![15, -7, 0], ![63, 0, 0]], ![![5, -2, 0], ![21, 0, 0]]], ![![![5, -2, 0], ![21, 0, 0]], ![![1, 2, -1], ![4, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-2, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![-173, 51, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![-6, 3, 0], ![-2, -1, 1]]]
 hmul := by decide
 f := ![![![![-168296, 10502, -36425], ![196348, 47460, 0]], ![![-493664, 144304, 0], ![123416, -397, 0]]]]
 g := ![![![![76, -13, -4]], ![![232, -7, -7]]], ![![![52, 2, -1]], ![![69, 11, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![366968866580983496047977168694, -108172518669456857672017183733, 14863166671671684984844186828])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
