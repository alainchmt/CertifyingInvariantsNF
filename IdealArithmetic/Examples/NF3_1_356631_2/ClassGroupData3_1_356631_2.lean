import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_356631_2.RI3_1_356631_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![323, -30, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![291110, 16243, -9483]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-25, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-25, -2, 1]] ![![3, 0, 0], ![-25, -2, 1]]
  ![![3, 0, 0], ![-25, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-75, -6, 3]], ![![-75, -6, 3], ![-131, 15, -1]]]
 hmul := by decide
 f := ![![![![9776592, -26285879, 3999669], ![-62614284, 0, 4218088]], ![![0, 0, 0], ![5673, 0, -2]]], ![![![-83099953, 223427619, -33996834], ![532215797, 0, -35853368]], ![![0, 0, 0], ![-48220, 0, 17]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]], ![![![0, 1, 0], ![3, 0, 0]], ![![23, 13, -3], ![8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![3, 0, 0], ![-25, -3, 1]] ![![3, 0, 0], ![-25, -2, 1]]
  ![![323, -30, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![9, 0, 0], ![-75, -6, 3]], ![![-75, -9, 3], ![-320, 3, 5]]]
 hmul := by decide
 f := ![![![![1287777, -3461515, 526636], ![-8248126, 0, 555640]], ![![0, 0, 0], ![323, 0, 0]]]]
 g := ![![![![11790, 3251, 780]], ![![8283, 2284, 548]]], ![![![-40857, -11266, -2703]], ![![-28705, -7915, -1899]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3397804423, -936919477, -224791584])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-25, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-25, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
