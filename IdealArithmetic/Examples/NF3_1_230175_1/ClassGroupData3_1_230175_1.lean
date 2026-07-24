import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_230175_1.RI3_1_230175_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-19, 15, -6]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![2264, 539, -336]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![1, 1, 0]]
  ![![121, 0, 0], ![56, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![11, 11, 0]], ![![11, 11, 0], ![1, 2, 5]]]
 hmul := by decide
 f := ![![![![0, -15814, -38475], ![0, -18920, 0]], ![![0, 0, 0], ![1143571, -2178, 0]]], ![![![0, -7254, -17650], ![0, -8673, 0]], ![![0, 0, 0], ![524531, -999, 0]]]]
 g := ![![![![2073, 37, 0], ![-4477, 0, 0]], ![![107, 2, 0], ![-231, 0, 0]]], ![![![107, 2, 0], ![-231, 0, 0]], ![![-31, -1, 0], ![67, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![56, 1, 0]] ![![11, 0, 0], ![1, 1, 0]]
  ![![-19, 15, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![121, 121, 0]], ![![616, 11, 0], ![56, 57, 5]]]
 hmul := by decide
 f := ![![![![-1395852690, -715484195, -24173606], ![7550294106, 50863687, 0]], ![![1532717280, 25270560, 0], ![2504440, 477, 0]]]]
 g := ![![![![4456, 1041, 471]], ![![4901, 1142, 516]]], ![![![2471, 577, 261]], ![![2716, 633, 286]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-4933021, -1150520, -519869])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![56, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
