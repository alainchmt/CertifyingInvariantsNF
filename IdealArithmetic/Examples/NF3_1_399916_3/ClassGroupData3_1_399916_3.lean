import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_399916_3.RI3_1_399916_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![3568807, 536804, 190078]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![221553, 166896, -61627]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![121, 0, 0], ![-31, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![22, 11, 0]], ![![22, 11, 0], ![5, 4, 2]]]
 hmul := by decide
 f := ![![![![2227375, 4879752, 5023950], ![848595, -27999279, 0]], ![![0, 0, 0], ![4052169, -1815, 0]]], ![![![-576785, -1263624, -1300964], ![-219741, 7250481, 0]], ![![0, 0, 0], ![-1049319, 470, 0]]]]
 g := ![![![![-3481, 123302, -7956], ![1936, 481338, 0]], ![![-618, 22131, -1428], ![374, 86394, 0]]], ![![![-618, 22131, -1428], ![374, 86394, 0]], ![![-121, 4990, -322], ![156, 19482, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![-31, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![3568807, 536804, 190078]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![242, 121, 0]], ![![-341, 11, 0], ![-61, -29, 2]]]
 hmul := by decide
 f := ![![![![-169878301811432639, -379247615060524731, -384750224478791736], ![-65364019880308174, 2116158647065137831, 0]], ![![41422744146594632, -356545826599302, 0], ![98423163738, -50848085, 0]]]]
 g := ![![![![-81911, 3880, 2598]], ![![14274, -6741, 1414]]], ![![![23637, -1671, -580]], ![![-2287, 1845, -462]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1109197501052, 166840530565, 59076896571])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-31, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
