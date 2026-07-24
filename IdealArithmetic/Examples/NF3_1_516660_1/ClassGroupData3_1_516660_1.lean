import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_516660_1.RI3_1_516660_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-2656419765356401952, -601161303094910252, -219981870307307186]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![566443906997401965335631674748042844558536749, 275406296500094998253679941770064391205911750, -120786952390280265743415075243374451008124030]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-19, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-19, -1, 1]] ![![2, 0, 0], ![-19, -1, 1]]
  ![![-2656419765356401952, -601161303094910252, -219981870307307186]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-38, -2, 2]], ![![-38, -2, 2], ![-68, 12, -2]]]
 hmul := by decide
 f := ![![![![-1683879306038016857, 14029963989265777840, -5098607676182226827], ![6432567574637157912, 0, 0]], ![![0, 0, 0], ![-3654656842573642149, 0, 0]]]]
 g := ![![![![-1978011428, -410315441, 206908700]], ![![-45728074943, -752208441, 1379938459]]], ![![![-45728074943, -752208441, 1379938459]], ![![200565184285, 21172902955, -13017750624]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1438106791938258274340285287383131972831231098040104296916588198349127539233461170727461551, -325450881033951721292846523410168724736035557214662193373318740279009315850743837067648950, -119091653329034401841610845926854780544283647166015990026168307837126294633363598364478970])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-19, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
