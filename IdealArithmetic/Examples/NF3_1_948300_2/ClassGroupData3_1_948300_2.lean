import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![1426700321, 309682724, 79240070]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-447655111913397110, -48952286427462266, 27713281222931533]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![-1, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![121, 0, 0], ![21, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![-11, 11, 0], ![0, -1, 3]]]
 hmul := by decide
 f := ![![![![-4225412, -34635, 12791826], ![380985, -46899600, 0]], ![![0, 0, 0], ![-42834, -726, 0]]], ![![![-733336, -6011, 2220069], ![66121, -8139600, 0]], ![![0, 0, 0], ![-7435, -126, 0]]]]
 g := ![![![![-11780, 258719, 35280], ![121, -1422960, 0]], ![![1078, -23760, -3240], ![11, 130680, 0]]], ![![![1078, -23760, -3240], ![11, 130680, 0]], ![![-18, 21, 3], ![98, -120, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![21, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![1426700321, 309682724, 79240070]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-121, 121, 0]], ![![231, 11, 0], ![-22, 21, 3]]]
 hmul := by decide
 f := ![![![![18917468242869762, 156214845952643, -57221346023850908], ![-1705568490628826, 209812215035225110, 0]], ![![7247936514451, -6680917121566, 0], ![-505361596358, -8560201926, 0]]]]
 g := ![![![![234595, 244192, -81302]], ![![-1499571, -126495, 81380]]], ![![![-93671, 32899, -7384]], ![![-126716, -21941, 10315]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![125091995700007677741091631452339153, 27152744979979851079413208652512525, 6947708884481503870778229935099674])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![21, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
