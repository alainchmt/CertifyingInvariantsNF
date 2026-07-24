import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_532652_1.RI3_1_532652_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![1329, 492, 52]

def alpha1 := B.equivFun.symm ![-10243, -820, 201]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![330383, 59108, -9934]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-43, -4, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-43, -4, 1]] ![![5, 0, 0], ![-43, -4, 1]]
  ![![1329, 492, 52]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-215, -20, 5]], ![![-215, -20, 5], ![-87, 74, -6]]]
 hmul := by decide
 f := ![![![![961, -8624, 834], ![-970, 0, 0]], ![![0, 0, 0], ![2658, 0, 0]]]]
 g := ![![![![169, 20, -4]], ![![289, -40, 1]]], ![![![289, -40, 1]], ![![-4615, -402, 94]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-41, -3, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![7, 0, 0], ![-41, -3, 1]] ![![7, 0, 0], ![-41, -3, 1]]
  ![![-10243, -820, 201]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-287, -21, 7]], ![![-287, -21, 7], ![229, 104, -9]]]
 hmul := by decide
 f := ![![![![-156, -72963, 2858], ![32701, 0, 0]], ![![0, 0, 0], ![40972, 0, 0]]]]
 g := ![![![![75969, 28118, 2971]], ![![218983, 81051, 8564]]], ![![![218983, 81051, 8564]], ![![631225, 233632, 24686]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-11761808977, -4353335788, -459981602])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-41, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-43, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-43, -4, 1]] ![![7, 0, 0], ![-41, -3, 1]]
  ![![35, 0, 0], ![-48, 11, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![35, 0, 0], ![-205, -15, 5]], ![![-301, -28, 7], ![69, 87, -8]]]
 hmul := by decide
 f := ![![![![57, 28, 0], ![-196, 0, 0]], ![![140, 0, 0], ![0, 0, 0]]], ![![![-36, -35, -1], ![276, 0, 0]], ![![-192, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, -2, 0], ![5, 0, 0]]], ![![![1, -3, 0], ![7, 0, 0]], ![![39, -6, -1], ![27, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![35, 0, 0], ![-48, 11, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
