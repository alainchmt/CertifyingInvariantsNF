import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_344763_1.RI3_1_344763_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-49, 131, -25]

def alpha1 := B.equivFun.symm ![-8842554204, -1829019137, -378319536]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![2462929921, -147738928, -74815168]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 1]] ![![2, 0, 0], ![1, 1, 1]]
  ![![-49, 131, -25]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 2]], ![![2, 2, 2], ![227, 115, 3]]]
 hmul := by decide
 f := ![![![![-2192, -775, 558], ![-1202, 0, 0]], ![![0, 0, 0], ![49, 0, 0]]]]
 g := ![![![![-93119, -19261, -3984]], ![![-1359902, -281286, -58182]]], ![![![-1359902, -281286, -58182]], ![![-19859893, -4107877, -849685]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 2, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![-1, 2, 1]] ![![5, 0, 0], ![-1, 2, 1]]
  ![![-8842554204, -1829019137, -378319536]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-5, 10, 5]], ![![-5, 10, 5], ![453, 109, 2]]]
 hmul := by decide
 f := ![![![![-473053333749, -131696999651, -10118960739], ![39908074743, 0, 0]], ![![0, 0, 0], ![26527662612, 0, 0]]]]
 g := ![![![![98208, -1860, -3817]], ![![-234206, -46609, 19661]]], ![![![-234206, -46609, 19661]], ![![-117845, 359978, -69417]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![4817022058571097089, 996366584271774000, 206091306658430912])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 1]] ![![5, 0, 0], ![-1, 2, 1]]
  ![![10, 0, 0], ![-1, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![-2, 4, 2]], ![![5, 5, 5], ![338, 114, 2]]]
 hmul := by decide
 f := ![![![![7, 3, 4], ![5, 0, 0]], ![![-10, 0, 0], ![0, 0, 0]]], ![![![0, -2, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]], ![![![0, -1, 1], ![-5, 0, 0]], ![![34, 12, 0], ![2, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-1, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
