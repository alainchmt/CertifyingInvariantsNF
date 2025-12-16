import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1240312500_5.RI5_1_1240312500_5

open BigOperators Classical Matrix Polynomial
noncomputable section 


def alpha0 := B.equivFun.symm ![33937, 20880, 13147, 17954, -47580]

def alpha1 := B.equivFun.symm ![194, 109, 64, 85, -223]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![72622, -21683, 6662, 13571, -23580]

def zeta2 := B.equivFun.symm ![-924605, -3154467, -3847477, -4269764, 10021778]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]] i)))
def MulJ00 : IdealMulEqCertificate O ℤ timesTableO (J00) J00
  ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]] ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]]
  ![![33937, 20880, 13147, 17954, -47580]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-14, -12, -6, -8, 20]], ![![-14, -12, -6, -8, 20], ![71, 12, 13, 14, -40]]]
 hmul := by decide
 f :=  ![![![![307815, -152727, -16297, -49904, 81665], ![-86586, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![-33937, 0, 0, 0, 0]]]]
 g :=  ![![![![1291, -27, 511, 669, -1434]], ![![3439, -2568, -1375, -1198, 3251]]], ![![![3439, -2568, -1375, -1198, 3251]], ![![-334, -2968, -3402, -3730, 8813]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]] i)))
def MulJ10 : IdealMulEqCertificate O ℤ timesTableO (J10) J10
  ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![194, 109, 64, 85, -223]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-20, -14, -8, -10, 26]], ![![-20, -14, -8, -10, 26], ![62, 27, 16, 23, -61]]]
 hmul := by decide
 f :=  ![![![![954, -532, -262, -108, 193], ![-721, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![-291, 0, 0, 0, 0]]]]
 g :=  ![![![![7, 1, 4, 5, -11]], ![![24, 0, 10, 13, -28]]], ![![![24, 0, 10, 13, -28]], ![![79, -8, 24, 33, -69]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![3839530, -4678322, -1154911, -2111859, 4794084])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![13857272649, 7383951789, 4195642221, 5477637022, -14293747630])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulRJ0_1J1_1 : IdealMulEqCertificate O ℤ timesTableO (J0) J1
  ![![2, 0, 0, 0, 0], ![-7, -6, -3, -4, 10]] ![![2, 0, 0, 0, 0], ![-10, -7, -4, -5, 13]]
  ![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-20, -14, -8, -10, 26]], ![![-14, -12, -6, -8, 20], ![62, 32, 18, 24, -64]]]
 hmul := by decide
 f :=  ![![![![2, 4, 1, 2, -4], ![-4, 0, 0, 0, 0]], ![![6, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-2, 3, 0, 1, -1], ![-7, 0, 0, 0, 0]], ![![9, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![28, -30, -9, -18, 36], ![-30, 6, 0, 0, 0]], ![![-47, 41, 11, 24, -46], ![46, -9, 0, 0, 0]]], ![![![-17, 12, 3, 7, -13], ![15, -3, 0, 0, 0]], ![![224, -215, -61, -127, 248], ![-229, 45, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![6, 2, 2, 2, -6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulRJ0_1J1_1]
 rfl
