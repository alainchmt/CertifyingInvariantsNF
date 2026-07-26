import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF10_0_21144617347_1.RI10_0_21144617347_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-79, -9, -2, 60, 43, 9, -9, 7, 48, 188]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![80, 8, 2, -60, -43, -9, 9, -7, -48, -188]

def zeta2 := B.equivFun.symm ![37, 4, 1, -28, -20, -4, 4, -3, -22, -86]

def zeta3 := B.equivFun.symm ![36, 2, 1, -27, -18, -4, 4, -3, -21, -82]

def zeta4 := B.equivFun.symm ![88, 8, 2, -66, -47, -10, 10, -8, -53, -208]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0, 0, 0]] ![![5, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0, 0, 0]]
  ![![-79, -9, -2, 60, 43, 9, -9, 7, 48, 188]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![10, 5, 0, 0, 0, 0, 0, 0, 0, 0]], ![![10, 5, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 4, 1, 0, 0, 0, 0, 0, 0, 0]]]
 hmul := by decide
 f := ![![![![-97552980007470, -43530704138877, -211004305755057, -507351780553263, -617784876111143, -350010345072042, 81855852637799, 343172366275587, 135474810020243, 7824899375471], ![235462522913076, -9790809224907, 532912369048875, 1007620498115593, 1045526343950072, 352452527947612, -381372271406398, -666738210882649, -126616429152, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-174488024, 156118684, 552328860, 686159036, 6552956, 40656472, -267647480, -326667, -188, 0]]]]
 g := ![![![![-20, -33, -4, -1, 34, -4, 5, -3, 14, 53]], ![![-20, -14, -7, 7, 17, 3, 0, 1, 12, 49]]], ![![![-20, -14, -7, 7, 17, 3, 0, 1, 12, 49]], ![![6, -4, -6, -8, -3, 2, 1, 0, -4, -13]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-35, -2, -1, 27, 18, 4, -4, 3, 21, 82])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-123, -10, -3, 93, 65, 14, -14, 11, 74, 290])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-95, -12, 2, 71, 54, 8, -10, 7, 57, 221])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta4 : IsUnit zeta4 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-171, -21, 4, 126, 98, 13, -17, 12, 102, 395])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 0, 0, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
