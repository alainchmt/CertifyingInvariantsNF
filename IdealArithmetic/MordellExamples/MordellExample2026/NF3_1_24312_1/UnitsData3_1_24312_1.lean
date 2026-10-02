import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.RI3_1_24312_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![178361260665498855294599509801, 35938665342336427911821503300, 25318107466978248199411982702]

lemma isUnit_zeta1 : IsUnit zeta1 := by
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-179098485472199, -53763431635260, 67503788428502])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis)
   timesTableT_eq_Table _ (by norm_num)
  decide


-- Opus 5
lemma zeta1_coe : (zeta1 : K) =
  Adj.map (C (25318107466978248199411982702 / 3) * X ^ 2 +
  C 35938665342336427911821503300 * X + C 178361260665498855294599509801) := by
  show (((basisOfBuilderLists T ([-90, 3, 0, 1]) BQ).equivFun.symm
    ![178361260665498855294599509801, 35938665342336427911821503300,
      25318107466978248199411982702] : O) : K) = _
  rw [basisOfBuilderLists_apply_Fn]
  congr 1
  simp only [BQ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.isValue, List.ofFn_succ, List.ofFn_zero, ofList_cons, ofList_nil,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_zero, Polynomial.map_one, map_ofNat, algebraMap_int_eq, eq_intCast]
  simp only [Polynomial.map_ofNat, Polynomial.map_zero, Polynomial.map_one,
    Polynomial.map_natCast, Polynomial.map_intCast]
  simp only [← Polynomial.C_eq_natCast, ← Polynomial.C_1, ← map_ofNat Polynomial.C,
    ← Polynomial.C_mul, ← Polynomial.C_add]
  push_cast
  rw [show (3 : ℚ[X]) = C 3 from (map_ofNat Polynomial.C 3).symm]
  have h1 : C (3⁻¹ : ℚ) * C 3 = 1 := by rw [← Polynomial.C_mul]; norm_num
  have h2 : C (3⁻¹ : ℚ) * C (25318107466978248199411982702 : ℚ)
      = C (25318107466978248199411982702 / 3 : ℚ) := by rw [← Polynomial.C_mul]; norm_num
  linear_combination C (178361260665498855294599509801 : ℚ) * h1 +
    X * C (35938665342336427911821503300 : ℚ) * h1 + X ^ 2 * h2
