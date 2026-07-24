import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_411060_1.RI3_1_411060_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![359141075, 7802570, 16776900]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2184829668498074427315359169244988351106323445205975533455651011405603853909090095117, -47466824636156703695410202018969053198364557612547939377165665414226221547261873752, -102062034718067844711471289432545816753157231745148554773375518789163576471825817996]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![13, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![13, -1, 1]] ![![5, 0, 0], ![13, -1, 1]]
  ![![359141075, 7802570, 16776900]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![65, -5, 5]], ![![65, -5, 5], ![55, 20, 10]]]
 hmul := by decide
 f := ![![![![72462771, 203184943, 54507193], ![158667677, 0, 0]], ![![0, 0, 0], ![-213924131, 0, 0]]]]
 g := ![![![![-9901, 1742, 80]], ![![13975, 1415, -2757]]], ![![![13975, 1415, -2757]], ![![68597, -20186, 4986]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![88475654165004707426505048599686081521563, -114660349344100430295571963792187679207720, 66922314675057588758230674409883315124764])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![13, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
