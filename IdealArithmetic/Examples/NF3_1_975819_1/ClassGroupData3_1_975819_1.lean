import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-35068446765, 6111685617, -1984294325]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![1192750189641302820072362337334571632660907349, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-27, 3, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-27, 3, 1]] ![![2, 0, 0], ![-27, 3, 1]]
  ![![-35068446765, 6111685617, -1984294325]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-54, 6, 2]], ![![-54, 6, 2], ![-903, 23, 25]]]
 hmul := by decide
 f := ![![![![-119239930593, -664187291730, -70437875311], ![578239188022, 0, 0]], ![![0, 0, 0], ![-35068446765, 0, 0]]]]
 g := ![![![![-744278, 50914, 25995]], ![![-7076446, -8316, 114234]]], ![![![-7076446, -8316, 114234]], ![![55320795, -7833663, -3025265]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![985397084161214532953148659188911094612522366046040894404219564640835691412321910109949701, -171733787545803570204895736526087601102592992865146200778228504789969353719581012503830483, 55757184088465129528715630278031151691423948274979582693625425256891166200281808104636134])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-27, 3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
