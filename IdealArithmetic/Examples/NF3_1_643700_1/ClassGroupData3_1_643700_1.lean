import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![1314841706305739, -65469205166340, -83594671704068]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461499, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-13, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-13, 0, 1]] ![![3, 0, 0], ![-13, 0, 1]]
  ![![1314841706305739, -65469205166340, -83594671704068]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-39, 0, 3]], ![![-39, 0, 3], ![26, -21, -5]]]
 hmul := by decide
 f := ![![![![166639242123240, -3075238337509651, -449149305563078], ![-871819817721687, 0, 0]], ![![0, 0, 0], ![-1314841706305739, 0, 0]]]]
 g := ![![![![-46671134026100672668244847461, 9385801594743105722169713876, -3358014631804873046682016844]], ![![-210226952383527585598115404541, 42277705612120322771113545660, -15125948765436779958397280195]]], ![![![-210226952383527585598115404541, 42277705612120322771113545660, -15125948765436779958397280195]], ![![-946953024191566973429155842954, 190437052582298105251008052685, -68133808556886952317317669707]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-4189845828102210266548993780494750128223924959414749095, -237665488373072912541775230498120218134769716486788198, 34591250072179483776936429959450170882447873600866124])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-13, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
