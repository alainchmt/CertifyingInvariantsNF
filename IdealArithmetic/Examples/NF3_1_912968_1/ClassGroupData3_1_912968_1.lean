import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-44652, -71, 927]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![10952044939719060747743573477669218572084256, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-15, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-15, -2, 1]] ![![2, 0, 0], ![-15, -2, 1]]
  ![![2, 0, 0], ![-16, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-30, -4, 2]], ![![-30, -4, 2], ![-420, 67, -1]]]
 hmul := by decide
 f := ![![![![-4159624, 21933011, -2171485], ![8178515, 0, -479808]], ![![0, 0, 0], ![-4704, 0, -3]]], ![![![37437605, -197401748, 19543820], ![-73608360, 0, 4318374]], ![![0, 0, 0], ![42337, 0, 27]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, -1, 0], ![2, 0, 0]]], ![![![1, -1, 0], ![2, 0, 0]], ![![6, 47, -14], ![27, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![-16, -1, 1]] ![![2, 0, 0], ![-15, -2, 1]]
  ![![-44652, -71, 927]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![-30, -4, 2]], ![![-32, -2, 2], ![-218, 79, -5]]]
 hmul := by decide
 f := ![![![![73279, -387425, 37833], ![-143185, 0, 8520]], ![![0, 0, 0], ![71, 0, 0]]]]
 g := ![![![![193158203, 44386435, 9926722]], ![![1356374319, 311685549, 69706337]]], ![![![2220063664, 510155458, 114092772]], ![![15589487237, 3582357628, 801169733]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![4700271171721087694186, 749725791144472654331, -248410053772582659368])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-15, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-16, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
