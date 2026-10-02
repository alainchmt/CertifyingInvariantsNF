import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.RI2_2_8104_1

namespace NF2_2_8104_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![4213, -80]

def v := B.equivFun.symm ![-1, 0]

def zeta1 := B.equivFun.symm ![45, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![9, 0], ![1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0], ![3, 3]], ![![3, 3], ![2027, 2]]]
 hmul := by decide
 f := ![![![![1843, -183], ![555, 0]], ![![0, 0], ![-9, 0]]], ![![![204, -21], ![64, 0]], ![![0, 0], ![-1, 0]]]]
 g := ![![![![0, -1], ![9, 0]], ![![0, 0], ![3, 0]]], ![![![0, 0], ![3, 0]], ![![222, -3], ![29, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![27, 0], ![1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0], ![9, 9]], ![![3, 3], ![2027, 2]]]
 hmul := by decide
 f := ![![![![552, -124], ![-233, 2]], ![![1827, 0], ![-27, 0]]], ![![![6, -69], ![-18, 0]], ![![676, 0], ![-1, 0]]]]
 g := ![![![![0, -1], ![27, 0]], ![![0, 0], ![9, 0]]], ![![![0, 0], ![3, 0]], ![![74, -1], ![29, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![81, 0], ![1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0], ![27, 27]], ![![3, 3], ![2027, 2]]]
 hmul := by decide
 f := ![![![![552, -124], ![301, 2]], ![![675, 0], ![-81, 0]]], ![![![2, -23], ![-6, 0]], ![![676, 0], ![-1, 0]]]]
 g := ![![![![0, -1], ![81, 0]], ![![0, 0], ![27, 0]]], ![![![0, 0], ![3, 0]], ![![25, 0], ![2, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![243, 0], ![163, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0], ![81, 81]], ![![3, 3], ![2027, 2]]]
 hmul := by decide
 f := ![![![![552, -124], ![367, 2]], ![![243, 0], ![-243, 0]]], ![![![369, 360], ![-1084, 2]], ![![163, 0], ![-163, 0]]]]
 g := ![![![![-162, -1], ![243, 0]], ![![-54, 0], ![81, 0]]], ![![![-2, 0], ![3, 0]], ![![-156, -1], ![245, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0], ![163, 1]] ![![3, 0], ![1, 1]]
  ![![729, 0], ![649, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0], ![243, 243]], ![![489, 3], ![2189, 164]]]
 hmul := by decide
 f := ![![![![78487196, -7371590], ![23705202, 0]], ![![-128785140, 0], ![-729, 0]]], ![![![69874060, -6562637], ![21103810, 0]], ![![-114652340, 0], ![-649, 0]]]]
 g := ![![![![-648, -1], ![729, 0]], ![![-216, 0], ![243, 0]]], ![![![-2, 0], ![3, 0]], ![![-143, 0], ![164, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![729, 0], ![649, 1]] ![![3, 0], ![1, 1]]
  ![![2187, 0], ![2107, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0], ![729, 729]], ![![1947, 3], ![2675, 650]]]
 hmul := by decide
 f := ![![![![1021354456, -100576626], ![306925944, 0]], ![![-1262170188, 0], ![-2187, 0]]], ![![![983993525, -96897554], ![295698657, 0]], ![![-1216000268, 0], ![-2107, 0]]]]
 g := ![![![![-2106, -1], ![2187, 0]], ![![-702, 0], ![729, 0]]], ![![![-2, 0], ![3, 0]], ![![-625, 0], ![650, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![2187, 0], ![2107, 1]] ![![3, 0], ![1, 1]]
  ![![6561, 0], ![4294, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0], ![2187, 2187]], ![![6321, 3], ![4133, 2108]]]
 hmul := by decide
 f := ![![![![16667632005, -1658929441], ![5002900857, 0]], ![![-19031427090, 0], ![-6561, 0]]], ![![![10908521846, -1085725197], ![3274265550, 0]], ![![-12455562860, 0], ![-4294, 0]]]]
 g := ![![![![-4293, -1], ![6561, 0]], ![![-1431, 0], ![2187, 0]]], ![![![-1, 0], ![3, 0]], ![![-1379, 0], ![2108, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![6561, 0], ![4294, 1]] ![![3, 0], ![1, 1]]
  ![![19683, 0], ![17416, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![19683, 0], ![6561, 6561]], ![![12882, 3], ![6320, 4295]]]
 hmul := by decide
 f := ![![![![159864865146, -15949624267], ![47971746963, 0]], ![![-268697612799, 0], ![-19683, 0]]], ![![![141452344225, -14112617804], ![42446575477, 0]], ![![-237750222248, 0], ![-17416, 0]]]]
 g := ![![![![-17415, -1], ![19683, 0]], ![![-5805, 0], ![6561, 0]]], ![![![-2, 0], ![3, 0]], ![![-3800, 0], ![4295, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![19683, 0], ![17416, 1]] ![![3, 0], ![1, 1]]
  ![![59049, 0], ![56782, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![59049, 0], ![19683, 19683]], ![![52248, 3], ![19442, 17417]]]
 hmul := by decide
 f := ![![![![5360620400811, -535757302045], ![1608287699592, 0]], ![![-6664278052566, 0], ![-59049, 0]]], ![![![5154816298309, -515188591250], ![1546542569023, 0]], ![![-6408424128788, 0], ![-56782, 0]]]]
 g := ![![![![-56781, -1], ![59049, 0]], ![![-18927, 0], ![19683, 0]]], ![![![-2, 0], ![3, 0]], ![![-16748, 0], ![17417, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![59049, 0], ![56782, 1]] ![![3, 0], ![1, 1]]
  ![![177147, 0], ![174880, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![177147, 0], ![59049, 59049]], ![![170346, 3], ![58808, 56783]]]
 hmul := by decide
 f := ![![![![152450583370850, -15242400289727], ![45736061027043, 0]], ![![-174391134218379, 0], ![-177147, 0]]], ![![![150499630362887, -15047339004710], ![45150763786059, 0]], ![![-172159401808160, 0], ![-174880, 0]]]]
 g := ![![![![-174879, -1], ![177147, 0]], ![![-58293, 0], ![59049, 0]]], ![![![-2, 0], ![3, 0]], ![![-56056, 0], ![56783, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![177147, 0], ![174880, 1]] ![![3, 0], ![1, 1]]
  ![![531441, 0], ![352027, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![531441, 0], ![177147, 177147]], ![![524640, 3], ![176906, 174881]]]
 hmul := by decide
 f := ![![![![4733912330615079, -473364434094148], ![1420182632173644, 0]], ![![-5274809765824293, 0], ![-531441, 0]]], ![![![3135747817743520, -313557030114088], ![940730262543147, 0]], ![![-3494038768995671, 0], ![-352027, 0]]]]
 g := ![![![![-352026, -1], ![531441, 0]], ![![-117342, 0], ![177147, 0]]], ![![![-1, 0], ![3, 0]], ![![-115841, 0], ![174881, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ011 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![531441, 0], ![352027, 1]] ![![3, 0], ![1, 1]]
  ![![1594323, 0], ![1414909, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010
 hI2 := rfl
 M := ![![![1594323, 0], ![531441, 531441]], ![![1056081, 3], ![354053, 352028]]]
 hmul := by decide
 f := ![![![![59214929684418354, -5921326438861516], ![17764534415185614, 0]], ![![-98333864800926354, 0], ![-1594323, 0]]], ![![![52551294151091522, -5254981625607301], ![15765437508494742, 0]], ![![-87268056919215182, 0], ![-1414909, 0]]]]
 g := ![![![![-1414908, -1], ![1594323, 0]], ![![-471636, 0], ![531441, 0]]], ![![![-2, 0], ![3, 0]], ![![-312413, 0], ![352028, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ012 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![1594323, 0], ![1414909, 1]] ![![3, 0], ![1, 1]]
  ![![4213, -80]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011
 hI2 := rfl
 M := ![![![4782969, 0], ![1594323, 1594323]], ![![4244727, 3], ![1416935, 1414910]]]
 hmul := by decide
 f := ![![![![2545330899553355, -254531309007335], ![763599863515343, 0]], ![![-3154893969034808, 0], ![-4213, 0]]]]
 g := ![![![![4213, 80]], ![![55431, 1431]]], ![![![3739, 71]], ![![49195, 1270]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow14 : J0 ^ 14 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-45, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0], ![1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0], ![1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0], ![1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0], ![163, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0], ![649, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0], ![2107, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0], ![4294, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     

lemma PowJ0_9 : J0 ^ 9 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19683, 0], ![17416, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     

lemma PowJ0_10 : J0 ^ 10 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![59049, 0], ![56782, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     

lemma PowJ0_11 : J0 ^ 11 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![177147, 0], ![174880, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     

lemma PowJ0_12 : J0 ^ 12 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![531441, 0], ![352027, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010]
 rfl     

lemma PowJ0_13 : J0 ^ 13 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1594323, 0], ![1414909, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011]
 rfl     

lemma PowJ0_0 : J0 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1, 0]] i)) := by
 simp only [pow_zero, one_mul, Set.range_unique, Matrix.cons_val_fin_one]
 rw [B_one_repr, Ideal.span_singleton_one, Ideal.one_eq_top]

end

end NF2_2_8104_1
