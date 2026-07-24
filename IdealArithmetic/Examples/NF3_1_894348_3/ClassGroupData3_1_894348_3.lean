import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_894348_3.RI3_1_894348_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![5, -2, 1]

def alpha1 := B.equivFun.symm ![11, 1, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6553, 986, -1027]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![25, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![1, 2, 7]]]
 hmul := by decide
 f := ![![![![0, -6730, -11403], ![0, -17300, 0]], ![![0, 0, 0], ![127425, -100, 0]]], ![![![0, -135, -231], ![0, -344, 0]], ![![0, 0, 0], ![2549, -2, 0]]]]
 g := ![![![![0, -1, 0], ![25, 0, 0]], ![![0, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![5, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![25, 25, 0]], ![![5, 5, 0], ![1, 2, 7]]]
 hmul := by decide
 f := ![![![![0, -640, -5826], ![-2184, 3032, 12]], ![![0, -468, 0], ![30581, -24, 0]]]]
 g := ![![![![389, 36, 23]], ![![915, 85, 55]]], ![![![183, 17, 11]], ![![437, 40, 26]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-4, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-4, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![121, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-44, 11, 0]], ![![-44, 11, 0], ![16, -8, 7]]]
 hmul := by decide
 f := ![![![![11756995, -3183435, 435267], ![30597413, -264869, 0]], ![![0, 0, 0], ![-4624862, -1815, 0]]], ![![![-408090, 110501, -15113], ![-1062048, 9201, 0]], ![![0, 0, 0], ![160532, 63, 0]]]]
 g := ![![![![373, -93, 0], ![11253, 0, 0]], ![![-132, 37, -7], ![-3982, 121, 0]]], ![![![-132, 37, -7], ![-3982, 121, 0]], ![![56, -14, 0], ![1690, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![-4, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![11, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-484, 121, 0]], ![![-44, 11, 0], ![16, -8, 7]]]
 hmul := by decide
 f := ![![![![-1372443, 694599, -615040], ![-3619419, -462896, 0]], ![![-1857591, 15760671, 0], ![-412798, -162, 0]]]]
 g := ![![![![-61, 15, -4]], ![![-44, -11, 11]]], ![![![-4, -1, 1]], ![![18, 0, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![227239013, 20961696, 13535303])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![55, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![55, 0, 0], ![-20, 5, 0]], ![![11, 11, 0], ![-4, -3, 7]]]
 hmul := by decide
 f := ![![![![825, -251, -210], ![2145, -154, 0]], ![![-220, 220, 0], ![0, 0, 0]]], ![![![-60, 23, 14], ![-156, 22, 0]], ![![16, -20, 0], ![0, 0, 0]]]]
 g := ![![![![65, -16, 0], ![880, 0, 0]], ![![-20, 9, -7], ![-270, 55, 0]]], ![![![13, -3, 0], ![176, 0, 0]], ![![-4, 1, 0], ![-54, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![55, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![1, 1, 0]] ![![121, 0, 0], ![-4, 1, 0]]
  ![![605, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![605, 0, 0], ![-20, 5, 0]], ![![121, 121, 0], ![-4, -3, 7]]]
 hmul := by decide
 f := ![![![![1134249, -283749, -2849], ![34296361, -9317, 0]], ![![-2420, 2420, 0], ![0, 0, 0]]], ![![![-7500, 1879, 21], ![-226778, 121, 0]], ![![16, -20, 0], ![0, 0, 0]]]]
 g := ![![![![1825, -456, 0], ![275880, 0, 0]], ![![-60, 19, -7], ![-9070, 605, 0]]], ![![![365, -91, 0], ![55176, 0, 0]], ![![-12, 3, 0], ![-1814, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![605, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![275, 0, 0], ![51, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![275, 0, 0], ![-100, 25, 0]], ![![11, 11, 0], ![-4, -3, 7]]]
 hmul := by decide
 f := ![![![![-3203, 989, 826], ![-8327, 638, 0]], ![![4400, -4400, 0], ![0, 0, 0]]], ![![![-587, 182, 147], ![-1525, 121, 0]], ![![816, -800, 0], ![0, 0, 0]]]]
 g := ![![![![6172, 121, 0], ![-33275, 0, 0]], ![![-2300, -96, -7], ![12400, 275, 0]]], ![![![202, 4, 0], ![-1089, 0, 0]], ![![-92, -2, 0], ![496, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![275, 0, 0], ![51, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![1, 1, 0]] ![![121, 0, 0], ![-4, 1, 0]]
  ![![3025, 0, 0], ![601, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3025, 0, 0], ![-100, 25, 0]], ![![121, 121, 0], ![-4, -3, 7]]]
 hmul := by decide
 f := ![![![![28007452, -7008812, -2926], ![847155848, -227601, 0]], ![![-57475, 57475, 0], ![0, 0, 0]]], ![![![5564452, -1392490, -581], ![168310850, -45133, 0]], ![![-11419, 11400, 0], ![0, 0, 0]]]]
 g := ![![![![88348, 147, 0], ![-444675, 0, 0]], ![![-3010, -606, -7], ![15150, 3025, 0]]], ![![![2380, 4, 0], ![-11979, 0, 0]], ![![-1082, -2, 0], ![5446, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3025, 0, 0], ![601, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
