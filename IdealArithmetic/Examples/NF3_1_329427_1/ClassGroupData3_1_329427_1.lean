import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_329427_1.RI3_1_329427_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![8, 2, -1]

def alpha1 := B.equivFun.symm ![-15, -1, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-563, 19, 19]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 1, 2]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-56, -4, 0], ![-2, 0, 1]], ![![0, 0, 0], ![1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![56, 4, 0], ![5, 0, -2]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![0, 2, 0], ![0, 1, 2]]]
 hmul := by decide
 f := ![![![![-13, 0, 25], ![-500, 0, 50]], ![![990, 0, -99], ![-110, 0, 1]]]]
 g := ![![![![155, 41, 10]], ![![560, 148, 36]]], ![![![280, 74, 18]], ![![1008, 267, 65]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![12, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![4, 5, 2]]]
 hmul := by decide
 f := ![![![![-3, -164, -108], ![-30, 250, 0]], ![![0, 0, 0], ![100, 0, 0]]], ![![![-16, -1548, -1024], ![-314, 2372, 0]], ![![0, 0, 0], ![944, -1, 0]]]]
 g := ![![![![253, 21, 0], ![-525, 0, 0]], ![![82, 7, 0], ![-170, 0, 0]]], ![![![82, 7, 0], ![-170, 0, 0]], ![![28, 2, 0], ![-58, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![12, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![-15, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![60, 5, 0], ![24, 15, 2]]]
 hmul := by decide
 f := ![![![![11741, -185207, -145221], ![-32340, 376180, 0]], ![![2390, -65688, 0], ![239, 1, 0]]]]
 g := ![![![![141, 38, 9]], ![![258, 69, 17]]], ![![![108, 29, 7]], ![![200, 53, 13]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![110021, 29108, 7087])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![12, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![10, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![4, 2, 0]], ![![0, 5, 0], ![0, 3, 2]]]
 hmul := by decide
 f := ![![![![-469, 44603, 29793], ![8735, -74550, 0]], ![![-2700, 0, -54], ![0, 0, 0]]], ![![![-157, 14862, 9927], ![2913, -24840, 0]], ![![-901, 0, -18], ![0, 0, 0]]]]
 g := ![![![![553, 1521, 1001], ![264, -4978, -54]], ![![368, 1012, 666], ![178, -3312, -36]]], ![![![367, 1009, 664], ![181, -3302, -36]], ![![183, 504, 332], ![93, -1650, -18]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![12, 1, 0]]
  ![![50, 0, 0], ![12, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![24, 2, 0]], ![![0, 25, 0], ![0, 13, 2]]]
 hmul := by decide
 f := ![![![![-333771, 23675717, 3631188], ![786825, -45394750, 0]], ![![-196000, 0, -784], ![0, 0, 0]]], ![![![-83446, 5918910, 907794], ![196713, -11348650, 0]], ![![-49001, 0, -196], ![0, 0, 0]]]]
 g := ![![![![-507, 475596, 73346], ![9434, -1829338, -784]], ![![-260, 237791, 36672], ![4744, -914644, -392]]], ![![![-130, 118818, 18324], ![2371, -457022, -196]], ![![-74, 59408, 9162], ![1223, -228510, -98]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![12, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![20, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![8, 4, 0]], ![![0, 5, 0], ![0, 3, 2]]]
 hmul := by decide
 f := ![![![![8753, -3283, 1942], ![-20620, -9115, 0]], ![![48285, 3399, -18], ![0, 0, 0]]], ![![![-10, -2, -3], ![24, 10, 0]], ![![-33, -2, 0], ![0, 0, 0]]]]
 g := ![![![![91, -18, 0], ![-27, -81, -18]], ![![174, -35, 0], ![-70, -162, -36]]], ![![![174, -35, 0], ![-69, -162, -36]], ![![94, -18, 0], ![-17, -80, -18]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![12, 1, 0]]
  ![![100, 0, 0], ![12, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![48, 4, 0]], ![![0, 25, 0], ![0, 13, 2]]]
 hmul := by decide
 f := ![![![![40197297, -6497735, 219386], ![-83652900, -7338625, 0]], ![![53920800, 734624, -1568], ![0, 0, 0]]], ![![![5024659, -812218, 27423], ![-10456606, -917325, 0]], ![![6740097, 91828, -196], ![0, 0, 0]]]]
 g := ![![![![1725, -967, 0], ![268, 8624, -1568]], ![![856, -484, 0], ![188, 4312, -784]]], ![![![211, -121, 0], ![71, 1078, -196]], ![![101, -61, 0], ![73, 540, -98]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![12, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
