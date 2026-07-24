import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_933107_3.RI3_1_933107_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-31, 0, -1]

def alpha1 := B.equivFun.symm ![3837, -4, 124]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![13, -24, -54]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, -1, 8]]]
 hmul := by decide
 f := ![![![![-420, 446, 45], ![224, 0, 36]], ![![0, 0, 0], ![92, 0, 4]]], ![![![-175, 186, 26], ![93, 0, 15]], ![![0, 0, 0], ![45, 0, 2]]]]
 g := ![![![![1876, -2760, 261], ![252, 0, -348]], ![![-22, 32, -3], ![-2, 0, 4]]], ![![![-22, 32, -3], ![-2, 0, 4]], ![![949, -1396, 134], ![127, 0, -176]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-31, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![-13820544, 14810163, -600443], ![7405082, 0, 1194368]], ![![123969, 0, 3999], ![1209, 0, 31]]]]
 g := ![![![![-1, 1, 0]], ![![1, -1, 4]]], ![![![0, 0, 2]], ![![23, -31, 1]]]]
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
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![6, 3, 8]]]
 hmul := by decide
 f := ![![![![14250051, 7104693, 67622976], ![7120964, -42035904, 0]], ![![0, 0, 0], ![-1136300, -1495, 0]]], ![![![6796182, 3388394, 32250976], ![3396154, -20047904, 0]], ![![0, 0, 0], ![-541928, -713, 0]]]]
 g := ![![![![2469, 18644, 13616], ![1950, -42550, 0]], ![![958, 7295, 5328], ![780, -16650, 0]]], ![![![958, 7295, 5328], ![780, -16650, 0]], ![![590, 4458, 3256], ![467, -10174, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![12, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![3837, -4, 124]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![60, 5, 0], ![26, 13, 8]]]
 hmul := by decide
 f := ![![![![616798297749, 304347837244, 2885299088796], ![307588886549, -1801481156964, 0]], ![![-38482779166, -9114670948, 0], ![-192770988, -229471, 0]]]]
 g := ![![![![33, -44, 4]], ![![14, -27, -68]]], ![![![16, -23, -12]], ![![-58, 73, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3041701, -3180, 98298])
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
 M := ![![![10, 0, 0], ![4, 2, 0]], ![![0, 5, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![144, 362, 325], ![130, -200, 0]], ![![-1006, 0, -10], ![0, 0, 0]]], ![![![28, 72, 65], ![28, -40, 0]], ![![-201, 0, -2], ![0, 0, 0]]]]
 g := ![![![![-4, -45, -105], ![5, 135, -10]], ![![-2, -18, -42], ![4, 54, -4]]], ![![![-1, 0, 0], ![5, 0, 0]], ![![-9, -13, -49], ![6, 63, -2]]]]
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
 M := ![![![50, 0, 0], ![24, 2, 0]], ![![0, 25, 0], ![2, 11, 8]]]
 hmul := by decide
 f := ![![![![28375364, 213571919, 156052281], ![22163075, -487663300, 0]], ![![225270, 0, -50], ![0, 0, 0]]], ![![![6809876, 51255709, 37451414], ![5318988, -117035650, 0]], ![![54063, 0, -12], ![0, 0, 0]]]]
 g := ![![![![466823, 2785471, 2028273], ![167775, -12676625, -50]], ![![224010, 1336632, 973284], ![80504, -6082986, -24]]], ![![![-837, -4928, -3588], ![-250, 22425, 0]], ![![18292, 109207, 79521], ![6621, -497002, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![12, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![20, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![8, 4, 0]], ![![10, 5, 0], ![6, 3, 8]]]
 hmul := by decide
 f := ![![![![118544496, 59109090, 1669965], ![59239620, -1036530, 0]], ![![-283474868, 0, -15356], ![0, 0, 0]]], ![![![11826657, 5897051, 166605], ![5910074, -103410, 0]], ![![-28281027, 0, -1532], ![0, 0, 0]]]]
 g := ![![![![-582, -6913, -16359], ![-402, 42066, -3116]], ![![-232, -2734, -6468], ![-140, 16632, -1232]]], ![![![-289, -3417, -8085], ![-185, 20790, -1540]], ![![-177, -2052, -4865], ![-111, 12510, -924]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![12, 1, 0]]
  ![![100, 0, 0], ![-38, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![48, 4, 0]], ![![50, 25, 0], ![26, 13, 8]]]
 hmul := by decide
 f := ![![![![826241122428884, 6222179812555039, 4543970135610301], ![645482931268075, -14199906672885050, 0]], ![![-160786811540, 0, -382780], ![0, 0, 0]]], ![![![-313979397237693, -2364486847746620, -1726751387114295], ![-245289584583931, 5396098084391250, 0]], ![![61100500569, 0, 145460], ![0, 0, 0]]]]
 g := ![![![![-65427764, 1576555070, -323486007], ![40628190, 4043503030, -15580]], ![![-31344798, 755288155, -154974066], ![19463976, 1937141304, -7464]]], ![![![-32335625, 779163295, -159872895], ![20079250, 1998375575, -7700]], ![![-16814535, 405164990, -83133921], ![10441194, 1039155495, -4004]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![-38, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
