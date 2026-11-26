import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_225000000_2.RI5_1_225000000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![2422, -2032, 692, 138, 851]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![1640, 830, 1218, 991, 2364]

def zeta2 := B.equivFun.symm ![-133, 209, -93, -18, -98]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![2, 0, 0, 0, 0], ![8, -3, 1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-14, 20, -8, -2, -10]], ![![-14, 20, -8, -2, -10], ![-44, 34, -10, -2, -13]]]
 hmul := by decide
 f := ![![![![-276347, 53335, 146660, 113148, 245026], ![271450, -384705, 6921, 0, 22353]], ![![0, 0, 0, 0, 0], ![-471, -24, 0, 0, -1]]], ![![![-76049, 14703, 40389, 31146, 67482], ![74704, -105879, 1884, 0, 6147]], ![![0, 0, 0, 0, 0], ![-129, -7, -1, 0, 0]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![257, 642, -120, 29, -210], ![-66, -298, -30, 0, 0]]], ![![![257, 642, -120, 29, -210], ![-66, -298, -30, 0, 0]], ![![406, 1002, -185, 46, -326], ![-107, -467, -47, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![8, -3, 1, 0, 1]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![4, 0, 0, 0, 0], ![8, 1, -5, -2, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-14, 20, -8, -2, -10]], ![![16, -6, 2, 0, 2], ![-32, 55, -23, -6, -27]]]
 hmul := by decide
 f := ![![![![84, -26, -40, -31, -68], ![-74, 108, 0, 0, -6]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-68538, -212326, -159445, 13144, -254057], ![125766, -113592, 178431, 0, 41955]], ![![0, 0, 0, 0, 0], ![-5107, -132, -6, 0, 0]]]]
 g := ![![![![88730, -76501, 61181, 17597, 66581], ![-10142, 22212, 300, 0, -6]], ![![-331261, 285585, -228379, -65685, -248539], ![37873, -82920, -1120, 0, 21]]], ![![![360852, -311099, 248787, 71555, 270747], ![-41254, 90328, 1220, 0, -24]], ![![-766626, 660924, -528534, -152014, -575190], ![87647, -191900, -2592, 0, 48]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![8, 1, -5, -2, -5]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![4, 0, 0, 0, 0], ![6, -3, 1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-28, 40, -16, -4, -20]], ![![16, 2, -10, -4, -10], ![-98, 131, -61, -16, -71]]]
 hmul := by decide
 f := ![![![![-426485563685248, 108108156953410, 229178518843018, 197444564346061, 421924459474410], ![421349789120378, -620159988715484, -4224773202202, 0, 13357456282968]], ![![296742390086, -20977181076, -177847350, 0, 0], ![-584085, -4990, 1234, 0, -7]]], ![![![-427850268279514, 108454090581730, 229911863659830, 198076364170065, 423274569061485], ![422698059828624, -622144429122958, -4238291988980, 0, 13400198601839]], ![![297691931495, -21044305635, -178416441, 0, 0], ![-585954, -5006, 1238, 0, -7]]]]
 g := ![![![![410, 708, -428, -32, -1052], ![-272, -2112, 64, 0, 0]], ![![-6799, -11555, 6997, 521, 17217], ![4528, 34620, -1044, 0, 0]]], ![![![379, 650, -396, -31, -972], ![-250, -1944, 60, 0, 0]], ![![-22700, -38593, 23366, 1739, 57496], ![15117, 115614, -3486, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![6, -3, 1, 0, 1]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![2422, -2032, 692, 138, 851]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-28, 40, -16, -4, -20]], ![![12, -6, 2, 0, 2], ![-18, 35, -15, -4, -17]]]
 hmul := by decide
 f := ![![![![1141417615022, -259961403870, -590347818797, -523934688193, -1087931728525], ![-1132276368891, 1657976109531, -10327424198, 0, -42208944764]], ![![-2552945847, 374618619, 11031777, 0, 0], ![139065, 519, 3243, 0, 0]]]]
 g := ![![![![11, 18, 2, -3, 28]], ![![-13, 54, -46, 24, 5]]], ![![![-30, -26, -18, 4, -60]], ![![9, -103, 71, -47, -31]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-5424574, 3240098, -817290, -84269, -1056426])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-190721077, 40049621, -221123523, -75455658, -207020810])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![8, -3, 1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![8, 1, -5, -2, -5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![6, -3, 1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
