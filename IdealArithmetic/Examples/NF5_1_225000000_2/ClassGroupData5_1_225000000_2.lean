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
  ![![4, 0, 0, 0, 0], ![0, 6, 0, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![-14, 20, -8, -2, -10]], ![![16, -6, 2, 0, 2], ![-32, 55, -23, -6, -27]]]
 hmul := by decide
 f := ![![![![84, -26, -40, -31, -68], ![-74, 108, 0, 0, -6]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-79797, -246252, -184818, 15366, -294472], ![146178, -132174, 207000, 0, 48693]], ![![0, 0, 0, 0, 0], ![-5925, -153, -7, 0, 0]]]]
 g := ![![![![334, 1758, 3900, 1989, 2813], ![1934, -3540, -108, 0, 6]], ![![-1241, -6552, -14538, -7414, -10481], ![-7205, 13198, 402, 0, -21]]], ![![![1354, 7130, 15822, 8069, 11411], ![7846, -14362, -438, 0, 24]], ![![-2879, -15208, -33747, -17210, -24327], ![-16723, 30637, 933, 0, -48]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![0, 6, 0, 0, -1]] ![![2, 0, 0, 0, 0], ![-7, 10, -4, -1, -5]]
  ![![4, 0, 0, 0, 0], ![6, -3, 1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![-28, 40, -16, -4, -20]], ![![0, 12, 0, 0, -2], ![-42, 48, -12, -2, -15]]]
 hmul := by decide
 f := ![![![![-1952187350, 831489415, 1282612877, 1007578263, 2395010422], ![1933561882, -2939803671, -226095408, 0, -32479048]], ![![-41937771, -13815792, -700164, 0, 0], ![41145, 2142, -126, 0, -7]]], ![![![-1967704039, 838098355, 1292807529, 1015586851, 2414046791], ![1948930534, -2963170287, -227892476, 0, -32737194]], ![![-42271103, -13925604, -705729, 0, 0], ![41472, 2159, -127, 0, -7]]]]
 g := ![![![![410, 708, -428, -32, -1052], ![-272, -2112, 64, 0, 0]], ![![-6799, -11555, 6997, 521, 17217], ![4528, 34620, -1044, 0, 0]]], ![![![-1527, -2586, 1568, 117, 3858], ![1018, 7758, -234, 0, 0]], ![![-8415, -14301, 8662, 646, 21313], ![5603, 42849, -1293, 0, 0]]]]
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

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![0, 6, 0, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![6, -3, 1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
