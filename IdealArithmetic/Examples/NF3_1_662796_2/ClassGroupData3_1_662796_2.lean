import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_662796_2.RI3_1_662796_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![132, 31, 5]

def alpha1 := B.equivFun.symm ![-117, -26, -4]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-271, -51, 12]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![3, 1, 0]] ![![7, 0, 0], ![3, 1, 0]]
  ![![49, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![21, 7, 0], ![8, 7, 3]]]
 hmul := by decide
 f := ![![![![679, -2387, -1809], ![-49, 4263, 0]], ![![0, 0, 0], ![-294, 0, 0]]], ![![![77521, -272335, -206415], ![-5680, 486435, 0]], ![![0, 0, 0], ![-33576, -4, 0]]]]
 g := ![![![![-127, -397, 396], ![49, -6468, 0]], ![![-54, -165, 165], ![7, -2695, 0]]], ![![![-54, -165, 165], ![7, -2695, 0]], ![![-19, -60, 60], ![10, -979, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![-4, 1, 0]] ![![7, 0, 0], ![3, 1, 0]]
  ![![132, 31, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![147, 49, 0]], ![![-28, 7, 0], ![-13, 0, 3]]]
 hmul := by decide
 f := ![![![![215485701, -787177127, -581509222], ![-20102854, 1368299943, 0]], ![![159582804, -80140602, 0], ![174600, -124, 0]]]]
 g := ![![![![-1070, -11, 13]], ![![414, -18, -1]]], ![![![212, -1, -2]], ![![-43, 8, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![5, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![17, 0, 0], ![5, 1, 0]] ![![17, 0, 0], ![5, 1, 0]]
  ![![17, 0, 0], ![-43, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![85, 17, 0]], ![![85, 17, 0], ![24, 11, 3]]]
 hmul := by decide
 f := ![![![![-1055737286, 6471974091, 3233772348], ![70193407, -18295664372, 0]], ![![0, 0, 0], ![-493480620, -29458, 0]]], ![![![2685467642, -16462691341, -8225712167], ![-178550181, 46538485964, 0]], ![![0, 0, 0], ![1255261380, 74932, 0]]]]
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![5, 1, 0], ![0, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![9, 1, 0], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![17, 0, 0], ![-43, -2, 1]] ![![17, 0, 0], ![5, 1, 0]]
  ![![-117, -26, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![289, 0, 0], ![85, 17, 0]], ![![-731, -34, 17], ![256, 21, -2]]]
 hmul := by decide
 f := ![![![![45099, -275350, -137680], ![-2924, 780260, 0]], ![![0, 0, 0], ![1872, 0, 0]]]]
 g := ![![![![391, 22, -8]], ![![-107, -5, 2]]], ![![![221, 4, -3]], ![![-18, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-35200, -8256, -1335])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-43, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![3, 1, 0]] ![![17, 0, 0], ![5, 1, 0]]
  ![![119, 0, 0], ![-46, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![119, 0, 0], ![35, 7, 0]], ![![51, 17, 0], ![14, 9, 3]]]
 hmul := by decide
 f := ![![![![-348149, 2130585, 1063689], ![22933, -6029016, 0]], ![![-30702, 595, 0], ![0, 0, 0]]], ![![![135152, -827128, -412941], ![-8886, 2340560, 0]], ![![11919, -231, 0], ![0, 0, 0]]]]
 g := ![![![![-253, -13501, 900], ![119, -35700, 0]], ![![-85, -3960, 264], ![7, -10472, 0]]], ![![![-121, -5760, 384], ![17, -15232, 0]], ![![-14, -1575, 105], ![54, -4164, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![119, 0, 0], ![-46, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![3, 1, 0]] ![![17, 0, 0], ![-43, -2, 1]]
  ![![119, 0, 0], ![-43, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![119, 0, 0], ![-301, -14, 7]], ![![51, 17, 0], ![342, 25, -4]]]
 hmul := by decide
 f := ![![![![5152, 10920, 39], ![-14280, 0, 0]], ![![-95676, 1869, 0], ![0, 0, 0]]], ![![![-1821, -3942, -15], ![5173, 0, 0]], ![![34554, -675, 0], ![0, 0, 0]]]]
 g := ![![![![204609, 13984, -2816], ![-74144, -58464, 0]], ![![-517151, -35346, 7117], ![187572, 147784, 0]]], ![![![87315, 5967, -1202], ![-31542, -24940, 0]], ![![587402, 40147, -8084], ![-212972, -167852, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![119, 0, 0], ![-43, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![-4, 1, 0]] ![![17, 0, 0], ![5, 1, 0]]
  ![![833, 0, 0], ![192, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![833, 0, 0], ![245, 49, 0]], ![![-68, 17, 0], ![-21, 2, 3]]]
 hmul := by decide
 f := ![![![![-57062088, 347237565, 173968428], ![3642777, -985848836, 0]], ![![24485202, 79968, 0], ![0, 0, 0]]], ![![![-13146665, 80000832, 40080972], ![839281, -227131900, 0]], ![![5641200, 18424, 0], ![0, 0, 0]]]]
 g := ![![![![-330240, 63699456, 990147], ![833, -274930817, 0]], ![![-97241, 18728333, 291114], ![882, -80832654, 0]]], ![![![26951, -5202315, -80865], ![17, 22453515, 0]], ![![8174, -1606147, -24966], ![642, 6932227, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![833, 0, 0], ![192, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![-4, 1, 0]] ![![17, 0, 0], ![-43, -2, 1]]
  ![![833, 0, 0], ![314, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![833, 0, 0], ![-2107, -98, 49]], ![![-68, 17, 0], ![643, 39, -11]]]
 hmul := by decide
 f := ![![![![30802938, -60115052, 3641581], ![-70626653, 0, 0]], ![![2563629138, 8377824, 0], ![0, 0, 0]]], ![![![11611540, -22661110, 1372739], ![-26623590, 0, 0]], ![![966391596, 3158124, 0], ![0, 0, 0]]]]
 g := ![![![![3783701, 3560588, -65878], ![1417766, -7636944, 0]], ![![-9568543, -9003998, 166591], ![-3584350, 19312272, 0]]], ![![![-309540, -291039, 5384], ![-115192, 624240, 0]], ![![2919641, 2747577, -50836], ![1094313, -5893152, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![833, 0, 0], ![314, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
