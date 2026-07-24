import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_455700_1.RI3_3_455700_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![331, -38, -13]

def alpha1 := B.equivFun.symm ![33, -4, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-26, 3, 1]

def zeta2 := B.equivFun.symm ![264, -5, -5]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![2, 2, 3]]]
 hmul := by decide
 f := ![![![![-11235, 3452, 90], ![-2592, 0, -144]], ![![0, 0, 0], ![18, 0, 0]]], ![![![-1249, 383, 10], ![-286, 0, -16]], ![![0, 0, 0], ![2, 0, 0]]]]
 g := ![![![![0, -1, -2], ![3, 6, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![166, -38, 0], ![23, -3, 6]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![331, -38, -13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![3, 3, 0], ![2, 2, 3]]]
 hmul := by decide
 f := ![![![![611963970, -173797985, -5142415], ![146055330, 0, 7864870]], ![![-121995097, 0, -483992], ![58226, 0, 41]]]]
 g := ![![![![-101, 20, -3]], ![![225, -81, 18]]], ![![![75, -27, 6]], ![![-488, 124, -23]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-3, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![121, 0, 0], ![41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-33, 11, 0], ![10, -6, 3]]]
 hmul := by decide
 f := ![![![![2490946863, -8539071830, 8672355240], ![-1455628394, -31802154120, 0]], ![![0, 0, 0], ![38726050, 5082, 0]]], ![![![840608898, -2881643068, 2926621635], ![-491224521, -10732133280, 0]], ![![0, 0, 0], ![13068710, 1715, 0]]]]
 g := ![![![![-4845, -249086, -18228], ![-3630, 735196, 0]], ![![1293, 68297, 4998], ![1100, -201586, 0]]], ![![![1293, 68297, 4998], ![1100, -201586, 0]], ![![-409, -20785, -1521], ![-289, 61348, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![41, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![33, -4, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-363, 121, 0]], ![![451, 11, 0], ![-122, 38, 3]]]
 hmul := by decide
 f := ![![![![1039237185534667, -3559629441503048, 3614774858278531], ![-607030999827906, -13254183469039730, 0]], ![![395047646580, 98874608280, 0], ![10152850, 1414, 0]]]]
 g := ![![![![1425, -50, -31]], ![![317, -9, -8]]], ![![![547, -19, -12]], ![![124, -4, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-92, 3, 2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1266, 355, -70])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![33, 0, 0], ![-14, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![33, 0, 0], ![-9, 3, 0]], ![![11, 11, 0], ![-2, -2, 3]]]
 hmul := by decide
 f := ![![![![-6078776, 20970015, -21261432], ![3564220, 77958496, 0]], ![![-99825, 0, 36], ![0, 0, 0]]], ![![![2532841, -8737562, 8858986], ![-1485095, -32482912, 0]], ![![41594, 0, -15], ![0, 0, 0]]]]
 g := ![![![![-433801, 8870434, -1903698], ![452850, 20945670, 1152]], ![![108461, -2217644, 475932], ![-113193, -5236500, -288]]], ![![![-180739, 3695886, -793180], ![188693, 8727060, 480]], ![![36160, -739173, 158635], ![-37709, -1745400, -96]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![-14, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![1, 1, 0]] ![![121, 0, 0], ![41, 1, 0]]
  ![![363, 0, 0], ![-80, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![363, 0, 0], ![123, 3, 0]], ![![121, 121, 0], ![42, 42, 3]]]
 hmul := by decide
 f := ![![![![-78665223355, -4061607688584, -297227571756], ![-60222163914, 11988178721200, 0]], ![![-14270982, 0, 234], ![0, 0, 0]]], ![![![17144994313, 885222692102, 64780405054], ![13125350935, -2612809669140, 0]], ![![3110344, 0, -51], ![0, 0, 0]]]]
 g := ![![![![4677277, -412359162, 15463742], ![-2166430, -1871106620, 234]], ![![1618874, -142721210, 5352140], ![-749701, -647606807, 81]]], ![![![2929798, -258299963, 9686420], ![-1357168, -1172052949, 147]], ![![1016530, -89614415, 3360600], ![-470547, -406631256, 51]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![363, 0, 0], ![-80, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![99, 0, 0], ![19, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![99, 0, 0], ![-27, 9, 0]], ![![11, 11, 0], ![-2, -2, 3]]]
 hmul := by decide
 f := ![![![![-1846396130, 6339113281, -6433404156], ![1079845613, 23590006594, 0]], ![![-32089860, -702090, 108], ![0, 0, 0]]], ![![![-359020143, 1232600813, -1250935083], ![209969215, 4586928808, 0]], ![![-6239672, -136517, 21], ![0, 0, 0]]]]
 g := ![![![![8694, 2519, 0], ![1755, -23040, 3456]], ![![-2180, -630, 0], ![-405, 5760, -864]]], ![![![1208, 350, 0], ![241, -3200, 480]], ![![-257, -71, 0], ![32, 641, -96]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![99, 0, 0], ![19, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![1, 1, 0]] ![![121, 0, 0], ![41, 1, 0]]
  ![![1089, 0, 0], ![-80, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1089, 0, 0], ![369, 9, 0]], ![![121, 121, 0], ![42, 42, 3]]]
 hmul := by decide
 f := ![![![![-98803583022887, -5101197832655978, -373304233784430], ![-75637559806534, 15056605045224028, 0]], ![![-17151658282, -70606232, 1065], ![0, 0, 0]]], ![![![7236319242375, 373608880431396, 27340593605617], ![5539652639526, -1102737344949240, 0]], ![![1256177874, 5171161, -78], ![0, 0, 0]]]]
 g := ![![![![256, 2007, 0], ![467, 28045, 1065]], ![![94, 684, 0], ![251, 9559, 363]]], ![![![46, 277, 0], ![210, 3871, 147]], ![![30, 96, 0], ![264, 1344, 51]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1089, 0, 0], ![-80, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
