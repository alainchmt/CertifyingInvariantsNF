import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_406700_5.RI3_1_406700_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![1, -7, -1]

def alpha1 := B.equivFun.symm ![6, -22, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-5, 18, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![17, 0, 0], ![-2, 1, 0]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![289, 0, 0], ![-53, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-34, 17, 0]], ![![-34, 17, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-87108969, 44142609, -298482], ![-739253619, 4465781, 0]], ![![0, 0, 0], ![10162685, -60112, 0]]], ![![![15993834, -8104900, 54803], ![135732288, -819942, 0]], ![![0, 0, 0], ![-1865942, 11037, 0]]]]
 g := ![![![![4135, -78, 0], ![22542, 0, 0]], ![![-474, 62, -1], ![-2584, 289, 0]]], ![![![-474, 62, -1], ![-2584, 289, 0]], ![![62, -1, 0], ![338, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![289, 0, 0], ![-53, 1, 0]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![1, -7, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-578, 289, 0]], ![![-901, 17, 0], ![106, -55, 1]]]
 hmul := by decide
 f := ![![![![1717300004, -869316964, 4784107], ![14595835034, -80940702, 0]], ![![777600, -6615024, 0], ![-15552, -299, 0]]]]
 g := ![![![![-4824, 83, -104]], ![![488, -6, 11]]], ![![![880, -15, 19]], ![![-89, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![17, 0, 0], ![-1, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![289, 0, 0], ![84, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-17, 17, 0]], ![![-17, 17, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, -3294, -2315], ![0, 68, 0]], ![![0, 0, 0], ![620194, -47685, 0]]], ![![![0, -956, -673], ![0, 31, 0]], ![![0, 0, 0], ![180121, -13849, 0]]]]
 g := ![![![![10501, 125, 0], ![-36125, 0, 0]], ![![-677, -92, -1], ![2329, 289, 0]]], ![![![-677, -92, -1], ![2329, 289, 0]], ![![-59, -1, 0], ![203, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![289, 0, 0], ![84, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![6, -22, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-289, 289, 0]], ![![1428, 17, 0], ![-84, 83, 1]]]
 hmul := by decide
 f := ![![![![49554, -422797, -5992], ![441868, 21609, 0]], ![![-80110, 1369480, 0], ![16022, -1232, 0]]]]
 g := ![![![![-26154, 408, -559]], ![![1111, -17, 24]]], ![![![-7627, 119, -163]], ![![324, -5, 7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![15163, -234, 324])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![84, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![17, 0, 0], ![-2, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![17, 0, 0], ![36, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-17, 17, 0]], ![![-34, 17, 0], ![2, -3, 1]]]
 hmul := by decide
 f := ![![![![-12044, 9192, -11], ![-107387, 178, 0]], ![![-48672, 0, 0], ![153, 0, 0]]], ![![![-25300, 19308, -22], ![-225584, 355, 0]], ![![-102240, 0, 0], ![324, 0, 0]]]]
 g := ![![![![-19, 3, -1], ![17, 0, 0]], ![![-1, 1, 0], ![0, 0, 0]]], ![![![-2, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![36, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![17, 0, 0], ![-2, 1, 0]] ![![289, 0, 0], ![84, 1, 0]]
  ![![289, 0, 0], ![-100, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4913, 0, 0], ![1428, 17, 0]], ![![-578, 289, 0], ![-168, 82, 1]]]
 hmul := by decide
 f := ![![![![875643567, 11727034, 15529], ![-3012618909, -4488034, 0]], ![![28729, 0, 0], ![2601, 0, 0]]], ![![![-302698962, -4053957, -5369], ![1041424446, 1551694, 0]], ![![-9931, 0, 0], ![-900, 0, 0]]]]
 g := ![![![![198892, -3087511, 316876], ![-217039, -6090675, 0]], ![![57875, -897276, 92087], ![-62858, -1770019, 0]]], ![![![-23461, 365646, -37529], ![25976, 721327, 0]], ![![-6754, 106252, -10907], ![7734, 209626, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![-100, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![-53, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![289, 0, 0], ![-53, 1, 0]] ![![17, 0, 0], ![-1, 1, 0]]
  ![![289, 0, 0], ![-83, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-289, 289, 0]], ![![-901, 17, 0], ![53, -54, 1]]]
 hmul := by decide
 f := ![![![![-152081736, 81281311, -242342], ![-1356062145, 4150478, 0]], ![![-394312688, -521152, 0], ![-2312, 0, 0]]], ![![![43679616, -23344923, 69603], ![389476576, -1192058, 0]], ![![113251119, 149680, 0], ![664, 0, 0]]]]
 g := ![![![![5012, -62190, 7215], ![-4335, -138720, 0]], ![![-219, 3669, -428], ![527, 8211, 0]]], ![![![-863, 11397, -1324], ![991, 25443, 0]], ![![82, -680, 78], ![49, -1506, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![-83, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![289, 0, 0], ![-53, 1, 0]] ![![289, 0, 0], ![84, 1, 0]]
  ![![289, 0, 0], ![172, 31, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![83521, 0, 0], ![24276, 289, 0]], ![![-15317, 289, 0], ![-4452, 31, 1]]]
 hmul := by decide
 f := ![![![![8578692910413940819, 114887987585595676, 151913707735844], ![-29514781948915639259, -43903061535659163, 0]], ![![10705673850930, 0, 0], ![71383, 0, 0]]], ![![![5105659521164730640, 68376261256745209, 90412336284400], ![-17565895999103995990, -26129165186191747, 0]], ![![6371544732780, 0, 0], ![42484, 0, 0]]]]
 g := ![![![![117, -31, -1], ![289, 0, 0]], ![![-88, -30, -1], ![289, 0, 0]]], ![![![-53, 1, 0], ![0, 0, 0]], ![![-16, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![172, 31, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
