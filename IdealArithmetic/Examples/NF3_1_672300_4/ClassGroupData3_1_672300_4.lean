import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_672300_4.RI3_1_672300_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![6343, 354, 336]

def alpha1 := B.equivFun.symm ![2473, 138, 131]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-7433, 4221, -2554]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![49, 0, 0], ![-19, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![6, 3, 7]]]
 hmul := by decide
 f := ![![![![-323761521, 32496727, -7087518], ![-87860899, 0, 15639820]], ![![0, 0, 0], ![2688630, 0, -588]]], ![![![127191839, -12766553, 2784378], ![34516734, 0, -6144206]], ![![0, 0, 0], ![-1056246, 0, 231]]]]
 g := ![![![![248716, -3089937, 1082448], ![-159495, -7578144, -392]], ![![62192, -772553, 270636], ![-39858, -1894704, -98]]], ![![![62192, -772553, 270636], ![-39858, -1894704, -98]], ![![26651, -331094, 115987], ![-17089, -812016, -42]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![-19, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![6343, 354, 336]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![98, 49, 0]], ![![-133, 7, 0], ![-36, -18, 7]]]
 hmul := by decide
 f := ![![![![178916831895777639, -18055703881100918, 3704460118775934], ![48539708558636338, 0, -8643787182572904]], ![![392449885534270, 0, -54639231044], ![1509524106, 0, 100072]]]]
 g := ![![![![265, 78, -84]], ![![-1774, 157, 42]]], ![![![-367, -11, 42]], ![![828, -108, 7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![7, 0, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![7, 0, 0], ![7, 0, 1]] ![![7, 0, 0], ![7, 0, 1]]
  ![![49, 0, 0], ![-7, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![49, 0, 7]], ![![49, 0, 7], ![91, 21, 5]]]
 hmul := by decide
 f := ![![![![1390099010, -33888820, -177027786], ![1364809335, -123354105, 0]], ![![0, 0, 0], ![-3162040, -98, 0]]], ![![![-198585578, 4841260, 25289683], ![-194972757, 17622015, 0]], ![![0, 0, 0], ![451720, 14, 0]]]]
 g := ![![![![-3130, 16, 424], ![-20825, 49, 0]], ![![-3129, 16, 424], ![-20818, 49, 0]]], ![![![-3129, 16, 424], ![-20818, 49, 0]], ![![-5532, 5, 784], ![-38425, 14, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![49, 0, 0], ![-7, 0, 1]] ![![7, 0, 0], ![7, 0, 1]]
  ![![2473, 138, 131]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![343, 0, 0], ![343, 0, 49]], ![![-49, 0, 7], ![-7, 21, -9]]]
 hmul := by decide
 f := ![![![![-217575595772076, 5515953168476, 27886515169780], ![-213591807890666, 19306003149078, 0]], ![![-6438416326344, -137997462, 0], ![43592925, 12365, 0]]]]
 g := ![![![![19, 63, -50]], ![![1123, -168, 26]]], ![![![155, -42, 18]], ![![-673, 66, 11]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2697258607, 150539088, 142879381])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![7, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-7, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![7, 0, 1]]
  ![![7, 0, 0], ![3, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![49, 0, 7]], ![![14, 7, 0], ![170, -2, 3]]]
 hmul := by decide
 f := ![![![![9779961, -227328, -1247698], ![9601732, -867837, 0]], ![![-144384, 0, 0], ![-21, 0, 0]]], ![![![4192770, -97458, -534902], ![4116369, -372051, 0]], ![![-61899, 0, 0], ![-9, 0, 0]]]]
 g := ![![![![4, 3, -1], ![7, 0, 0]], ![![4, 3, 0], ![7, 0, 0]]], ![![![-1, 4, -1], ![7, 0, 0]], ![![20, 4, -1], ![10, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![2, 1, 0]] ![![49, 0, 0], ![-7, 0, 1]]
  ![![49, 0, 0], ![-11, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![343, 0, 0], ![-49, 0, 7]], ![![98, 49, 0], ![142, -16, 3]]]
 hmul := by decide
 f := ![![![![-87577804, 17179, 12511960], ![-613093145, 7168, 0]], ![![-103917, 0, 0], ![-147, 0, 0]]], ![![![19646523, -3844, -2806850], ![137537214, -1578, 0]], ![![23312, 0, 0], ![33, 0, 0]]]]
 g := ![![![![18719, -2528, 3568], ![-4312, -5880, 0]], ![![-2677, 360, -512], ![648, 843, 0]]], ![![![5353, -723, 1019], ![-1211, -1680, 0]], ![![7750, -1048, 1476], ![-1764, -2433, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-11, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-19, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![-19, 1, 0]] ![![7, 0, 0], ![7, 0, 1]]
  ![![49, 0, 0], ![-18, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![343, 0, 49]], ![![-133, 7, 0], ![23, -2, -18]]]
 hmul := by decide
 f := ![![![![610242079304, -15607302018, -77852815274], ![599120248562, -54150551994, 0]], ![![6650034888, 0, -4004], ![-147, 0, 0]]], ![![![-224344604021, 5737745904, 28621197400], ![-220255861527, 19907483532, 0]], ![![-2444766584, 0, 1472], ![54, 0, 0]]]]
 g := ![![![![47545, 209, -1507], ![-17444, 0, -3969]], ![![47545, 209, -1506], ![-17444, 0, -3969]]], ![![![-18463, -83, 585], ![6801, 0, 1542]], ![![3203, 13, -102], ![-1161, 0, -267]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-18, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![-19, 1, 0]] ![![49, 0, 0], ![-7, 0, 1]]
  ![![49, 0, 0], ![3, -10, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![2401, 0, 0], ![-343, 0, 49]], ![![-931, 49, 0], ![289, -16, -18]]]
 hmul := by decide
 f := ![![![![-8811614886, 89552, 1258867904], ![-61685278795, 751319, 0]], ![![7632896, 0, 0], ![-490, 0, 0]]], ![![![-539585829, 5496, 77087700], ![-3777343356, 46045, 0]], ![![467406, 0, 0], ![-30, 0, 0]]]]
 g := ![![![![46, 10, -1], ![49, 0, 0]], ![![-7, 0, 1], ![0, 0, 0]]], ![![![-19, 1, 0], ![0, 0, 0]], ![![4, 6, -1], ![31, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![3, -10, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
