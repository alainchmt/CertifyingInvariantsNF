import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_888300_3.RI3_1_888300_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![57, 15, 1]

def alpha1 := B.equivFun.symm ![621, 171, 12]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![3929, 447, -51]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![-2, 1, 0]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![49, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![-14, 7, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-14865199, 7921092, -238114], ![-51598932, 1420832, 0]], ![![0, 0, 0], ![1717058, -1176, 0]]], ![![![7028105, -3745005, 112577], ![24395416, -671749, 0]], ![![0, 0, 0], ![-811806, 556, 0]]]]
 g := ![![![![967, -42, 0], ![2058, 0, 0]], ![![-250, 34, -1], ![-532, 49, 0]]], ![![![-250, 34, -1], ![-532, 49, 0]], ![![78, -3, 0], ![166, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![-23, 1, 0]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![57, 15, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![-98, 49, 0]], ![![-161, 7, 0], ![46, -25, 1]]]
 hmul := by decide
 f := ![![![![45467188874, -23992136204, 567689931], ![158977603054, -3925925642, 0]], ![![94534803, -334649727, 0], ![-4774485, -1308, 0]]]]
 g := ![![![![-1851, -125, 18]], ![![2406, 157, -23]]], ![![![1137, 76, -11]], ![![-1472, -95, 14]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 0, 0], ![8, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![21, 0, 0], ![8, 1, 0]] ![![21, 0, 0], ![8, 1, 0]]
  ![![21, 0, 0], ![-104, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![441, 0, 0], ![168, 21, 0]], ![![168, 21, 0], ![64, 16, 1]]]
 hmul := by decide
 f := ![![![![66576301, 9821726, 187462], ![-171200230, -3491242, 0]], ![![0, 0, 0], ![-9344420, -640, 0]]], ![![![-327680388, -48341363, -922669], ![842626538, 17183550, 0]], ![![0, 0, 0], ![45992080, 3150, 0]]]]
 g := ![![![![21, 0, 0], ![0, 0, 0]], ![![8, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![21, 0, 0], ![-104, -5, 1]] ![![21, 0, 0], ![8, 1, 0]]
  ![![621, 171, 12]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![441, 0, 0], ![168, 21, 0]], ![![-2184, -105, 21], ![-102, 6, 3]]]
 hmul := by decide
 f := ![![![![230053, 32721, 465], ![-591422, -12697, 0]], ![![0, 0, 0], ![20528, 0, 0]]]]
 g := ![![![![-1089, -51, 9]], ![![-102, -7, 1]]], ![![![2056, 139, -20]], ![![88, 8, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-516301, -142467, -10038])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![21, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![21, 0, 0], ![-104, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![-2, 1, 0]] ![![21, 0, 0], ![8, 1, 0]]
  ![![21, 0, 0], ![-93, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![147, 0, 0], ![56, 7, 0]], ![![-42, 21, 0], ![-16, 6, 1]]]
 hmul := by decide
 f := ![![![![1653481, 222329, 4671], ![-4249128, -98100, 0]], ![![121655, 0, 0], ![63, 0, 0]]], ![![![-7323479, -984745, -20691], ![18819936, 434551, 0]], ![![-538820, 0, 0], ![-279, 0, 0]]]]
 g := ![![![![555, 694, 90], ![-2184, -294, 0]], ![![238, 265, 34], ![-826, -112, 0]]], ![![![-132, -197, -26], ![630, 84, 0]], ![![-37, -75, -10], ![243, 32, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![21, 0, 0], ![-93, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![-2, 1, 0]] ![![21, 0, 0], ![-104, -5, 1]]
  ![![21, 0, 0], ![-707, -56, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![147, 0, 0], ![-728, -35, 7]], ![![-42, 21, 0], ![938, 56, -7]]]
 hmul := by decide
 f := ![![![![-1, 93, -3], ![33, 0, 0]], ![![-576, 10, 0], ![0, 0, 0]]], ![![![487, -3911, 113], ![-1313, 0, 0]], ![![24480, -353, 0], ![0, 0, 0]]]]
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![100, 9, -1], ![4, 0, 0]]], ![![![99, 9, -1], ![3, 0, 0]], ![![11, 0, 0], ![-1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![21, 0, 0], ![-707, -56, 7]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![-23, 1, 0]] ![![21, 0, 0], ![8, 1, 0]]
  ![![147, 0, 0], ![-114, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1029, 0, 0], ![392, 49, 0]], ![![-483, 21, 0], ![-184, -15, 1]]]
 hmul := by decide
 f := ![![![![-21995271667, -3134630631, -57706628], ![56546404470, 1211853705, 0]], ![![-966757918, -33894, 0], ![441, 0, 0]]], ![![![17056930062, 2430848602, 44750432], ![-43850700318, -939770330, 0]], ![![749703048, 26285, 0], ![-342, 0, 0]]]]
 g := ![![![![1220618049, 89975991, 3765139], ![-947188179, -393712746, 0]], ![![464994406, 34276348, 1434329], ![-360831205, -149984842, 0]]], ![![![-572944347, -42233722, -1767315], ![444599661, 184804356, 0]], ![![-218263052, -16088933, -673259], ![169370280, 70401206, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![147, 0, 0], ![-114, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![-23, 1, 0]] ![![21, 0, 0], ![-104, -5, 1]]
  ![![147, 0, 0], ![-644, -35, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1029, 0, 0], ![-5096, -245, 49]], ![![-483, 21, 0], ![3122, 161, -28]]]
 hmul := by decide
 f := ![![![![14474542, -29856097, 3068618], ![-64428219, 0, 0]], ![![710601465, -29771, 0], ![0, 0, 0]]], ![![![-63070372, 130093806, -13371080], ![280737088, 0, 0]], ![![-3096347024, 129715, 0], ![0, 0, 0]]]]
 g := ![![![![224363, 129187, 16297], ![-1012557, -134064, 0]], ![![-1107896, -638143, -80509], ![5001976, 662256, 0]]], ![![![-105473, -60773, -7668], ![476388, 63072, 0]], ![![678682, 390882, 49313], ![-3063817, -405648, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![147, 0, 0], ![-644, -35, 7]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
