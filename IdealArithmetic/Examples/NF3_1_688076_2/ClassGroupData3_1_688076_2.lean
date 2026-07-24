import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_688076_2.RI3_1_688076_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-6, -1, 0]

def alpha1 := B.equivFun.symm ![15, -4, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-19, 2, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![-1, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![49, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![-7, 7, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![38265853, -38168700, 80314520], ![-10919220, -284189840, 0]], ![![0, 0, 0], ![21638596, 15456, 0]]], ![![![4669346, -4657491, 9800284], ![-1332400, -34677928, 0]], ![![0, 0, 0], ![2640424, 1886, 0]]]]
 g := ![![![![1552, 9586, 3198], ![392, -78351, 0]], ![![-229, -1403, -468], ![-42, 11466, 0]]], ![![![-229, -1403, -468], ![-42, 11466, 0]], ![![60, 389, 130], ![41, -3184, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![6, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![-6, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![-49, 49, 0]], ![![42, 7, 0], ![-5, 5, 2]]]
 hmul := by decide
 f := ![![![![441534290, -293803078, 654049854], ![-105048191, -2292545880, 0]], ![![-1057454448, 23324109, 0], ![1940712, -1886, 0]]]]
 g := ![![![![2, -7, 2]], ![![-51, 7, -2]]], ![![![-7, 0, 0]], ![![1, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-1, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![121, 0, 0], ![-45, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![-11, 11, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![10370776, -10364055, 21160692], ![-1884975, -116887632, 0]], ![![0, 0, 0], ![5544726, 2640, 0]]], ![![![-3857613, 3855113, -7871136], ![701168, 43478656, 0]], ![![0, 0, 0], ![-2062470, -982, 0]]]]
 g := ![![![![80002, -4753725, 211302], ![-68970, -12783771, 0]], ![![-7439, 442207, -19656], ![6424, 1189188, 0]]], ![![![-7439, 442207, -19656], ![6424, 1189188, 0]], ![![1396, -80316, 3570], ![-1046, -215984, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![-45, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![15, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-121, 121, 0]], ![![-495, 11, 0], ![46, -46, 2]]]
 hmul := by decide
 f := ![![![![-326912962786, -296346705185, 631233179451], ![2778750692, -3473092099386, 0]], ![![-1728369883680, 14405796551, 0], ![-646235, 328, 0]]]]
 g := ![![![![-14, -33, -7]], ![![109, -11, -6]]], ![![![15, 11, 2]], ![![-32, 4, 2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-188, 43, -9])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-45, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![-1, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![77, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![77, 0, 0], ![-7, 7, 0]], ![![-11, 11, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![56, -55, 0], ![0, 0, 0]], ![![385, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![8, 0, 0]], ![![-5, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![7, 0, 0]]], ![![![0, 0, 0], ![11, 0, 0]], ![![0, 0, 0], ![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![77, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![-1, 1, 0]] ![![121, 0, 0], ![-45, 1, 0]]
  ![![847, 0, 0], ![76, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![847, 0, 0], ![-315, 7, 0]], ![![-121, 121, 0], ![46, -46, 2]]]
 hmul := by decide
 f := ![![![![26504251615456, -1575350473037911, 70023979049346], ![-22876378477029, -4236450730434725, 0]], ![![43067409, -118636, 0], ![0, 0, 0]]], ![![![2377062991300, -141287041870249, 6280177667886], ![-2051693193927, -379950748723183, 0]], ![![3862548, -10640, 0], ![0, 0, 0]]]]
 g := ![![![![79454, 6136603, 161490], ![14399, -68391015, 0]], ![![-29575, -2282274, -60060], ![-5075, 25435410, 0]]], ![![![-11409, -877798, -23100], ![-1573, 9782850, 0]], ![![4248, 333562, 8778], ![1572, -3717482, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![847, 0, 0], ![76, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![6, 1, 0]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![539, 0, 0], ![153, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![539, 0, 0], ![-49, 49, 0]], ![![66, 11, 0], ![-5, 5, 2]]]
 hmul := by decide
 f := ![![![![28476335750, 26782881894, -46380861912], ![49370195105, 255436614180, 0]], ![![-385291631725, -1522891776, 0], ![0, 0, 0]]], ![![![8083126554, 7602432621, -13165400908], ![14013935593, 72506747258, 0]], ![![-109366635047, -432279176, 0], ![0, 0, 0]]]]
 g := ![![![![2280916, 410145099, 5361408], ![1408407, -1444899456, 0]], ![![-207935, -37383017, -488670], ![-128233, 131696565, 0]]], ![![![279144, 50200051, 656214], ![172491, -176849673, 0]], ![![-21220, -3814878, -49868], ![-13084, 13439427, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![539, 0, 0], ![153, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![6, 1, 0]] ![![121, 0, 0], ![-45, 1, 0]]
  ![![5929, 0, 0], ![1770, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![5929, 0, 0], ![-2205, 49, 0]], ![![726, 121, 0], ![-269, -39, 2]]]
 hmul := by decide
 f := ![![![![2342290424675630764, -139220269417350249450, 6188310112110227448], ![-2021680483700443203, -374392761782497260286, 0]], ![![-92438736621, -69450542, 0], ![0, 0, 0]]], ![![![699249110332569018, -41561733124458328741, 1847409823636349412], ![-603536719747305236, -111768294329947941059, 0]], ![![-27595939283, -20733223, 0], ![0, 0, 0]]]]
 g := ![![![![2657956, 5628785555, 6360210], ![1749055, -18854842545, 0]], ![![-989775, -2093361191, -2365380], ![-646212, 7012169010, 0]]], ![![![325629, 689211414, 778770], ![213565, -2308663665, 0]], ![![-120729, -255373817, -288558], ![-78886, 855430192, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5929, 0, 0], ![1770, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
