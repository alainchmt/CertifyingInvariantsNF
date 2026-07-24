import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_3037500000_7.RI5_1_3037500000_7

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-15494, 74713, -35713, -46552, -141563]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-416355, 88799, -67875, -113988, -357834]

def zeta2 := B.equivFun.symm ![27871707746025729, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![2, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![4, 4, -2, -2, -6]], ![![4, 4, -2, -2, -6], ![24, -23, 13, 16, 57]]]
 hmul := by decide
 f := ![![![![787757463012, 594326684286, -677500745700, -374895859389, -1797746007139], ![-1319797673460, 297509780143, -15104406810, 0, 110284596]], ![![0, 0, 0, 0, 0], ![3063461, -37457, -267, 0, 1]]], ![![![-717177250451, -541077168199, 616799135264, 341306549631, 1636674482897], ![1201548587041, -270853982506, 13751106723, 0, -100403496]], ![![0, 0, 0, 0, 0], ![-2788986, 34101, 243, 0, -1]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-454, -225, 103, 108, 322], ![-54, -62, -6, 0, 0]]], ![![![-454, -225, 103, 108, 322], ![-54, -62, -6, 0, 0]], ![![2719, 1382, -638, -670, -2001], ![335, 376, 36, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![4, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![4, 4, -2, -2, -6]], ![![28, -10, 6, 8, 26], ![30, -9, 11, 12, 43]]]
 hmul := by decide
 f := ![![![![-20762481539, -15664260656, 17857109620, 9881178573, 47383518888], ![34786698178, -7841529056, 398104929, 0, -2873796]], ![![0, 0, 0, 0, 0], ![-206916, 680, -2, 0, 0]]], ![![![-124693901709, -94075352909, 107245016310, 59343711254, 284572719993], ![208919589627, -47094122704, 2390911548, 0, -17259249]], ![![0, 0, 0, 0, 0], ![-1242681, 4084, -12, 0, 0]]]]
 g := ![![![![735, 370, -167, -176, -522], ![176, 200, 20, 0, 0]], ![![-517013, -255072, 114988, 120741, 357816], ![-120741, -139213, -13877, 0, -21]]], ![![![1483814, 732089, -330031, -346546, -1026991], ![346546, 399548, 39828, 0, 60]], ![![1705241, 841333, -379279, -398258, -1180240], ![398258, 459171, 45771, 0, 69]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![4, 0, 0, 0, 0], ![14, -3, 3, 4, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![8, 8, -4, -4, -12]], ![![28, -10, 6, 8, 26], ![30, -9, 11, 12, 43]]]
 hmul := by decide
 f := ![![![![7718748430448975294, 6715719576793255731, -5333439518363879532, -3762199554395027845, -14780874828517048306], ![-10486507580246295733, 1544628811773717193, -78455626016353502, 0, 247481404941848]], ![![14231315267498, -150641176562, -14818082931, 0, 0], ![401696805, -1320169, 3877, 0, -9]]], ![![![15425546079890459684, 13421041341727094862, -10658621380933559672, -7518574171834772702, -29538864729540162599], ![-20956779114357113618, 3086866106213542621, -156789780784644511, 0, 494579639464225]], ![![28440596479379, -301049118458, -29613223326, 0, 0], ![802771671, -2638294, 7748, 0, -18]]]]
 g := ![![![![-160, 429, 123, -252, 381], ![252, 0, 96, 0, 0]], ![![118, -375, -105, 220, -334], ![-220, -4, -84, 0, 0]]], ![![![-864, 2482, 710, -1454, 2223], ![1454, 8, 556, 0, 0]], ![![-844, 2477, 703, -1451, 2208], ![1451, 12, 554, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![14, -3, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![-15494, 74713, -35713, -46552, -141563]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![8, 8, -4, -4, -12]], ![![28, -6, 6, 8, 26], ![26, 15, 3, -2, 7]]]
 hmul := by decide
 f := ![![![![-1480281362021619458, -1287923275669945914, 1022836108419653740, 721506666749980507, 2834645135540032961], ![2011083944390820594, -296225749882369811, 15046029040530999, 0, -47240167730693]], ![![-4585522873015, 18587558925, 39341487759, 0, 0], ![23714749101, -37153552, 82460, 0, 0]]]]
 g := ![![![![-5470, 2849, -1814, -1781, -6574]], ![![28409, -10866, 9007, 11215, 38623]]], ![![![18958, -9805, 8728, 9903, 35320]], ![![-87169, 15379, -11278, -21555, -65380]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![7357150742275, -2482701464523, 1426969328867, 1755669472306, 5949858965136])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![53244018700387351, 475661232740110983, -165572817600232159, -231313712475559748, -731897584179683280])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![14, -3, 3, 4, 13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
