import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_649415_1.RI3_1_649415_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-5305, -125, 267]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![4491035, -390570, -11588]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![3, -3, 5]]]
 hmul := by decide
 f := ![![![![591, 235, -360], ![-117, 180, 0]], ![![0, 0, 0], ![90, -9, 0]]], ![![![-262, -105, 160], ![54, -80, 0]], ![![0, 0, 0], ![-40, 4, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![3, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![-1, 5, -5], ![2, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-12, 3, 0], ![6, -6, 5]]]
 hmul := by decide
 f := ![![![![-2203179, 626720, -778820], ![943303, 389410, 0]], ![![-4926560, 194705, 0], ![116688, -27, 0]]], ![![![326453, -92864, 115400], ![-139769, -57700, 0]], ![![729984, -28850, 0], ![-17290, 4, 0]]]]
 g := ![![![![-35, 99, -100], ![27, 540, 0]], ![![15, -35, 35], ![9, -189, 0]]], ![![![18, -45, 45], ![3, -243, 0]], ![![-6, 24, -25], ![26, 136, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![81, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![-27, 27, 0]], ![![-12, 3, 0], ![6, -6, 5]]]
 hmul := by decide
 f := ![![![![64967270, -5799877, -11361140], ![-23589046, 5680570, 0]], ![![522390900, 10108203, 0], ![350064, -81, 0]]], ![![![-3208809, 286462, 561140], ![1165093, -280570, 0]], ![![-25801500, -499256, 0], ![-17290, 4, 0]]]]
 g := ![![![![81, -200, 200], ![0, -3240, 0]], ![![-27, 70, -70], ![27, 1134, 0]]], ![![![-12, 30, -30], ![3, 486, 0]], ![![10, -16, 15], ![80, -242, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![243, 0, 0], ![-85, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![-81, 81, 0]], ![![-12, 3, 0], ![6, -6, 5]]]
 hmul := by decide
 f := ![![![![-107391592, 166964062, 105598090], ![-624602424, -61320272, -1122752]], ![![-3460149, -55392183, 0], ![1050192, -243, 0]]], ![![![37565268, -58403578, -36937910], ![218484216, 21449656, 392736]], ![![1210368, 19376023, 0], ![-367354, 85, 0]]]]
 g := ![![![![81, -3440, 200], ![0, -9720, 0]], ![![0, 1204, -70], ![81, 3402, 0]]], ![![![-3, 172, -10], ![3, 486, 0]], ![![30, -86, 5], ![80, -242, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-85, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![729, 0, 0], ![-328, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![-243, 243, 0]], ![![-255, 3, 0], ![87, -87, 5]]]
 hmul := by decide
 f := ![![![![-877683278, -52556424, -8677520], ![275042288, 4338760, 0]], ![![-2761347240, 70294284, 0], ![-81810, -729, 0]]], ![![![394898408, 23646853, 3904300], ![-123750517, -1952150, 0]], ![![1242420420, -31627697, 0], ![36809, 328, 0]]]]
 g := ![![![![81, -13160, 200], ![0, -29160, 0]], ![![81, 4606, -70], ![243, 10206, 0]]], ![![![301, 4605, -70], ![732, 10206, 0]], ![![119, -1645, 25], ![242, -3644, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![729, 0, 0], ![-328, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![2187, 0, 0], ![-1057, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0, 0], ![-729, 729, 0]], ![![-984, 3, 0], ![330, -330, 5]]]
 hmul := by decide
 f := ![![![![5326450994, 377543267, 13657420], ![-1649635906, -6828710, 0]], ![![13048393680, -332151435, 0], ![108864, -2187, 0]]], ![![![-2574324045, -182470226, -6600760], ![797284609, 3300380, 0]], ![![-6306411840, 160531924, 0], ![-52615, 1057, 0]]]]
 g := ![![![![-2255455, 1667297120, -7879480], ![1854576, 3446484552, 0]], ![![753221, -556507717, 2630000], ![-618192, -1150362000, 0]]], ![![![1015380, -750172403, 3545240], ![-833244, -1550687976, 0]], ![![-340566, 251917078, -1190535], ![280664, 520740010, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![2187, 0, 0], ![-1057, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![-5305, -125, 267]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0, 0], ![-2187, 2187, 0]], ![![-3171, 3, 0], ![1059, -1059, 5]]]
 hmul := by decide
 f := ![![![![-114301524808845153, -8457747477493939, -89422532748008], ![35281259110450407, 44711266374004, 0]], ![![-260756145520164040, 6518902631691966, 0], ![5688125, -10610, 0]]]]
 g := ![![![![-12823274, -1673787, -857498]], ![![-41717162, -5445228, -2789645]]], ![![![6134534, 800724, 410219]], ![![19957099, 2604946, 1334540]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow8 : J0 ^ 8 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-12303557314429, -1605949912602, -822744334448])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-85, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![-328, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![-1057, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
