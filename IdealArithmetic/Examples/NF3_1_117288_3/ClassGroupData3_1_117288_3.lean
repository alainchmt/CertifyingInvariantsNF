import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_117288_3.RI3_1_117288_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![6434, -3957, 588]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![879, 164, -176]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![20, 0, 0], ![2, 1, 0]] ![![20, 0, 0], ![2, 1, 0]]
  ![![400, 0, 0], ![102, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![400, 0, 0], ![40, 20, 0]], ![![40, 20, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![384415, 51800, -7926], ![-2604920, 22284, -30830]], ![![306380, 249759, -12332], ![-11180, -133200, 0]]], ![![![98003, 13202, -2022], ![-664096, 5699, -7860]], ![![78120, 63684, -3144], ![-2848, -33963, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-5, 0, 0], ![20, 0, 0]]], ![![![-5, 0, 0], ![20, 0, 0]], ![![25, 0, 0], ![-98, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![400, 0, 0], ![102, 1, 0]] ![![20, 0, 0], ![2, 1, 0]]
  ![![8000, 0, 0], ![3702, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8000, 0, 0], ![800, 400, 0]], ![![2040, 20, 0], ![204, 104, 1]]]
 hmul := by decide
 f := ![![![![-24139873305, 115991327447, 0], ![3385579050, 23285507005, 0]], ![![93135582000, -465677910000, 0], ![2036934000, -25784000, 0]]], ![![![-11170742295, 53675063280, 0], ![1566678950, 10775383725, 0]], ![![43098552000, -215492760000, 0], ![942592552, -11931563, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-185, 0, 0], ![400, 0, 0]]], ![![![-9, 0, 0], ![20, 0, 0]], ![![1665, 0, 0], ![-3598, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8000, 0, 0], ![3702, 1, 0]] ![![20, 0, 0], ![2, 1, 0]]
  ![![160000, 0, 0], ![43702, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![160000, 0, 0], ![16000, 8000, 0]], ![![74040, 20, 0], ![7404, 3704, 1]]]
 hmul := by decide
 f := ![![![![-167286319606387034239, 3745229455449000115980, 0], ![170532840811811302390, 20290792873713989005, 0]], ![![324652685977929240000, -8116317149448231000000, 0], ![109971490680000, -29891680000, 0]]], ![![![-45692167216629395866, 1022962612517705663979, 0], ![46578913904222343620, 5542176450083929200, 0]], ![![88674823200934640240, -2216870580023366006000, 0], ![30037338098152, -8164538763, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2185, 0, 0], ![8000, 0, 0]]], ![![![-5, 0, 0], ![20, 0, 0]], ![![10925, 0, 0], ![-39998, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![160000, 0, 0], ![43702, 1, 0]] ![![20, 0, 0], ![2, 1, 0]]
  ![![3200000, 0, 0], ![-916298, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3200000, 0, 0], ![320000, 160000, 0]], ![![874040, 20, 0], ![87404, 43704, 1]]]
 hmul := by decide
 f := ![![![![-15138293508256375961539917, 2970663470377263676967063141, 0], ![147019344168037546252199170, 1362935673947274788069005, 0]], ![![1597580277154313464800000, -10903485391578189397260000000, 0], ![311249285813600000, -7125833600000, 0]]], ![![![4334746270285228757894079, -850629061424083535795327276, 0], ![-42097978444175653913976950, -390267260048792209582525, 0]], ![![-457456128994920897599760, 3122138080390335126118362000, 0], ![-89124093153141848, 2040433461237, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![45815, 0, 0], ![160000, 0, 0]]], ![![![6, 0, 0], ![20, 0, 0]], ![![274890, 0, 0], ![960002, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3200000, 0, 0], ![-916298, 1, 0]] ![![20, 0, 0], ![2, 1, 0]]
  ![![6434, -3957, 588]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64000000, 0, 0], ![6400000, 3200000, 0]], ![![-18325960, 20, 0], ![-1832596, -916296, 1]]]
 hmul := by decide
 f := ![![![![-2867822365243130531672488866215, 578488048933806684250630108384174, 0], ![28637620210166021159364256532606, -12657861616062070007817135509, 0]], ![![-14179995508979038692461459886, 2025257858569931201250808008217950, 0], ![-48621295445315540, -53061422193, 0]]]]
 g := ![![![![-384817123, -46895466, -17060817]], ![![-91370245, -11134790, -4050855]]], ![![![110189407, 13428154, 4885233]], ![![26163163, 3188361, 1159931]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-14576369, -1776356, -646240])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![400, 0, 0], ![102, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8000, 0, 0], ![3702, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![160000, 0, 0], ![43702, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3200000, 0, 0], ![-916298, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
