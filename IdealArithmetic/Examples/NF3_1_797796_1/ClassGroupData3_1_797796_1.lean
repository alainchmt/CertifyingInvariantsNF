import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_797796_1.RI3_1_797796_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-209153, -46267, -5221]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![97702967, -5104226, -46088]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-77, -4, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-77, -4, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![2, 0, 0], ![-77, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-154, -8, 2]], ![![-154, -8, 2], ![249, 35, -5]]]
 hmul := by decide
 f := ![![![![21468087, -200924976, -18725202], ![-434032238, 0, 11773050]], ![![0, 0, 0], ![-223652, 0, -9]]], ![![![-830097528, 7769098944, 724041100], ![16782579437, 0, -455224587]], ![![0, 0, 0], ![8647877, 0, 348]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![9, 13, -1], ![-3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![-77, -3, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![4, 0, 0], ![-79, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![-154, -8, 2]], ![![-154, -6, 2], ![959, 75, -13]]]
 hmul := by decide
 f := ![![![![860, -7700, -713], ![-16600, 0, 450]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![-16214, 152192, 14079], ![328036, 0, -8892]], ![![0, 0, 0], ![79, 0, 0]]]]
 g := ![![![![36, -126, -17], ![-160, 0, 6]], ![![-447, 4630, 610], ![5884, 0, -219]]], ![![![-425, 4695, 618], ![5966, 0, -222]], ![![2899, -28020, -3696], ![-35617, 0, 1326]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0], ![-79, -3, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![4, 0, 0], ![-79, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0], ![-308, -16, 4]], ![![-158, -6, 2], ![1113, 83, -15]]]
 hmul := by decide
 f := ![![![![13361006582, -125499265836, -11542166252], ![-269171301954, 0, 7297735774]], ![![689310894, 0, 0], ![-412514, 0, -7]]], ![![![-267220097718, 2509985012722, 230843297054], ![5383425386933, 0, -145954697798]], ![![-13786216209, 0, 0], ![8250279, 0, 140]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![4, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![61, 7, -1], ![-11, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0], ![-79, -5, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![8, 0, 0], ![233, 15, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0], ![-308, -16, 4]], ![![-158, -10, 2], ![-307, 3, 1]]]
 hmul := by decide
 f := ![![![![118230, -1109104, -102243], ![-2382884, 0, 64638]], ![![3696, 0, 0], ![8, 0, 0]]], ![![![3442089, -32303176, -2977851], ![-69402500, 0, 1882608]], ![![107646, 0, 0], ![233, 0, 0]]]]
 g := ![![![![100, 60, 233], ![4476, 0, -98]], ![![-5952, -2432, -8876], ![-170974, 0, 3745]]], ![![![-3114, -1250, -4545], ![-87562, 0, 1918]], ![![-5919, -2439, -8927], ![-171935, 0, 3766]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![233, 15, -3]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![8, 0, 0], ![-75, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0], ![-616, -32, 8]], ![![466, 30, -6], ![1229, 7, -7]]]
 hmul := by decide
 f := ![![![![429090335722, -4028583891800, -371324394802], ![-8648472337508, 0, 234699778005]], ![![-4172225190, 0, 0], ![-969158, 0, -195]]], ![![![-4026847731537, 37806710049500, 3484736598667], ![81162585865638, 0, -2202567128805]], ![![39154728375, 0, 0], ![9095175, 0, 1830]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![73, -2, -1], ![16, 0, 0]]], ![![![2, 3, 0], ![-6, 0, 0]], ![![13, -1, 1], ![-15, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![-75, -1, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![16, 0, 0], ![-233, -11, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![16, 0, 0], ![-616, -32, 8]], ![![-150, -2, 2], ![2225, 147, -27]]]
 hmul := by decide
 f := ![![![![130641, -1228812, -112698], ![-2626710, 0, 71190]], ![![17808, 0, 0], ![-16, 0, 0]]], ![![![-1901847, 17894962, 1641189], ![38252241, 0, -1036725]], ![![-259329, 0, 0], ![233, 0, 0]]]]
 g := ![![![![303, -811, -102], ![-2996, 0, 90]], ![![-9173, 30789, 3830], ![113506, 0, -3405]]], ![![![-2197, 7599, 944], ![28006, 0, -840]], ![![33158, -110667, -13770], ![-408009, 0, 12240]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-233, -11, 3]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![16, 0, 0], ![-83, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![32, 0, 0], ![-1232, -64, 16]], ![![-466, -22, 6], ![1611, 153, -25]]]
 hmul := by decide
 f := ![![![![66677303012015, -626201370578124, -57692506641254], ![-1343519678126646, 0, 36464599061604]], ![![854982385140, 0, 0], ![-70718146, 0, -651]]], ![![![-346086953684025, 3250283304007688, 299451582051472], ![6973506899847988, 0, -189268633199964]], ![![-4437765712770, 0, 0], ![367060853, 0, 3379]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![6, -3, 0], ![16, 0, 0]]], ![![![2, -1, 0], ![6, 0, 0]], ![![54, 9, -1], ![-9, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-83, -1, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![-209153, -46267, -5221]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![32, 0, 0], ![-1232, -64, 16]], ![![-166, -2, 2], ![2841, 179, -35]]]
 hmul := by decide
 f := ![![![![-27559818518, 259127941750, 23784907955], ![554689584587, 0, -15044399572]], ![![-3863683369, 0, 0], ![209153, 0, 0]]]]
 g := ![![![![-8594, -419, 102]], ![![37284, 3045, -581]]], ![![![21462, 1164, -268]], ![![-32507, -4502, 715]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2257806251445977, -499452081267662, -56360660323200])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-77, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-77, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-79, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-79, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![233, 15, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-75, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-233, -11, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-83, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
