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
  ![![8, 0, 0], ![-75, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0], ![-308, -16, 4]], ![![-158, -10, 2], ![-307, 3, 1]]]
 hmul := by decide
 f := ![![![![118230, -1109104, -102243], ![-2382884, 0, 64638]], ![![3696, 0, 0], ![8, 0, 0]]], ![![![-1107953, 10398024, 958536], ![22339872, 0, -605990]], ![![-34650, 0, 0], ![-75, 0, 0]]]]
 g := ![![![![551, -45, 58], ![-4580, 0, 98]], ![![-18801, 1868, -2246], ![175262, 0, -3745]]], ![![![-9651, 955, -1150], ![89758, 0, -1918]], ![![-18904, 1881, -2259], ![176245, 0, -3766]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![-75, -5, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![8, 0, 0], ![-75, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0], ![-616, -32, 8]], ![![-150, -10, 2], ![-615, -13, 5]]]
 hmul := by decide
 f := ![![![![19082716984, -179158570064, -16516238011], ![-384625582024, 0, 10437958620]], ![![554356264, 0, 0], ![1799858, 0, 195]]], ![![![-179083958334, 1681334265296, 154998540628], ![3609563138016, 0, -97956226605]], ![![-5202420300, 0, 0], ![-16890975, 0, -1830]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![73, -2, -1], ![16, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![45, 0, -1], ![13, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![-75, -1, 1]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![16, 0, 0], ![-383, -13, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![16, 0, 0], ![-616, -32, 8]], ![![-150, -2, 2], ![2225, 147, -27]]]
 hmul := by decide
 f := ![![![![130641, -1228812, -112698], ![-2626710, 0, 71190]], ![![17808, 0, 0], ![-16, 0, 0]]], ![![![-3126166, 29415162, 2697733], ![62877797, 0, -1704135]], ![![-426279, 0, 0], ![383, 0, 0]]]]
 g := ![![![![502, -3174, -465], ![-2148, 0, 90]], ![![-7120, 120484, 17438], ![81762, 0, -3405]]], ![![![-1765, 29723, 4302], ![20170, 0, -840]], ![![26169, -433084, -62692], ![-293887, 0, 12240]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-383, -13, 5]] ![![2, 0, 0], ![-77, -4, 1]]
  ![![16, 0, 0], ![-83, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![32, 0, 0], ![-1232, -64, 16]], ![![-766, -26, 10], ![6061, 447, -79]]]
 hmul := by decide
 f := ![![![![58025197489794, -545029940520496, -50196504235423], ![-1169008474433780, 0, 31725226745867]], ![![626228502466, 0, 0], ![-206607886, 0, -651]]], ![![![-301178406005074, 2828964929242704, 260543760067534], ![6067710652744068, 0, -164669034054571]], ![![-3250424131703, 0, 0], ![1072393313, 0, 3379]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![6, -3, 0], ![16, 0, 0]]], ![![![4, -1, 0], ![10, 0, 0]], ![![52, 24, -1], ![-63, 0, 0]]]]
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

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-75, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-75, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-383, -13, 5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-83, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
