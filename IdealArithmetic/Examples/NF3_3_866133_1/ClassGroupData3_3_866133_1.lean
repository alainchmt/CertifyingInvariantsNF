import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_866133_1.RI3_3_866133_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![29, 3, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-208, -22, 7]

def zeta2 := B.equivFun.symm ![44, 8, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, -1, 4]]]
 hmul := by decide
 f := ![![![![-227565, 532524, -453738], ![-837734, 227692, 6]], ![![0, 0, 0], ![-1396, 0, -4]]], ![![![-113880, 266490, -227064], ![-419225, 113944, 3]], ![![0, 0, 0], ![-699, 0, -2]]]]
 g := ![![![![62218, 6021, 675], ![32616, 0, -900]], ![![-278, -27, -3], ![-142, 0, 4]]], ![![![-278, -27, -3], ![-142, 0, 4]], ![![31246, 3023, 340], ![16383, 0, -452]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![2, 1, 4]]]
 hmul := by decide
 f := ![![![![-67561981, 158844672, -135158194], ![-250158258, 67579092, 762]], ![![169344, 0, -2688], ![3800, 0, -8]]], ![![![16965838, -39888450, 33940392], ![62818737, -16970196, -191]], ![![-42525, 0, 675], ![-949, 0, 2]]]]
 g := ![![![![353692, -434250, 621459], ![-142704, -1243368, -1800]], ![![-1572, 1932, -2765], ![640, 5532, 8]]], ![![![176060, -216159, 309347], ![-71032, -618918, -896]], ![![88031, -108080, 154674], ![-35512, -309459, -448]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![-2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![16, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![0, 8, 0]], ![![-4, 2, 0], ![2, -3, 4]]]
 hmul := by decide
 f := ![![![![-620316481928, 1458728466048, -1240784329757], ![-2297271681432, 620390673000, 3260672]], ![![682440112, 0, -10832496], ![-3568, 0, 16]]], ![![![-232502720724, 546750484056, -465062174828], ![-861047434946, 232530528238, 1222144]], ![![255787469, 0, -4060161], ![-1337, 0, 6]]]]
 g := ![![![![154162, 268547, 208803], ![74608, -828912, -3600]], ![![-690, -1195, -929], ![-320, 3688, 16]]], ![![![-38716, -67436, -52433], ![-18724, 208150, 904]], ![![19526, 34016, 26449], ![9454, -104997, -456]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![6, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32, 0, 0], ![-10, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![0, 16, 0]], ![![12, 2, 0], ![2, 5, 4]]]
 hmul := by decide
 f := ![![![![104207473149808, -245085139597134, 208434671993619], ![385973449212236, -104213523349072, -264974080]], ![![156864528672, -29745145152, -129186240], ![-23264, 0, -32]]], ![![![-32563226104185, 76585321322595, -65132616182449], ![-120610742367036, 32565116697684, 82800310]], ![![-49017742782, 9294898512, 40368705], ![7269, 0, 10]]]]
 g := ![![![![-1268394, 8541601, -3110445], ![663328, 24867360, -7200]], ![![5646, -38003, 13839], ![-2944, -110640, 32]]], ![![![-474942, 3198350, -1164687], ![248380, 9311430, -2696]], ![![-77509, 521974, -190078], ![40542, 1519635, -440]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-10, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![29, 3, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![0, 32, 0]], ![![-20, 2, 0], ![2, -11, 4]]]
 hmul := by decide
 f := ![![![![215658823423962, -507210960479934, 431332108626509], ![798773955209918, -215664970395454, -269915008]], ![![-176164941300, -16423520136, -71329068], ![8152, 0, 29]]]]
 g := ![![![![201, 7, -4]], ![![-691, -29, 12]]], ![![![-106, -4, 2]], ![![345, 12, -7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-60, -13, -3])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-8646, -313, 165])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-10, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
