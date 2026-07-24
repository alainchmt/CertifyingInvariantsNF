import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_387059_1.RI3_1_387059_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-2, 4, -3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2, 3, -3]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![3, 1, 4]]]
 hmul := by decide
 f := ![![![![-11677, 26000, -3305], ![7162, 0, 1983]], ![![0, 0, 0], ![164, 0, -6]]], ![![![3904, -8693, 1105], ![-2394, 0, -663]], ![![0, 0, 0], ![-55, 0, 2]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![-2, 0, 0]]], ![![![0, 1, 0], ![-2, 0, 0]], ![![-5, 28, 0], ![9, 0, 4]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![-2, 2, 0], ![1, -1, 4]]]
 hmul := by decide
 f := ![![![![-111062, 261307, -28875], ![75124, 0, 18375]], ![![33376, 0, 4172], ![1592, 0, 36]]], ![![![18446, -43403, 4796], ![-12476, 0, -3052]], ![![-5544, 0, -693], ![-265, 0, -6]]]]
 g := ![![![![26, -102, 0], ![-10, 7, -28]], ![![11, -43, 0], ![-6, 3, -12]]], ![![![-7, 29, 0], ![6, -2, 8]], ![![4, -15, 0], ![3, 2, -4]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![-1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![7, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![-2, 2, 0], ![1, -1, 4]]]
 hmul := by decide
 f := ![![![![-73834, 168287, -19251], ![47228, 0, 12555]], ![![9536, 0, 1192], ![3184, 0, 72]]], ![![![-30786, 70170, -8027], ![19692, 0, 5235]], ![![3976, 0, 497], ![1327, 0, 30]]]]
 g := ![![![![8, -153, 0], ![12, 126, -56]], ![![4, -65, 0], ![4, 54, -24]]], ![![![-8, 21, 0], ![14, -18, 8]], ![![-4, -12, 0], ![11, 10, -4]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![7, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![14, 2, 0], ![9, 7, 4]]]
 hmul := by decide
 f := ![![![![-39715797, 98281780, -11375363], ![29282994, 0, 7502899]], ![![-11393760, 608256, -55296], ![-2912, 0, -144]]], ![![![11580197, -28656671, 3316790], ![-8538235, 0, -2187670]], ![![3322155, -177353, 16123], ![849, 0, 42]]]]
 g := ![![![![39, -166, 0], ![-8, -196, -112]], ![![20, -71, 0], ![8, -84, -48]]], ![![![16, -71, 0], ![-6, -84, -48]], ![![10, -41, 0], ![-1, -48, -28]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-9, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![64, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![-18, 2, 0], ![-7, -9, 4]]]
 hmul := by decide
 f := ![![![![-21254920943, 54139059322, -6302048915], ![16442069190, 0, 4179253491]], ![![13154027200, 264670560, -381920], ![31168, 0, 288]]], ![![![3099471903, -7894759703, 918988295], ![-2397643898, 0, -609434343]], ![![-1918169350, -38595249, 55693], ![-4545, 0, -42]]]]
 g := ![![![![48, -167, 0], ![48, -392, -224]], ![![20, -71, 0], ![16, -168, -96]]], ![![![-7, 47, 0], ![34, 112, 64]], ![![4, 14, 0], ![55, 36, 20]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![-9, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![128, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![64, 64, 0]], ![![-18, 2, 0], ![-7, -9, 4]]]
 hmul := by decide
 f := ![![![![-2160348282, 5464077615, -634226387], ![1651864668, 0, 421710739]], ![![2511042432, 25206720, -763840], ![62336, 0, 576]]], ![![![157515018, -398396083, 46242628], ![-120440532, 0, -30747716]], ![![-183084798, -1837869, 55693], ![-4545, 0, -42]]]]
 g := ![![![![48, -167, 0], ![96, -784, -448]], ![![20, -71, 0], ![32, -336, -192]]], ![![![1, 23, 0], ![98, 112, 64]], ![![2, 7, 0], ![55, 36, 20]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![-9, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![256, 0, 0], ![119, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![256, 0, 0], ![128, 128, 0]], ![![-18, 2, 0], ![-7, -9, 4]]]
 hmul := by decide
 f := ![![![![46192460401, -121228485478, 14125807149], ![-37518012538, 0, -9404910765]], ![![-145003395328, -592827520, -1527680], ![124672, 0, 1152]]], ![![![21412241372, -56194746280, 6547934222], ![-17391252454, 0, -4359590670]], ![![-67215464910, -274801685, -708147], ![57791, 0, 534]]]]
 g := ![![![![-153, -12598, 0], ![-64, 27104, -896]], ![![-108, -5399, 0], ![64, 11616, -384]]], ![![![-92, 899, 0], ![226, -1936, 64]], ![![-81, 280, 0], ![183, -604, 20]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![256, 0, 0], ![119, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![512, 0, 0], ![119, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![512, 0, 0], ![256, 256, 0]], ![![238, 2, 0], ![121, 119, 4]]]
 hmul := by decide
 f := ![![![![21110381251249, 57629837472090, -7700337203923], ![39370109361670, 0, 5130211618259]], ![![-131912867012096, 333063661568, -389978112], ![-2110976, 0, -2304]]], ![![![4892773957660, 13356924473215, -1784714775584], ![9124849215439, 0, 1189034224672]], ![![-30573575755129, 77194494509, -90385613], ![-489263, 0, -534]]]]
 g := ![![![![-272, -12599, 0], ![384, 54208, -1792]], ![![-108, -5399, 0], ![128, 23232, -768]]], ![![![-182, -5850, 0], ![418, 25168, -832]], ![![-35, -2559, 0], ![-9, 11012, -364]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![512, 0, 0], ![119, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![1024, 0, 0], ![119, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![1024, 0, 0], ![512, 512, 0]], ![![238, 2, 0], ![121, 119, 4]]]
 hmul := by decide
 f := ![![![![372796868255067, -1160699691460604, 135785247600685], ![-393951411602766, 0, -90494011918893]], ![![801030112166912, -5637808533504, -779956224], ![-4221952, 0, -4608]]], ![![![43201749576593, -134508258180491, 15735540618945], ![-45653254301947, 0, -10486943357121]], ![![92827770982023, -653340232083, -90385613], ![-489263, 0, -534]]]]
 g := ![![![![-272, -12599, 0], ![768, 108416, -3584]], ![![-108, -5399, 0], ![256, 46464, -1536]]], ![![![-91, -2925, 0], ![418, 25168, -832]], ![![-77, -1280, 0], ![503, 11012, -364]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![1024, 0, 0], ![119, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-2, 4, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![2048, 0, 0], ![1024, 1024, 0]], ![![238, 2, 0], ![121, 119, 4]]]
 hmul := by decide
 f := ![![![![-488593779894588, -1200332278608612, 430585946856187], ![1564102183601709, -194370494946774, -27892025524207]], ![![107431751893854, -1771257942372, 2538676], ![13742, 0, 15]]]]
 g := ![![![![8622, -129, 292]], ![![5350, -69, 180]]], ![![![1004, -15, 34]], ![![623, -8, 21]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow11 : J0 ^ 11 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![8041, -120, 273])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![7, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![119, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     

lemma PowJ0_9 : J0 ^ 9 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![512, 0, 0], ![119, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     

lemma PowJ0_10 : J0 ^ 10 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1024, 0, 0], ![119, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     
