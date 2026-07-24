import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_455455_1.RI3_1_455455_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-38, -2, 1]

def alpha1 := B.equivFun.symm ![2, 2, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-19551, -3226, -692]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-2, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-2, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![4, 0, 0], ![-2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-4, 0, 2]], ![![-4, 0, 2], ![26, -22, 1]]]
 hmul := by decide
 f := ![![![![7283, -330, 2914], ![-5825, 198, 0]], ![![0, 0, 0], ![-6, 0, 0]]], ![![![-3641, 165, -1457], ![2913, -99, 0]], ![![0, 0, 0], ![3, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![901, -7, -414], ![1657, 2, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-2, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![8, 0, 0], ![-6, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-8, 0, 4]], ![![-4, 0, 2], ![26, -22, 1]]]
 hmul := by decide
 f := ![![![![170857, -7260, 73587], ![-134063, 4620, 0]], ![![-26216, 396, 0], ![-12, 0, 0]]], ![![![-128141, 5445, -55191], ![100549, -3465, 0]], ![![19662, -297, 0], ![9, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![4, 0, 0]]], ![![![1, 0, 0], ![2, 0, 0]], ![![241, 0, 21], ![-167, 22, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![-6, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![16, 0, 0], ![2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![-16, 0, 8]], ![![-12, 0, 2], ![34, -22, -3]]]
 hmul := by decide
 f := ![![![![54807, -2904, -27436], ![120983, 1936, 0]], ![![-264480, 264, 0], ![-24, 0, 0]]], ![![![6852, -363, -3430], ![15124, 242, 0]], ![![-33060, 33, 0], ![-3, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![8, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![88, -4, 18], ![-291, 6, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![2, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![32, 0, 0], ![2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![-32, 0, 16]], ![![4, 0, 2], ![18, -22, 5]]]
 hmul := by decide
 f := ![![![![-7794821, 322608, -3091798], ![6248923, -212784, 0]], ![![-522496, -7920, 0], ![-48, 0, 0]]], ![![![-487175, 20163, -193238], ![390559, -13299, 0]], ![![-32656, -495, 0], ![-3, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![16, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![41, -2, 8], ![-251, 6, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![2, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![64, 0, 0], ![-30, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![-64, 0, 32]], ![![4, 0, 2], ![18, -22, 5]]]
 hmul := by decide
 f := ![![![![-7314693, 300960, -2913686], ![5857851, -199584, 0]], ![![-487424, -7392, 0], ![-96, 0, 0]]], ![![![3428763, -141075, 1365790], ![-2745867, 93555, 0]], ![![228480, 3465, 0], ![45, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![14, 0, 0], ![32, 0, 0]]], ![![![1, 0, 0], ![2, 0, 0]], ![![-645, 2, 22], ![-1403, 6, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![-30, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![128, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![-128, 0, 64]], ![![-60, 0, 2], ![82, -22, -27]]]
 hmul := by decide
 f := ![![![![-73672773, 2823744, -29233174], ![59056187, -1877568, 0]], ![![-18877440, 19008, 0], ![-192, 0, 0]]], ![![![-19569330, 750057, -7765062], ![15686800, -498729, 0]], ![![-5014320, 5049, 0], ![-51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-18, 0, 0], ![64, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![14, -2, 0], ![-27, 6, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![34, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![256, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![256, 0, 0], ![-256, 0, 128]], ![![68, 0, 2], ![-46, -22, 37]]]
 hmul := by decide
 f := ![![![![322094253, -22649088, 119172785], ![-262507859, 15079680, 0]], ![![1546379392, 97152, 0], ![384, 0, 0]]], ![![![42778144, -3008082, 15827635], ![-34864324, 2002770, 0]], ![![205378513, 12903, 0], ![51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-18, 0, 0], ![128, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![66, -1, 2], ![-475, 6, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![256, 0, 0], ![34, 0, 1]] ![![2, 0, 0], ![-2, 0, 1]]
  ![![-38, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![512, 0, 0], ![-512, 0, 256]], ![![68, 0, 2], ![-46, -22, 37]]]
 hmul := by decide
 f := ![![![![-102513555381, 1509310462, 17686536452], ![-35414045924, -1006169039, 56218]], ![![5222688973, 3689821, 0], ![14595, 2, 0]]]]
 g := ![![![![771, -98, 59]], ![![6346, -796, 474]]], ![![![158, -20, 12]], ![![1294, -162, 97]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-2, 0, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0], ![-2, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![36, 0, 0], ![10, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0], ![-12, 0, 6]], ![![-12, 0, 6], ![26, -22, 1]]]
 hmul := by decide
 f := ![![![![481053416807, -59560944704, -241121623920], ![1496854661133, -3604189592, -16690746744]], ![![0, 0, 0], ![-267615414, 367020, -72]]], ![![![133625949150, -16544706863, -66978228868], ![415792961434, -1001163774, -4636318540]], ![![0, 0, 0], ![-74337615, 101950, -20]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![6, 0, 0]]], ![![![-2, 0, 0], ![6, 0, 0]], ![![1218, -45, 122], ![-3731, 42, -44]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![36, 0, 0], ![10, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![2, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![216, 0, 0], ![-72, 0, 36]], ![![60, 0, 6], ![2, -22, 13]]]
 hmul := by decide
 f := ![![![![-148639529, 17381649, 74522372], ![-447582051, -223298, 4708000]], ![![-82058108, -17500, 68], ![1, 0, 0]]]]
 g := ![![![![207, -26, 15]], ![![558, -68, 42]]], ![![![162, -20, 12]], ![![430, -54, 33]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-586203071, 73606534, -44286452])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![10, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-2, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![12, 0, 0], ![-2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![12, 0, 0], ![-4, 0, 2]], ![![-12, 0, 6], ![26, -22, 1]]]
 hmul := by decide
 f := ![![![![28751, -3556, -14398], ![89367, -214, -990]], ![![0, 0, 0], ![-18, 0, 0]]], ![![![-4759, 592, 2398], ![-14884, 37, 165]], ![![0, 0, 0], ![3, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![6, 0, 0]], ![![187, -81, -74], ![1021, -6, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![-2, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![72, 0, 0], ![10, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![72, 0, 0], ![20, 0, 2]], ![![-72, 0, 36], ![2, -22, 13]]]
 hmul := by decide
 f := ![![![![-54195, 1946, -5492], ![167778, -1740, 1980]], ![![0, 0, 0], ![36, 0, 0]]], ![![![-7537, 270, -764], ![23347, -241, 275]], ![![0, 0, 0], ![5, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![-6, 0, 0], ![36, 0, 0]], ![![319, -25, 30], ![-1487, 54, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![72, 0, 0], ![10, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-2, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![24, 0, 0], ![-14, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![24, 0, 0], ![-8, 0, 4]], ![![-12, 0, 6], ![26, -22, 1]]]
 hmul := by decide
 f := ![![![![3200423, -217076, -1602324], ![7324533, -14912, -60984]], ![![1648248, 1188, 0], ![-36, 0, 0]]], ![![![-1866882, 126627, 934688], ![-4272638, 8700, 35574]], ![![-961478, -693, 0], ![21, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![4, 0, 0]]], ![![![3, 0, 0], ![6, 0, 0]], ![![4108, 330, 82], ![-2363, 990, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-14, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-2, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![144, 0, 0], ![-62, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![144, 0, 0], ![40, 0, 4]], ![![-72, 0, 36], ![2, -22, 13]]]
 hmul := by decide
 f := ![![![![-609640027, 21916777, -61748890], ![1886135670, -19647132, 22375584]], ![![0, 0, 0], ![370728, 432, 0]]], ![![![262483936, -9436396, 26586326], ![-812086132, 8459196, -9633932]], ![![0, 0, 0], ![-159619, -186, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![4, 0, 0]]], ![![![15, 0, 0], ![36, 0, 0]], ![![-11512, 195, 176], ![-27839, 510, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![144, 0, 0], ![-62, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-6, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![-6, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![48, 0, 0], ![-14, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![48, 0, 0], ![-16, 0, 8]], ![![-36, 0, 6], ![34, -22, -3]]]
 hmul := by decide
 f := ![![![![3005783, 513621, -1488914], ![-3696063, -358002, 91080]], ![![16475040, 5544, 0], ![-72, 0, 0]]], ![![![-876647, -149807, 434266], ![1078022, 104419, -26565]], ![![-4805220, -1617, 0], ![21, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![8, 0, 0]]], ![![![1, 0, 0], ![6, 0, 0]], ![![-5849, -12, 420], ![-20559, 46, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![-14, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![-6, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![288, 0, 0], ![-62, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![288, 0, 0], ![80, 0, 8]], ![![-216, 0, 36], ![-38, -22, 9]]]
 hmul := by decide
 f := ![![![![382273744255, -30573803520, -25839210423], ![105469395354, 76434508800, 2080465920]], ![![176341028400, 19787040, 0], ![513360, 864, 0]]], ![![![-82295042170, 6581860480, 5562607799], ![-22705217041, -16454651200, -447878080]], ![![-37962304725, -4259710, 0], ![-110515, -186, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![8, 0, 0]]], ![![![7, 0, 0], ![36, 0, 0]], ![![-3015, 50, 42], ![-14595, 270, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![288, 0, 0], ![-62, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![2, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![96, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![96, 0, 0], ![-32, 0, 16]], ![![12, 0, 6], ![18, -22, 5]]]
 hmul := by decide
 f := ![![![![17884755, -2136907, -8964432], ![54514125, -98026, -595584]], ![![2824704, 4752, 0], ![-144, 0, 0]]], ![![![6334220, -756822, -3174904], ![19307092, -34716, -210936]], ![![1000416, 1683, 0], ![-51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![16, 0, 0]]], ![![![-2, 0, 0], ![6, 0, 0]], ![![-2018, 660, 25], ![-679, -1650, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![2, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![576, 0, 0], ![226, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![576, 0, 0], ![160, 0, 16]], ![![72, 0, 36], ![42, -22, 17]]]
 hmul := by decide
 f := ![![![![-6827033490769, 824697538560, 162069711865], ![-1891896255414, -2061743846400, -56175049728]], ![![-1377765861984, 74700864, 0], ![-13573728, 1728, 0]]], ![![![-2678662446029, 323579242560, 63589852225], ![-742306516888, -808948106400, -22040904928]], ![![-540581744459, 29309714, 0], ![-5325803, 678, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![16, 0, 0]]], ![![![-14, 0, 0], ![36, 0, 0]], ![![-529, 660, 17], ![389, -1650, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![576, 0, 0], ![226, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![2, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![192, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![192, 0, 0], ![-64, 0, 32]], ![![12, 0, 6], ![18, -22, 5]]]
 hmul := by decide
 f := ![![![![49479759, -4600503, -24800518], ![131582481, 368622, -1203840]], ![![111105024, 9504, 0], ![-288, 0, 0]]], ![![![8762070, -814673, -4391760], ![23301074, 65278, -213180]], ![![19674848, 1683, 0], ![-51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![32, 0, 0]]], ![![![-1, 0, 0], ![6, 0, 0]], ![![410, -34, 18], ![-1735, 142, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![192, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![2, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![1152, 0, 0], ![-350, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1152, 0, 0], ![320, 0, 32]], ![![72, 0, 36], ![42, -22, 17]]]
 hmul := by decide
 f := ![![![![-13791233681549, 1666128070656, 328469825907], ![-3821774083038, -4165320176640, -113545313280]], ![![-5599951568064, 149401728, 0], ![-27147456, 3456, 0]]], ![![![4190044955330, -506202104800, -99795520024], ![1161129278707, 1265505262000, 34497274000]], ![![1701374174325, -45391150, 0], ![8247925, -1050, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![10, 0, 0], ![32, 0, 0]]], ![![![11, 0, 0], ![36, 0, 0]], ![![3869, 195, -24], ![12485, 654, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1152, 0, 0], ![-350, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![-30, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![-30, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![384, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![384, 0, 0], ![-128, 0, 64]], ![![-180, 0, 6], ![82, -22, -27]]]
 hmul := by decide
 f := ![![![![5251705043, -709407456, -2637310370], ![17225333049, 149441664, -173055168]], ![![-9411259392, -386496, 0], ![-576, 0, 0]]], ![![![464994740, -62812119, -233511856], ![1525159699, 13231815, -15322593]], ![![-833288592, -34221, 0], ![-51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![64, 0, 0]]], ![![![-1, 0, 0], ![6, 0, 0]], ![![718, -17, 24], ![-7527, 142, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![384, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![-30, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![2304, 0, 0], ![802, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![2304, 0, 0], ![640, 0, 64]], ![![-1080, 0, 36], ![-278, -22, -15]]]
 hmul := by decide
 f := ![![![![-75052168352763, 5685947898898, -7858480865100], ![220168026800190, -10583869468920, 2087506953216]], ![![55866098800512, 777143808, 0], ![2282112, -2304, 0]]], ![![![-26124930129708, 1979223183554, -2735460787244], ![76638349606663, -3684142063392, 726640875208]], ![![19446445849831, 270516204, 0], ![794381, -802, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-22, 0, 0], ![64, 0, 0]]], ![![![-13, 0, 0], ![36, 0, 0]], ![![11765, -364, 30], ![-33627, 1038, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2304, 0, 0], ![802, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![128, 0, 0], ![34, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![768, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![768, 0, 0], ![-256, 0, 128]], ![![204, 0, 6], ![-46, -22, 37]]]
 hmul := by decide
 f := ![![![![-30338493713, 3524267194, 15223061780], ![-91051371723, -605722100, 878461056]], ![![-62344159104, -1254528, 0], ![1152, 0, 0]]], ![![![-1343110372, 156022245, 673937630], ![-4030920097, -26815821, 38890203]], ![![-2760027877, -55539, 0], ![51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![128, 0, 0]]], ![![![0, 0, 0], ![6, 0, 0]], ![![198, -2, 8], ![-4391, 14, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![768, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![128, 0, 0], ![34, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![4608, 0, 0], ![-1502, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4608, 0, 0], ![1280, 0, 128]], ![![1224, 0, 36], ![362, -22, 49]]]
 hmul := by decide
 f := ![![![![231184771480577, -2059139364375, 22986207651940], ![-646501450895874, -5707856259324, -7260359293440]], ![![-256343165694720, 1723322880, 0], ![-312963840, 13824, 0]]], ![![![-75355800078934, 671186485520, -7492466122660], ![210730290634923, 1860503494258, 2366549405110]], ![![83556300970805, -561725470, 0], ![102012085, -4506, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![42, 0, 0], ![128, 0, 0]]], ![![![12, 0, 0], ![36, 0, 0]], ![![14624, 337, -24], ![44773, 1038, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4608, 0, 0], ![-1502, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![256, 0, 0], ![34, 0, 1]] ![![6, 0, 0], ![-2, 0, 1]]
  ![![1536, 0, 0], ![34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![1536, 0, 0], ![-512, 0, 256]], ![![204, 0, 6], ![-46, -22, 37]]]
 hmul := by decide
 f := ![![![![135804952463, -15768110779, -68143911598], ![407465019969, 2739101558, -3926647296]], ![![562278023424, 5601024, 0], ![2304, 0, 0]]], ![![![3006099249, -349033703, -1508393878], ![9019408003, 60631156, -86917974]], ![![12446258331, 123981, 0], ![51, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![256, 0, 0]]], ![![![0, 0, 0], ![6, 0, 0]], ![![31, -1, 2], ![-1319, 14, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1536, 0, 0], ![34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![256, 0, 0], ![34, 0, 1]] ![![36, 0, 0], ![10, 0, 1]]
  ![![9216, 0, 0], ![-1502, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![9216, 0, 0], ![2560, 0, 256]], ![![1224, 0, 36], ![362, -22, 49]]]
 hmul := by decide
 f := ![![![![89238514693761793, -3078364671467335, 9029831137966532], ![-274651317279021186, 2603269235201604, -3262174385633280]], ![![-10595468682339840, 775495296000, 0], ![-625927680, 27648, 0]]], ![![![-14543863831383462, 501703964468740, -1471658677216334], ![44761965988833543, -424274130997476, 531660799394660]], ![![1726822261379605, -126388230750, 0], ![102012085, -4506, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![42, 0, 0], ![256, 0, 0]]], ![![![6, 0, 0], ![36, 0, 0]], ![![10338, 418, -14], ![63205, 2574, -44]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9216, 0, 0], ![-1502, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
