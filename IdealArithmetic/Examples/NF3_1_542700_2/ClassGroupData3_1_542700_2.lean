import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_542700_2.RI3_1_542700_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-7, -1, 0]

def alpha1 := B.equivFun.symm ![41, 8, 3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![509, -104, 27]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![49, 0, 0], ![7, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![0, 0, 6]]]
 hmul := by decide
 f := ![![![![8281, 1159, 0], ![167, 0, 0]], ![![0, 0, 0], ![0, -322, 0]]], ![![![1183, 165, 0], ![28, 0, 0]], ![![0, 0, 0], ![0, -46, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![7, 0, 0]]], ![![![-1, 0, 0], ![7, 0, 0]], ![![-6, -36, -30], ![42, 246, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![7, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![-7, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![0, 49, 0]], ![![49, 7, 0], ![0, 7, 6]]]
 hmul := by decide
 f := ![![![![0, 3708, 930], ![-12708, 801, 0]], ![![-1183, -13248, 0], ![0, 46, 0]]]]
 g := ![![![![131, 7, -6]], ![![-180, -7, 6]]], ![![![-7, 0, 0]], ![![0, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-5, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-5, 1, 0]] ![![11, 0, 0], ![-5, 1, 0]]
  ![![121, 0, 0], ![-49, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-55, 11, 0]], ![![-55, 11, 0], ![25, -10, 6]]]
 hmul := by decide
 f := ![![![![5529766836, -1237275825, 157604532], ![12147923260, -285452805, 0]], ![![0, 0, 0], ![-38420767, -4356, 0]]], ![![![-2250751944, 503601880, -64148946], ![-4944505384, 116186358, 0]], ![![0, 0, 0], ![15638203, 1773, 0]]]]
 g := ![![![![3039, -62, 0], ![7502, 0, 0]], ![![-1319, 76, -6], ![-3256, 121, 0]]], ![![![-1319, 76, -6], ![-3256, 121, 0]], ![![653, -13, 0], ![1612, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![-49, 1, 0]] ![![11, 0, 0], ![-5, 1, 0]]
  ![![41, 8, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-605, 121, 0]], ![![-539, 11, 0], ![245, -54, 6]]]
 hmul := by decide
 f := ![![![![1931295238454, -427857032762, 49431040851], ![4248352766654, -90512074798, 0]], ![![551953272, -1225382164, 0], ![-12383567, -1404, 0]]]]
 g := ![![![![601, -13, -9]], ![![-445, 36, -3]]], ![![![-259, 8, 3]], ![![175, -19, 3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-382561, -78451, -29283])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-49, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![-5, 1, 0]]
  ![![77, 0, 0], ![28, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![77, 0, 0], ![-35, 7, 0]], ![![0, 11, 0], ![0, -5, 6]]]
 hmul := by decide
 f := ![![![![31, 744, 3204], ![66, 1650, 0]], ![![0, -4788, 0], ![0, 0, 0]]], ![![![144, 272, 1464], ![316, 660, 0]], ![![-5, -2128, 0], ![0, 0, 0]]]]
 g := ![![![![-223, 49132, 10530], ![616, -135135, 0]], ![![109, -32756, -7020], ![-301, 90090, 0]]], ![![![52, -16378, -3510], ![-143, 45045, 0]], ![![-44, 7278, 1560], ![121, -20019, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![77, 0, 0], ![28, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![0, 1, 0]] ![![121, 0, 0], ![-49, 1, 0]]
  ![![847, 0, 0], ![-49, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![847, 0, 0], ![-343, 7, 0]], ![![0, 121, 0], ![0, -49, 6]]]
 hmul := by decide
 f := ![![![![3039, 5573, 324174], ![7502, 13915, 0]], ![![0, -379008, 0], ![0, 0, 0]]], ![![![-175, -241, -15198], ![-432, -605, 0]], ![![-3, 17766, 0], ![0, 0, 0]]]]
 g := ![![![![-7006, -102951307, 12606300], ![-121121, -1779589350, 0]], ![![2891, 41777341, -5115600], ![49980, 722152200, 0]]], ![![![105, 1492048, -182700], ![1815, 25791150, 0]], ![![0, -603925, 73950], ![0, -10439274, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![847, 0, 0], ![-49, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![7, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![7, 1, 0]] ![![11, 0, 0], ![-5, 1, 0]]
  ![![539, 0, 0], ![105, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![539, 0, 0], ![-245, 49, 0]], ![![77, 11, 0], ![-35, 2, 6]]]
 hmul := by decide
 f := ![![![![814600166872, -182697799393, 23844271620], ![1791527897731, -43714381150, 0]], ![![-1885129862, -520380, 0], ![0, 0, 0]]], ![![![162915845458, -36538620615, 4768731738], ![358296369176, -8742651489, 0]], ![![-377016281, -104076, 0], ![0, 0, 0]]]]
 g := ![![![![-6404, 18181739, 1038960], ![32879, -93333240, 0]], ![![2930, -8585822, -490620], ![-15043, 44074030, 0]]], ![![![-947, 2525241, 144300], ![4862, -12962950, 0]], ![![335, -1194372, -68250], ![-1720, 6131126, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![539, 0, 0], ![105, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![7, 1, 0]] ![![121, 0, 0], ![-49, 1, 0]]
  ![![5929, 0, 0], ![-2590, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![5929, 0, 0], ![-2401, 49, 0]], ![![847, 121, 0], ![-343, -42, 6]]]
 hmul := by decide
 f := ![![![![-17960136867952, 401117857347, -4357153644], ![-44335718507234, 87828428017, 0]], ![![42020489049, 16537353, 0], ![0, 0, 0]]], ![![![7877253709582, -175928900350, 1911032466], ![19445492294732, -38521243706, 0]], ![![-18430040688, -7253225, 0], ![0, 0, 0]]]]
 g := ![![![![17549841, 283634130724, -657067500], ![40174904, 649292201250, 0]], ![![-7109529, -114946463505, 266285250], ![-16275056, -263134207875, 0]]], ![![![2494223, 40305902787, -93372750], ![5709748, 92267839125, 0]], ![![-1008987, -16334546860, 37840650], ![-2309762, -37392868974, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5929, 0, 0], ![-2590, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
