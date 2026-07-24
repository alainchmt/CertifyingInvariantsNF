import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_408807_1.RI3_1_408807_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-5, 1, 0]

def alpha1 := B.equivFun.symm ![-8, -1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![4, -1, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![25, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![0, 5, 0], ![0, 0, 3]]]
 hmul := by decide
 f := ![![![![1450, -279, 0], ![-54, 0, 0]], ![![0, 0, 0], ![0, -115, 0]]], ![![![-290, 55, 0], ![15, 0, 0]], ![![0, 0, 0], ![0, 23, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![5, 0, 0]]], ![![![1, 0, 0], ![5, 0, 0]], ![![1, 10, -6], ![5, 51, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![-5, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![0, 25, 0]], ![![-25, 5, 0], ![0, -5, 3]]]
 hmul := by decide
 f := ![![![![0, 610, -141], ![-1462, -78, 0]], ![![290, 1878, 0], ![-1450, 23, 0]]]]
 g := ![![![![-88, -5, -3]], ![![-63, -5, -3]]], ![![![5, 0, 0]], ![![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-3, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![121, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-33, 11, 0], ![9, -6, 3]]]
 hmul := by decide
 f := ![![![![-4254746, 1552376, -133533], ![-14685814, 176528, 0]], ![![0, 0, 0], ![3430955, -2178, 0]]], ![![![-269584, 98362, -8463], ![-930504, 11193, 0]], ![![0, 0, 0], ![217390, -138, 0]]]]
 g := ![![![![737, 92, 0], ![-11132, 0, 0]], ![![-217, -35, -3], ![3278, 121, 0]]], ![![![-217, -35, -3], ![3278, 121, 0]], ![![49, 6, 0], ![-740, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![8, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![-8, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-363, 121, 0]], ![![88, 11, 0], ![-24, 5, 3]]]
 hmul := by decide
 f := ![![![![74957036, -49868263, -10092885], ![261291822, 337928, 0]], ![![-55956186, 403382187, 0], ![-217390, 138, 0]]]]
 g := ![![![![-127, 8, -3]], ![![6, -8, 3]]], ![![![-11, 0, 0]], ![![3, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![79, 4, 3])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![55, 0, 0], ![-25, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![55, 0, 0], ![-15, 5, 0]], ![![0, 11, 0], ![0, -3, 3]]]
 hmul := by decide
 f := ![![![![19, -3, 39], ![66, 11, 0]], ![![0, -70, 0], ![0, 0, 0]]], ![![![-7, 3, -18], ![-24, 0, 0]], ![![-4, 30, 0], ![0, 0, 0]]]]
 g := ![![![![26, 349, -42], ![55, 770, 0]], ![![2, -175, 21], ![5, -385, 0]]], ![![![5, -175, 21], ![11, -385, 0]], ![![10, 50, -6], ![22, 111, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![55, 0, 0], ![-25, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![0, 1, 0]] ![![121, 0, 0], ![8, 1, 0]]
  ![![605, 0, 0], ![250, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![605, 0, 0], ![40, 5, 0]], ![![0, 121, 0], ![0, 8, 3]]]
 hmul := by decide
 f := ![![![![4161, 520, 306], ![-62920, 0, 0]], ![![0, -510, 0], ![0, 0, 0]]], ![![![1730, 217, 132], ![-26160, 0, 0]], ![![-4, -220, 0], ![0, 0, 0]]]]
 g := ![![![![-249, 172499, 2070], ![605, -417450, 0]], ![![-252, 11249, 135], ![610, -27225, 0]]], ![![![-50, -3750, -45], ![121, 9075, 0]], ![![-150, -251, -3], ![363, 606, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![605, 0, 0], ![250, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![-5, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![275, 0, 0], ![-80, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![275, 0, 0], ![-75, 25, 0]], ![![-55, 11, 0], ![15, -8, 3]]]
 hmul := by decide
 f := ![![![![-5037275, 1713118, -73866], ![-17371332, 270226, 0]], ![![-1498200, 1400, 0], ![0, 0, 0]]], ![![![1433036, -487357, 21012], ![4941908, -76868, 0]], ![![426216, -400, 0], ![0, 0, 0]]]]
 g := ![![![![161, 122878, -4608], ![550, 422400, 0]], ![![7, -35840, 1344], ![25, -123200, 0]]], ![![![3, -25600, 960], ![11, -88000, 0]], ![![21, 7680, -288], ![72, 26401, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![275, 0, 0], ![-80, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![-5, 1, 0]] ![![121, 0, 0], ![8, 1, 0]]
  ![![3025, 0, 0], ![-355, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3025, 0, 0], ![200, 25, 0]], ![![-605, 121, 0], ![-40, 3, 3]]]
 hmul := by decide
 f := ![![![![5536005034441, 695319345150, 1276213386], ![-83728144817790, -51473520758, 0]], ![![1299612600, -86600, 0], ![0, 0, 0]]], ![![![-651970065331, -81887100191, -150298443], ![9860584249344, 6061987833, 0]], ![![-153054144, 10200, 0], ![0, 0, 0]]]]
 g := ![![![![-1124284, -29381366643, 248293266], ![-9580175, -250362376550, 0]], ![![-74192, -1939601221, 16390998], ![-632200, -16527589650, 0]]], ![![![225439, 5890640745, -49780068], ![1920996, 50194901900, 0]], ![![14952, 388871218, -3286236], ![127408, 3313621301, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3025, 0, 0], ![-355, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
