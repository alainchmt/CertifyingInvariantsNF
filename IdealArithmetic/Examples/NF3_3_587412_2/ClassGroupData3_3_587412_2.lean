import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_587412_2.RI3_3_587412_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-145, -8, 1]

def alpha1 := B.equivFun.symm ![907, 46, -6]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-9, -1, 0]

def zeta2 := B.equivFun.symm ![-31, -4, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![-1812875, -1087555, -89996], ![4401425, 380300, 0]], ![![0, 0, 0], ![348700, -75, 0]]], ![![![-72536, -43515, -3601], ![176108, 15217, 0]], ![![0, 0, 0], ![13952, -3, 0]]]]
 g := ![![![![23, 11, 0], ![-275, 0, 0]], ![![6, 3, 0], ![-70, 0, 0]]], ![![![6, 3, 0], ![-70, 0, 0]], ![![4, 2, 0], ![-48, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![-145, -8, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![10, 5, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![-256154675, -165910774, -18917335], ![633937373, 107489727, 0]], ![![32963163, -64133407, 0], ![-1910908, 411, 0]]]]
 g := ![![![![-81, -2, 1]], ![![200, 25, 0]]], ![![![40, 5, 0]], ![![16, 10, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![13, 0, 0], ![3, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![169, 0, 0], ![55, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![39, 13, 0]], ![![39, 13, 0], ![9, 6, 1]]]
 hmul := by decide
 f := ![![![![-648806252, -231879106, -5199725], ![2803638526, 64881986, 0]], ![![0, 0, 0], ![35348547, -10140, 0]]], ![![![-210382160, -75189207, -1686065], ![909108886, 21038660, 0]], ![![0, 0, 0], ![11462133, -3288, 0]]]]
 g := ![![![![3851, 70, 0], ![-11830, 0, 0]], ![![821, 15, 0], ![-2522, 0, 0]]], ![![![821, 15, 0], ![-2522, 0, 0]], ![![181, 3, 0], ![-556, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![169, 0, 0], ![55, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![907, 46, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![2197, 0, 0], ![507, 169, 0]], ![![715, 13, 0], ![165, 58, 1]]]
 hmul := by decide
 f := ![![![![28081007108666, 10418345476315, 381963170186], ![-121639316226167, -4986672076382, 0]], ![![-31798525684, 275009622268, 0], ![-625955230, -53868, 0]]]]
 g := ![![![![-961, -110, 2]], ![![-43, -67, -8]]], ![![![-299, -39, 0]], ![![-69, -32, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![129, 9, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2399, -124, 16])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![55, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![2, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![65, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![65, 0, 0], ![15, 5, 0]], ![![26, 13, 0], ![6, 5, 1]]]
 hmul := by decide
 f := ![![![![11922, 4015, -44], ![-51207, -1456, 0]], ![![-260, 780, 0], ![0, 0, 0]]], ![![![-4212, -1418, 16], ![18091, 520, 0]], ![![92, -280, 0], ![0, 0, 0]]]]
 g := ![![![![576, -25, 0], ![1625, 0, 0]], ![![140, -6, 0], ![395, 0, 0]]], ![![![258, -11, 0], ![728, 0, 0]], ![![56, -2, 0], ![158, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![65, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![2, 1, 0]] ![![169, 0, 0], ![55, 1, 0]]
  ![![845, 0, 0], ![-283, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![845, 0, 0], ![275, 5, 0]], ![![338, 169, 0], ![110, 57, 1]]]
 hmul := by decide
 f := ![![![![24737705, 525378, -100], ![-76009102, -240149, 0]], ![![-2535, 7605, 0], ![0, 0, 0]]], ![![![-8284891, -176013, 33], ![25456166, 80613, 0]], ![![849, -2550, 0], ![0, 0, 0]]]]
 g := ![![![![87165, -308, 0], ![260260, 0, 0]], ![![28585, -101, 0], ![85350, 0, 0]]], ![![![34866, -123, 0], ![104104, 0, 0]], ![![11434, -40, 0], ![34140, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![845, 0, 0], ![-283, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![2, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![325, 0, 0], ![-23, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![325, 0, 0], ![75, 25, 0]], ![![26, 13, 0], ![6, 5, 1]]]
 hmul := by decide
 f := ![![![![169348, 58986, -541], ![-731133, -45695, 0]], ![![-7800, 101400, 0], ![0, 0, 0]]], ![![![-11924, -4153, 39], ![51479, 3237, 0]], ![![552, -7200, 0], ![0, 0, 0]]]]
 g := ![![![![5153, -224, 0], ![72800, 0, 0]], ![![1221, -53, 0], ![17250, 0, 0]]], ![![![438, -19, 0], ![6188, 0, 0]], ![![140, -6, 0], ![1978, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![325, 0, 0], ![-23, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![2, 1, 0]] ![![169, 0, 0], ![55, 1, 0]]
  ![![4225, 0, 0], ![-1973, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4225, 0, 0], ![1375, 25, 0]], ![![338, 169, 0], ![110, 57, 1]]]
 hmul := by decide
 f := ![![![![925800445, 19858649, 6255], ![-2844708386, -9596834, 0]], ![![-97175, 1263275, 0], ![0, 0, 0]]], ![![![-432330957, -9273661, -2921], ![1328423966, 4481711, 0]], ![![45379, -589950, 0], ![0, 0, 0]]]]
 g := ![![![![726065, -368, 0], ![1554800, 0, 0]], ![![238745, -121, 0], ![511250, 0, 0]]], ![![![61242, -31, 0], ![131144, 0, 0]], ![![20678, -10, 0], ![44280, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4225, 0, 0], ![-1973, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
