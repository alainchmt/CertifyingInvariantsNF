import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1379721215357, -401354532686, -60476501207]

def alpha1 := B.equivFun.symm ![-304499617, -88577533, -13346951]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![14788779351151, -35753534905620, 6129394308642]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-35, -2, 1]] ![![2, 0, 0], ![-35, -2, 1]]
  ![![4, 0, 0], ![-33, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-70, -4, 2]], ![![-70, -4, 2], ![-175, 50, -5]]]
 hmul := by decide
 f := ![![![![-139, 82, -436], ![2382, 300, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![107888, -57151, 306843], ![-1677248, -211317, 0]], ![![0, 0, 0], ![-2833, -2, 0]]]]
 g := ![![![![33, 2, 6], ![-64, -8, 0]], ![![-116, -8, -115], ![1142, 136, 0]]], ![![![-116, -8, -115], ![1142, 136, 0]], ![![-398, -12, -339], ![3351, 400, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-33, -2, 1]] ![![2, 0, 0], ![-35, -2, 1]]
  ![![-1379721215357, -401354532686, -60476501207]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-140, -8, 4]], ![![-66, -4, 2], ![-245, 46, -3]]]
 hmul := by decide
 f := ![![![![72165583685554819680, -63622446711965456169, 202598255847815448013], ![-1097976139861336164014, -136612751925388584055, 0]], ![![19315531404544310667, -23143386157885869, 0], ![-338517528671597, -401354532686, 0]]]]
 g := ![![![![-13630544, -844478, 346859]], ![![-25373180, 9031254, -1235487]]], ![![![-19501862, 4093388, -444314]], ![![1100968785, 47980702, -24427541]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -1, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![-35, -1, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![4, 0, 0], ![-33, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-70, -2, 2]], ![![-70, -2, 2], ![385, 81, -13]]]
 hmul := by decide
 f := ![![![![5386151, 52837155, 32523104], ![-104414346, -13075209, 0]], ![![0, 0, 0], ![-21844, 6, 0]]], ![![![-43089287, -422699660, -260186329], ![835319569, 104602272, 0]], ![![0, 0, 0], ![174753, -48, 0]]]]
 g := ![![![![14962, 36649, 20411], ![-127292, -15216, 0]], ![![-253939, -623078, -347032], ![2164218, 258696, 0]]], ![![![-253939, -623078, -347032], ![2164218, 258696, 0]], ![![1136038, 2787138, 1552319], ![-9680841, -1157184, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![4, 0, 0], ![-33, -1, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![-304499617, -88577533, -13346951]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![8, 0, 0], ![-140, -4, 4]], ![![-66, -2, 2], ![315, 79, -11]]]
 hmul := by decide
 f := ![![![![-17252774914154054930, -167804813415682535051, -104068772315434879182], ![333791581547819789304, 41826465482559361940, 0]], ![![-348034133122763538, 413763268257899, 0], ![997864527697, -323883126, 0]]]]
 g := ![![![![-164224, 941, 2207]], ![![2387700, 158057, -62557]]], ![![![1111738, 79499, -30175]], ![![123445, -855302, 149958]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![21688670091718276670375049391, 6309134013707292922322115756, 950666604514475904757981410])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-33, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-35, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-35, -2, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-70, -2, 2]], ![![-70, -4, 2], ![105, 65, -10]]]
 hmul := by decide
 f := ![![![![5653, 54782, 33915], ![-108859, -13632, 0]], ![![123, 0, 0], ![-2, 0, 0]]], ![![![2774, 26741, 16554], ![-53135, -6654, 0]], ![![60, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-29, 5, 1], ![-12, 0, 0]]], ![![![-29, 4, 1], ![-12, 0, 0]], ![![38, 18, -5], ![29, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![-35, -2, 1]] ![![4, 0, 0], ![-33, -1, 1]]
  ![![4, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8, 0, 0], ![-66, -2, 2]], ![![-140, -8, 4], ![35, 61, -8]]]
 hmul := by decide
 f := ![![![![453206808, 1111904883, 619288693], ![-3862110170, -461651568, 0]], ![![339, 0, 0], ![-4, 0, 0]]], ![![![-112306909, -275535635, -153462861], ![957050374, 114399586, 0]], ![![-84, 0, 0], ![1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-15, -2, 0], ![6, 1, 0]]], ![![![-33, -4, 0], ![8, 2, 0]], ![![10, 14, 0], ![5, -4, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-33, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-33, -2, 1]] ![![2, 0, 0], ![-35, -1, 1]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-140, -4, 4]], ![![-66, -4, 2], ![35, 63, -8]]]
 hmul := by decide
 f := ![![![![3433790739, 33420005357, 20715521404], ![-66443579410, -8325851555, 0]], ![![69961968, -378, 0], ![-4, 0, 0]]], ![![![872064587, 8487530193, 5261028880], ![-16874380488, -2114479507, 0]], ![![17767930, -96, 0], ![-1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-32, -32, -33], ![-12, 68, 0]]], ![![![-15, -15, -15], ![-6, 31, 0]], ![![7, 7, -9], ![7, 14, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-33, -2, 1]] ![![4, 0, 0], ![-33, -1, 1]]
  ![![4, 0, 0], ![-69, -3, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![16, 0, 0], ![-132, -4, 4]], ![![-132, -8, 4], ![-31, 59, -6]]]
 hmul := by decide
 f := ![![![![477511366910, 1171534095461, 652499978650], ![-4069227306171, -486409075410, 0]], ![![165347, 0, 0], ![4, 0, 0]]], ![![![-8233164424701, -20199378497760, -11250286346426], ![70160879541839, 8386577101785, 0]], ![![-2850883, 0, 0], ![-69, 0, 0]]]]
 g := ![![![![4, 0, 0], ![0, 0, 0]], ![![36, 2, -1], ![4, 0, 0]]], ![![![36, 1, -1], ![4, 0, 0]], ![![44, 17, -3], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-69, -3, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
