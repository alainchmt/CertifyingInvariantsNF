import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_412776_3.RI3_1_412776_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![29, 2, 1]

def alpha1 := B.equivFun.symm ![-9, -1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![905, 1270, -768]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![15, 1, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![2, 0, 0], ![15, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![30, 2, 2]], ![![30, 2, 2], ![449, 44, 11]]]
 hmul := by decide
 f := ![![![![13948734, 373001204, -181186285], ![200523034, 0, -27015744]], ![![0, 0, 0], ![-44354, 0, -9]]], ![![![102290871, 2735344928, -1328700761], ![1470503727, 0, -198115656]], ![![0, 0, 0], ![-325263, 0, -66]]]]
 g := ![![![![-13, -2, -1], ![2, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![-8, -9, -10], ![31, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![15, 2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![29, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![30, 2, 2]], ![![30, 4, 2], ![561, 38, 13]]]
 hmul := by decide
 f := ![![![![11768, 314545, -152852], ![169147, 0, -22791]], ![![0, 0, 0], ![-29, 0, 0]]]]
 g := ![![![![4, -1, 0]], ![![-26, 5, 1]]], ![![![-26, 7, 0]], ![![197, -34, -6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-2, 1, 0]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![121, 0, 0], ![9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![-22, 11, 0], ![4, -4, 2]]]
 hmul := by decide
 f := ![![![![-68415719, 35223572, -1009112], ![-374931194, 4806483, 0]], ![![0, 0, 0], ![8131563, -12100, 0]]], ![![![-5032231, 2590825, -74224], ![-27577586, 353535, 0]], ![![0, 0, 0], ![598107, -890, 0]]]]
 g := ![![![![226, 25, 0], ![-3025, 0, 0]], ![![-46, -14, -2], ![616, 121, 0]]], ![![![-46, -14, -2], ![616, 121, 0]], ![![-8, -1, 0], ![108, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![9, 1, 0]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![-9, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-242, 121, 0]], ![![99, 11, 0], ![-18, 7, 2]]]
 hmul := by decide
 f := ![![![![1278580844, -655919182, 14414502], ![7030200952, -81715639, 0]], ![![-4984225, 26848465, 0], ![-598107, 890, 0]]]]
 g := ![![![![-123, 9, -2]], ![![2, -9, 2]]], ![![![-11, 0, 0]], ![![2, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![467105209, 31880794, 16307144])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![15, 1, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![22, 0, 0], ![7, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![22, 0, 0], ![-4, 2, 0]], ![![165, 11, 11], ![82, -8, 0]]]
 hmul := by decide
 f := ![![![![8240734, -4111986, 121403], ![44198308, -593483, 0]], ![![-27126, 0, -22], ![0, 0, 0]]], ![![![2247777, -1121601, 33113], ![12055715, -161873, 0]], ![![-7399, 0, -6], ![0, 0, 0]]]]
 g := ![![![![2044603, -309815, 11160], ![636988, -441408, -22]], ![![-556042, 84254, -3036], ![-173208, 120042, 6]]], ![![![14320947, -2170023, 78170], ![4461589, -3091737, -154]], ![![8357956, -1266464, 45621], ![2603862, -1804392, -90]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![22, 0, 0], ![7, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![15, 1, 1]] ![![121, 0, 0], ![9, 1, 0]]
  ![![242, 0, 0], ![29, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![242, 0, 0], ![18, 2, 0]], ![![1815, 121, 121], ![247, 3, 11]]]
 hmul := by decide
 f := ![![![![5808181232, 647907105, 2449005], ![-77756871896, -48993989, 0]], ![![-3279826, 0, -242], ![0, 0, 0]]], ![![![672022728, 74964647, 283355], ![-8996686412, -5668638, 0]], ![![-379485, 0, -28], ![0, 0, 0]]]]
 g := ![![![![248721081, 17898187, 4381888], ![29897648, -545156304, -242]], ![![16462500, 1184656, 290031], ![1978898, -36083136, -16]]], ![![![1742144725, 125366257, 30692548], ![209414337, -3818498640, -1694]], ![![250803821, 18048063, 4418581], ![30148049, -549721344, -244]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![242, 0, 0], ![29, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0], ![15, 2, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![22, 0, 0], ![5, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![22, 0, 0], ![-4, 2, 0]], ![![165, 22, 11], ![82, -10, 2]]]
 hmul := by decide
 f := ![![![![6674, -3318, 97], ![35794, -473, 0]], ![![-22, 0, 0], ![0, 0, 0]]], ![![![1519, -755, 22], ![8147, -107, 0]], ![![-5, 0, 0], ![0, 0, 0]]]]
 g := ![![![![18268, -3090, 507], ![3894, -3762, 0]], ![![-3415, 577, -95], ![-722, 703, 0]]], ![![![135991, -23004, 3774], ![29007, -28006, 0]], ![![68548, -11597, 1902], ![14626, -14117, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![22, 0, 0], ![5, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![2, 0, 0], ![15, 2, 1]] ![![121, 0, 0], ![9, 1, 0]]
  ![![242, 0, 0], ![-83, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![242, 0, 0], ![18, 2, 0]], ![![1815, 242, 121], ![247, 12, 13]]]
 hmul := by decide
 f := ![![![![428578, 47921, 179], ![-5737578, -3509, 0]], ![![-242, 0, 0], ![0, 0, 0]]], ![![![-147010, -16445, -63], ![1968094, 1301, 0]], ![![83, 0, 0], ![0, 0, 0]]]]
 g := ![![![![257919, -267572, 10694], ![-90508, -624360, 0]], ![![19247, -19891, 794], ![-6508, -46410, 0]]], ![![![1932671, -2005228, 80146], ![-678931, -4679070, 0]], ![![263167, -273023, 10912], ![-92371, -637080, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![242, 0, 0], ![-83, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
