import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_905324_3.RI3_1_905324_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-13, 1, 0]

def alpha1 := B.equivFun.symm ![15, -4, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-81, 7, 2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![13, 0, 0], ![0, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![169, 0, 0], ![-13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![0, 13, 0]], ![![0, 13, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![2353, -180, 0], ![-12, 0, 0]], ![![0, 0, 0], ![0, -2184, 0]]], ![![![-181, 13, 0], ![12, 0, 0]], ![![0, 0, 0], ![0, 168, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![13, 0, 0]]], ![![![1, 0, 0], ![13, 0, 0]], ![![1, 0, 0], ![13, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![169, 0, 0], ![-13, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![-13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2197, 0, 0], ![0, 169, 0]], ![![-169, 13, 0], ![0, -13, 1]]]
 hmul := by decide
 f := ![![![![0, 12, 0], ![12, 0, 0]], ![![181, 349, 0], ![-2353, 168, 0]]]]
 g := ![![![![-183, -13, -1]], ![![-14, -13, -1]]], ![![![13, 0, 0]], ![![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-8, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![17, 0, 0], ![-8, 1, 0]] ![![17, 0, 0], ![-8, 1, 0]]
  ![![289, 0, 0], ![-76, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-136, 17, 0]], ![![-136, 17, 0], ![64, -16, 1]]]
 hmul := by decide
 f := ![![![![13810672961, -2009997949, 35457730], ![29336080413, -601342989, 0]], ![![0, 0, 0], ![-24619621, -10404, 0]]], ![![![-3643817586, 530319267, -9355193], ![-7740051916, 158658767, 0]], ![![0, 0, 0], ![6495658, 2745, 0]]]]
 g := ![![![![21281, -280, 0], ![80920, 0, 0]], ![![-9952, 207, -1], ![-37842, 289, 0]]], ![![![-9952, 207, -1], ![-37842, 289, 0]], ![![4728, -62, 0], ![17978, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![289, 0, 0], ![-76, 1, 0]] ![![17, 0, 0], ![-8, 1, 0]]
  ![![15, -4, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-2312, 289, 0]], ![![-1292, 17, 0], ![608, -84, 1]]]
 hmul := by decide
 f := ![![![![1203716090623, -173423017645, 2864041040], ![2557841844487, -48676431665, 0]], ![![97507710, -208444924, 0], ![-1363011, -576, 0]]]]
 g := ![![![![-449, -60, -16]], ![![40, 15, 4]]], ![![![108, 15, 4]], ![![-8, -4, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-10019, -1295, -267])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![-76, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![13, 0, 0], ![0, 1, 0]] ![![17, 0, 0], ![-8, 1, 0]]
  ![![221, 0, 0], ![26, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![221, 0, 0], ![-104, 13, 0]], ![![0, 17, 0], ![0, -8, 1]]]
 hmul := by decide
 f := ![![![![1913, -271, 17], ![4063, -68, 0]], ![![0, -169, 0], ![0, 0, 0]]], ![![![2, 0, 2], ![4, 0, 0]], ![![-3, -26, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![13, 0, 0]]], ![![![-2, 0, 0], ![17, 0, 0]], ![![4, 0, 0], ![-34, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![221, 0, 0], ![26, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![13, 0, 0], ![0, 1, 0]] ![![289, 0, 0], ![-76, 1, 0]]
  ![![3757, 0, 0], ![-1521, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3757, 0, 0], ![-988, 13, 0]], ![![0, 289, 0], ![0, -76, 1]]]
 hmul := by decide
 f := ![![![![293361, -4088, 220], ![1115540, -867, 0]], ![![0, -2821, 0], ![0, 0, 0]]], ![![![-118765, 1715, -89], ![-451618, 578, 0]], ![![-4, 1131, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![5, 0, 0], ![13, 0, 0]]], ![![![117, 0, 0], ![289, 0, 0]], ![![585, 0, 0], ![1445, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3757, 0, 0], ![-1521, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-13, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![169, 0, 0], ![-13, 1, 0]] ![![17, 0, 0], ![-8, 1, 0]]
  ![![2873, 0, 0], ![-858, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2873, 0, 0], ![-1352, 169, 0]], ![![-221, 17, 0], ![104, -21, 1]]]
 hmul := by decide
 f := ![![![![-29232502726931, 4257868604847, -75482627866], ![-62116596017787, 1283202378994, 0]], ![![-15124517772, 22812296, 0], ![0, 0, 0]]], ![![![8707553946647, -1268301278227, 22484186876], ![18502815713711, -382230493356, 0]], ![![4505175477, -6795152, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![50, 0, 0], ![169, 0, 0]]], ![![![5, 0, 0], ![17, 0, 0]], ![![250, 0, 0], ![837, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2873, 0, 0], ![-858, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![169, 0, 0], ![-13, 1, 0]] ![![289, 0, 0], ![-76, 1, 0]]
  ![![48841, 0, 0], ![13507, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![48841, 0, 0], ![-12844, 169, 0]], ![![-3757, 289, 0], ![988, -89, 1]]]
 hmul := by decide
 f := ![![![![-18496016928209822219, 258615478877662048, -200612220811705], ![-70333519696709776328, 57976924672514185, 0]], ![![-62764481117884, 4176503760, 0], ![0, 0, 0]]], ![![![-5117475040089865373, 71553689817336125, -55505357544040], ![-19459867112287392364, 16041046354161160, 0]], ![![-17365666714712, 1155554400, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-47, 0, 0], ![169, 0, 0]]], ![![![-80, 0, 0], ![289, 0, 0]], ![![3760, 0, 0], ![-13596, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48841, 0, 0], ![13507, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
