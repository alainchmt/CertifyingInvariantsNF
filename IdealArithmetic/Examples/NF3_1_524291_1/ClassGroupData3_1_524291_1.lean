import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_524291_1.RI3_1_524291_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![5775, 593, 352]

def alpha1 := B.equivFun.symm ![-17, -67, 29]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-323159, 31712, 2216]

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
 f := ![![![![1403, -280, 40], ![562, 0, -24]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![-351, 70, -10], ![-140, 0, 6]], ![![0, 0, 0], ![1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![-2, 0, 0]]], ![![![0, 1, 0], ![-2, 0, 0]], ![![-131, -8, 0], ![33, 0, 4]]]]
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
 f := ![![![![-320227, 1601134, 0], ![640454, 0, 0]], ![![-7664860, 0, -54749], ![27448, 0, -98]]], ![![![45745, -228725, 0], ![-91490, 0, 0]], ![![1094940, 0, 7821], ![-3921, 0, 14]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![-4, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-68, -2, 0], ![15, 0, 4]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![-1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![5775, 593, 352]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![-2, 2, 0], ![1, -1, 4]]]
 hmul := by decide
 f := ![![![![-455545496, -1500010103, 415847178], ![3117160234, -204995472, -3904156]], ![![-453918668, 0, -38942175], ![19523455, 0, -69706]]]]
 g := ![![![![-354, 31, 4]], ![![134, -177, 68]]], ![![![122, -52, 16]], ![![1129, 61, -80]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![56, 0, 0], ![-1, 1, 0]] ![![56, 0, 0], ![-1, 1, 0]]
  ![![-17, -67, 29]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![3136, 0, 0], ![-56, 56, 0]], ![![-56, 56, 0], ![3, -3, 4]]]
 hmul := by decide
 f := ![![![![-51908099, -295800, 0], ![921667, 0, 20879705]], ![![0, 0, 0], ![-292286291, 27768, -7215]]]]
 g := ![![![![207050, 21261, 12620]], ![![28612, 2938, 1744]]], ![![![28612, 2938, 1744]], ![![3954, 406, 241]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![81203948249, 8338315488, 4949545496])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![56, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![56, 0, 0], ![-1, 1, 0]]
  ![![112, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![112, 0, 0], ![-2, 2, 0]], ![![56, 56, 0], ![1, -1, 4]]]
 hmul := by decide
 f := ![![![![16889816, 50745, 0], ![-300664, 0, -6758074]], ![![0, 0, 0], ![3388112, 0, -12100]]], ![![![-153543, -462, 0], ![2772, 0, 61437]], ![![0, 0, 0], ![-30801, 0, 110]]]]
 g := ![![![![554, 2, 0], ![-2, 111, -444]], ![![-9, -1, 0], ![110, -2, 8]]], ![![![275, 1, 0], ![54, 55, -220]], ![![5, 0, 0], ![3, 2, -4]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![112, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-1, 1, 0]] ![![56, 0, 0], ![-1, 1, 0]]
  ![![224, 0, 0], ![111, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![224, 0, 0], ![-4, 4, 0]], ![![-56, 56, 0], ![3, -3, 4]]]
 hmul := by decide
 f := ![![![![63238, -61557, 0], ![-2184, 0, -25314]], ![![0, 0, 0], ![672, 0, 98568]]], ![![![31334, -30501, 0], ![-1094, 0, -12543]], ![![0, 0, 0], ![333, 0, 48840]]]]
 g := ![![![![223, -12320, 0], ![220, 25086, -888]], ![![-115, 221, 0], ![220, -452, 16]]], ![![![-167, 3107, 0], ![168, -6328, 224]], ![![2, -167, 0], ![5, 340, -12]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![224, 0, 0], ![111, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![-1, 1, 0]] ![![56, 0, 0], ![-1, 1, 0]]
  ![![448, 0, 0], ![-113, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![448, 0, 0], ![-8, 8, 0]], ![![-56, 56, 0], ![3, -3, 4]]]
 hmul := by decide
 f := ![![![![114062561851, 650637910, 0], ![-2025212912, 0, -45857729258]], ![![0, 0, 0], ![91660258656, -55150576, 197136]]], ![![![-28772533969, -164124855, 0], ![510864473, 0, 11567713818]], ![![0, 0, 0], ![-23121503349, 13911855, -49728]]]]
 g := ![![![![774, -12541, 0], ![-8, -49284, -1776]], ![![97, 225, 0], ![440, 888, 32]]], ![![![1, 1581, 0], ![392, 6216, 224]], ![![63, -85, 0], ![229, -332, -12]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![448, 0, 0], ![-113, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
