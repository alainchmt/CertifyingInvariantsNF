import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_67500000_3.RI5_1_67500000_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-39385593, -5185057, 14008882, -9338801, -13238284]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![3, -3, 1, 0, -2]

def zeta2 := B.equivFun.symm ![-23660192637015, -2254937192931, 7939006997157, -5704386158684, -4933097265316]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]], ![![0, 2, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide
 f := ![![![![127600, -57966, -64532, 116656, 235839], ![43476, -32264, 0, -76560, 4104]], ![![0, 0, 0, 0, 0], ![-340, 512, 0, 64, -4]]], ![![![63890, -29024, -32312, 58410, 118086], ![21769, -16154, 0, -38334, 2055]], ![![0, 0, 0, 0, 0], ![-170, 257, 0, 32, -2]]]]
 g := ![![![![24, -36, 0, 76, 43], ![8, 96, -80, -28, 4]], ![![20, -28, 0, 64, 37], ![8, 76, -66, -24, 4]]], ![![![20, -28, 0, 64, 37], ![8, 76, -66, -24, 4]], ![![1, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![-39385593, -5185057, 14008882, -9338801, -13238284]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![0, 4, 0, 0, 0]], ![![4, 2, 0, 0, 0], ![0, 2, 1, 0, 0]]]
 hmul := by decide
 f := ![![![![-118167501486771, 58738876154952, 61577125358851, -113606029551933, -228160843007951], ![-44054157116214, 30788562679426, 0, 75197500946127, -1773905752437]], ![![201044456724, -128987091630, 0, -61187301711, 3306244104], ![-951331071, 442269189, 0, 50754783, -30046792]]]]
 g := ![![![![-831769086765, 341059815510, 13825664259, -59290224306, -240325941260]], ![![632042487321, -259163628470, -10505809199, 45053298430, 182618238972]]], ![![![-99863299722, 40948093520, 1659927530, -7118462938, -28853851144]], ![![75883859025, -31115529055, -1261341446, 5409158695, 21925387902]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3, 1, 3, 10, 10])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![23584247655287866223380575, -9670519486412793918203507, -392017323521799411850117, 1681134052174844745054038, 6814278879505475012377484])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
