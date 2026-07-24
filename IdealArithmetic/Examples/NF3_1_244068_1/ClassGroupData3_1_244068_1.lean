import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_244068_1.RI3_1_244068_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-22682701, 29836284, -7718512]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![50984514992545207, -57049937272612440, 35306536194485181]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![14, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![14, 1, 1]] ![![3, 0, 0], ![14, 1, 1]]
  ![![3, 0, 0], ![16, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![42, 3, 3]], ![![42, 3, 3], ![214, -9, 10]]]
 hmul := by decide
 f := ![![![![1399009, -12331859, -6925781], ![109543, 0, -2302252]], ![![0, 0, 0], ![-15750, 0, 32]]], ![![![7344880, -64742648, -36360567], ![575096, 0, -12086896]], ![![0, 0, 0], ![-82688, 0, 168]]]]
 g := ![![![![-13, 0, -1], ![3, 0, 0]], ![![-2, 1, 0], ![3, 0, 0]]], ![![![-2, 1, 0], ![3, 0, 0]], ![![2, -3, -1], ![13, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![3, 0, 0], ![16, 0, 1]] ![![3, 0, 0], ![14, 1, 1]]
  ![![-22682701, 29836284, -7718512]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![9, 0, 0], ![42, 3, 3]], ![![48, 0, 3], ![226, 0, 7]]]
 hmul := by decide
 f := ![![![![-4167894227, 36701143251, 20654736991], ![-331546245, 0, 6860121130]], ![![0, 0, 0], ![45365402, 0, 0]]]]
 g := ![![![![50658904186581811, 641474638938868, 2312463064920336]], ![![241371059655002638, 3056390891761453, 11018036598997709]]], ![![![263924518383803032, 3341976851962936, 12047550386040309]], ![![1257503329258910014, 15923291414472512, 57402149723084977]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1077396602431352810393427722357933911, 13642667713323239452749497904945246, 49180689740483542460257715724208155])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![14, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![16, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
