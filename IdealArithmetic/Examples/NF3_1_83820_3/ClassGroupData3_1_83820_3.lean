import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_83820_3.RI3_1_83820_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-711, 156, 65]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-30181761, 1063318, 1300667]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![90101, -87284, 227260], ![-59128, -363616, 0]], ![![0, 0, 0], ![68370, 192, 0]]], ![![![-41295, 40004, -104160], ![27103, 166656, 0]], ![![0, 0, 0], ![-31336, -88, 0]]]]
 g := ![![![![57, -314, 160], ![-54, -720, 0]], ![![-27, 157, -80], ![30, 360, 0]]], ![![![-27, 157, -80], ![30, 360, 0]], ![![18, -98, 50], ![-16, -224, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![-711, 156, 65]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-12, 3, 0], ![5, -5, 2]]]
 hmul := by decide
 f := ![![![![-454092240, 767430133, -379959701], ![-2232125417, 616542231, 0]], ![![1081011584, -140769278, 0], ![2821415, -15584, 0]]]]
 g := ![![![![-143926, 52845, -12077]], ![![419849, -154155, 35230]]], ![![![187925, -69000, 15769]], ![![-548199, 201281, -46000]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![67721301547448, -24865078707463, 5682571318383])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
