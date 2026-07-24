import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-50399288, 2697030, 491129]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1909480242515008478307664281449908943535, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![4, -2, 11]]]
 hmul := by decide
 f := ![![![![5287, -1068304, 3531], ![3203376, 23109, 0]], ![![0, 0, 0], ![-72198, -18, 0]]], ![![![-2351, 474772, -1573], ![-1423631, -10269, 0]], ![![0, 0, 0], ![32086, 8, 0]]]]
 g := ![![![![174, -241, 550], ![-81, -450, 0]], ![![-3, 5, -11], ![3, 9, 0]]], ![![![-3, 5, -11], ![3, 9, 0]], ![![81, -111, 253], ![-33, -206, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-50399288, 2697030, 491129]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-9, 3, 0], ![4, -5, 11]]]
 hmul := by decide
 f := ![![![![7356083491182, -596557466894502, -3679877693043], ![1788198491262350, -736954710578, 0]], ![![26106278284822, 5080615748064, 0], ![423384645672, 106192636, 0]]]]
 g := ![![![![1404216737525648, 117123628108608, 110183140707197]], ![![6877336420617161, 573628394948139, 539636443772093]]], ![![![1824373227697171, 152168255613177, 143151101021632]], ![![8935108169803788, 745264073859659, 701101371603281]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![8175091219729299849, -5326869337935292278, 3195681922367303720])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
