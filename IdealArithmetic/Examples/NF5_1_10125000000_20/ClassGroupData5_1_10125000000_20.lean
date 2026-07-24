import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_10125000000_20.RI5_1_10125000000_20

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-6667430, 4728448, 3761190, 1848488, 12175998]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![522639039, 373208254, 253932382, 152549974, 973964986]

def zeta2 := B.equivFun.symm ![-40361836033584012207962736373416606079185181, -28625023032266024058189980995879926936502830, -19477438336700166956474752701882523412401025, -11706991660938503323426989438545528946007265, -74738161282290023723164688025083459985227010]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]] ![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]]
  ![![-6667430, 4728448, 3761190, 1848488, 12175998]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![80, 54, 36, 22, 140]], ![![80, 54, 36, 22, 140], ![538, 504, 346, 204, 1306]]]
 hmul := by decide
 f := ![![![![410867660, -72522407, -73198911, -26231930, -186374933], ![-87884426, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![10001145, 0, 0, 0, 0]]]]
 g := ![![![![24519484392444, 17389466744996, 11832384059638, 7111901427725, 45402820068845]], ![![209104917001650, 148299325638999, 100907900309877, 60651094205989, 387200349329640]]], ![![![209104917001650, 148299325638999, 100907900309877, 60651094205989, 387200349329640]], ![![1783270219488889, 1264713306479652, 860553908124195, 517239343903619, 3302088070601353]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![5680453783, -2723711974, -3571773442, -1946139014, -11887509046])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-38713807666625831445398132749521321, -85215935613816451355167235822678670, -55982934604135449041367808920854075, -32276741251363137590086015270117385, -207518822613094638141568440363074990])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
