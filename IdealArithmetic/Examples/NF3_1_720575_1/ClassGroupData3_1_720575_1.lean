import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_720575_1.RI3_1_720575_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-231191107, 276838904, 64445045]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1901442840839226076324861798928425537679753451, 348993599977226740709068779116546198878153158, 121643682555387767708756276457703694927989454]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-13, 2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-13, 2, 1]] ![![2, 0, 0], ![-13, 2, 1]]
  ![![-231191107, 276838904, 64445045]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-26, 4, 2]], ![![-26, 4, 2], ![-447, -60, 1]]]
 hmul := by decide
 f := ![![![![-1800252226, -7105295611, -1779410328], ![3706638732, 0, 0]], ![![0, 0, 0], ![-231191107, 0, 0]]]]
 g := ![![![![372308805209513292, -75368930982037868, 17856917632009523]], ![![1855345565132238950, -375589859518876255, 88987293536709479]]], ![![![1855345565132238950, -375589859518876255, 88987293536709479]], ![![9245838717455906037, -1871696211361003045, 443454944138495402]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3154374864962418822747172691123933405602834494945665586160333969028838174988840139326077475, 638560942320557148721190464186807361303112186292976124771854899996891702246098145042145950, -151292183681815828524592087920368521014135392213495675803410750341452036656478490068911746])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-13, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
