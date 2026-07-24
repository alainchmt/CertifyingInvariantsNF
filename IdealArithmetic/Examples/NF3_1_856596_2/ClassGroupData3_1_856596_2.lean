import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![31820381388217399233703469882, 3491806425935584980359632214, 2435399953449439519981961599]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2199966188860623243419839637945345080, 23453403743587624138577357925239492, 146250198698687873969302070829777117]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 0, 1]] ![![3, 0, 0], ![-1, 0, 1]]
  ![![9, 0, 0], ![-4, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 0, 3]], ![![-3, 0, 3], ![-86, 14, 2]]]
 hmul := by decide
 f := ![![![![15945246, 185310, 1326391], ![-4872951, -296496, 0]], ![![0, 0, 0], ![7893, -18, 0]]], ![![![-7086775, -82360, -589508], ![2165759, 131776, 0]], ![![0, 0, 0], ![-3508, 8, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![3, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![224, 0, 6], ![-94, -14, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-4, 0, 1]] ![![3, 0, 0], ![-1, 0, 1]]
  ![![31820381388217399233703469882, 3491806425935584980359632214, 2435399953449439519981961599]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 0, 9]], ![![-12, 0, 3], ![-83, 14, -1]]]
 hmul := by decide
 f := ![![![![-28102536603505155217416943080878222, 0, 4117158431377944553307524922819101], ![10739898344961033256908156001232444, 0, 0]], ![![-69125460476710181024842898359176080, 50592255903621709712567504913978, 0], ![11219526262581071107824502674182, 120297912700998426974094615100, 0]]]]
 g := ![![![![1204837529900568, -22640268788332, -69194218571285]], ![![269243970088821, -337999865858218, 355058560183903]]], ![![![-311864519937249, -105119865689962, 141417592918396]], ![![-10199227430362159, 589868856492540, 142582618629275]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3182802369801828369578612686958014140846484251250750806856451368119052222, -349264505405088469470943637736709069162683692128104507267760229602492634, -243598486412999509570475683910617401800094074725297612760760775801228677])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
