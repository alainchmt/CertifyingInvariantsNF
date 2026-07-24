import IdealArithmetic.Examples.NF3_1_856596_2.ClassGroupData3_1_856596_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![6, 3, 12], ![177, 3, -3]]]
  hmulB := by decide  
  f := ![![![-35, -18, -72], ![0, 42, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-20, -11, -41], ![5, 24, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-4, 0, 7]], ![![0, 1, 0], ![-6, 3, 12], ![27, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![6, 6, 12], ![177, 3, 0]]]
  hmulB := by decide  
  f := ![![![46, 55, 120], ![35, -70, 0]], ![![18, 22, 48], ![15, -28, 0]], ![![39, 47, 103], ![31, -60, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-12, 6, 12], ![24, 3, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] ![-2199966188860623243419839637945345083, 23453403743587624138577357925239492, 146250198698687873969302070829777117] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-397852426236482105613863988752064793, 23453403743587624138577357925239492, 146250198698687873969302070829777117]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2199966188860623243419839637945345080, 23453403743587624138577357925239492, 146250198698687873969302070829777117]
 hxeq :=  rfl
 m := 3
 C := ![-2199966188860623243419839637945345083, 23453403743587624138577357925239492, 146250198698687873969302070829777117]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] ![31820381388217399233703469879, 3491806425935584980359632214, 2435399953449439519981961599] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![3154111653488520164825089069, 3491806425935584980359632214, 2435399953449439519981961599]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![31820381388217399233703469882, 3491806425935584980359632214, 2435399953449439519981961599]
 hxeq :=  rfl
 m := 3
 C := ![31820381388217399233703469879, 3491806425935584980359632214, 2435399953449439519981961599]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] ![-2199966188860623243419839637945345081, 23453403743587624138577357925239492, 146250198698687873969302070829777117] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-449689656040501908521626305242818037, 23453403743587624138577357925239492, 146250198698687873969302070829777117]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2199966188860623243419839637945345080, 23453403743587624138577357925239492, 146250198698687873969302070829777117]
 hxeq :=  rfl
 m := 1
 C := ![-2199966188860623243419839637945345081, 23453403743587624138577357925239492, 146250198698687873969302070829777117]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] ![31820381388217399233703469878, 3491806425935584980359632214, 2435399953449439519981961599] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![961794627102001024676114806, 3491806425935584980359632214, 2435399953449439519981961599]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![31820381388217399233703469882, 3491806425935584980359632214, 2435399953449439519981961599]
 hxeq :=  rfl
 m := 4
 C := ![31820381388217399233703469878, 3491806425935584980359632214, 2435399953449439519981961599]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

end Sat3
