import IdealArithmetic.Examples.NF3_1_796835_2.ClassGroupData3_1_796835_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![5, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![5, 1, 0]] 
 ![![19, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![5, 1, 0], ![3, 9, 9], ![-141, -20, 2]]]
  hmulB := by decide  
  f := ![![![-140, -465, -468], ![-57, 988, 0]], ![![-39, -117, -117], ![1, 247, 0]], ![![-60, -196, -197], ![-20, 416, 0]]]
  g := ![![![1, 0, 0], ![-5, 19, 0], ![-8, 0, 19]], ![![0, 1, 0], ![-6, 9, 9], ![-3, -20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![3, 4, 9], ![-141, -20, -3]]]
  hmulB := by decide  
  f := ![![![-14, -20, -45], ![0, 35, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-10, -14, -32], ![-2, 25, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-6, 4, 9], ![-18, -20, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![5, 1, 0], ![8, 0, 1]] ![2108971976667486228034948427966569274, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1019441886816148579417436962794534908, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2108971976667486228034948427966569287, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]
 hxeq :=  rfl
 m := 13
 C := ![2108971976667486228034948427966569274, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![5, 1, 0], ![8, 0, 1]] ![-1113, 16, -47] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-43, 16, -47]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1101, 16, -47]
 hxeq :=  rfl
 m := 12
 C := ![-1113, 16, -47]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] ![2108971976667486228034948427966569286, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-757579554026643535550279318563056332, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2108971976667486228034948427966569287, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]
 hxeq :=  rfl
 m := 1
 C := ![2108971976667486228034948427966569286, 1923824331681584734789440973681998150, 1482405770970798195377380731581592722]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] ![-1103, 16, -47] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-124, 16, -47]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1101, 16, -47]
 hxeq :=  rfl
 m := 2
 C := ![-1103, 16, -47]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

end Sat3
