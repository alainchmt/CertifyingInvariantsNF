import IdealArithmetic.Examples.NF3_1_508248_2.ClassGroupData3_1_508248_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq37 : Fact $ Nat.Prime 37 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-18, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![-2, 4, 10], ![138, 4, 0]]]
  hmulB := by decide  
  f := ![![![69, -141, -350], ![13, 455, 0]], ![![10, -20, -50], ![1, 65, 0]], ![![64, -130, -323], ![10, 420, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-12, 0, 13]], ![![0, 1, 0], ![-10, 4, 10], ![10, 4, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-18, 1, 0]] 
 ![![37, 0, 0], ![19, 1, 0], ![8, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-18, 1, 0], ![-2, -16, 10], ![138, 4, -20]]]
  hmulB := by decide  
  f := ![![![137, 1088, -680], ![0, 2516, 0]], ![![69, 544, -340], ![1, 1258, 0]], ![![34, 235, -147], ![9, 544, 0]]]
  g := ![![![1, 0, 0], ![-19, 37, 0], ![-8, 0, 37]], ![![-1, 1, 0], ![6, -16, 10], ![6, 4, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 37 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] ![-346882673112617, 10608407217225, 16529587380504] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-43573425854855, 10608407217225, 16529587380504]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-346882673112607, 10608407217225, 16529587380504]
 hxeq :=  rfl
 m := 10
 C := ![-346882673112617, 10608407217225, 16529587380504]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] ![10652005, -977389, 110766] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![867507, -977389, 110766]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10652007, -977389, 110766]
 hxeq :=  rfl
 m := 2
 C := ![10652005, -977389, 110766]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![19, 1, 0], ![8, 0, 1]] ![-346882673112643, 10608407217225, 16529587380504] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-18396732683350, 10608407217225, 16529587380504]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-346882673112607, 10608407217225, 16529587380504]
 hxeq :=  rfl
 m := 36
 C := ![-346882673112643, 10608407217225, 16529587380504]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 18
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![19, 1, 0], ![8, 0, 1]] ![10652002, -977389, 110766] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![765845, -977389, 110766]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10652007, -977389, 110766]
 hxeq :=  rfl
 m := 5
 C := ![10652002, -977389, 110766]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 23
 hpow := by zmod_pow
 heql := by decide

end Sat3
