import IdealArithmetic.Examples.NF3_1_399735_1.ClassGroupData3_1_399735_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_399735_1.RI3_1_399735_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![1, 1, 0]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![1, 1, 0], ![0, 2, 2], ![384, 76, 0]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -2, -1], ![6, 4, 0]]]
  g := ![![![1, 0, 0], ![-1, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-2, 2, 2], ![44, 76, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![0, -1, 2], ![384, 76, -3]]]
  hmulB := by decide  
  f := ![![![3, 5, -12], ![13, 78, 0]], ![![1, 5, -10], ![1, 65, 0]], ![![2, 5, -11], ![7, 72, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-12, 0, 13]], ![![-1, 1, 0], ![-1, -1, 2], ![-32, 76, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492290, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-65668439952817954250241397273200212049093921779031290374499458141599232818836224598, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492287, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]
 hxeq :=  rfl
 m := 3
 C := ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492290, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] ![4445973603914535295, 311037384426852398, -92825645688721961] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![670270013374287809, 311037384426852398, -92825645688721961]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4445973603914535301, 311037384426852398, -92825645688721961]
 hxeq :=  rfl
 m := 6
 C := ![4445973603914535295, 311037384426852398, -92825645688721961]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492293, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![189258991236463394126555584398865500118431241292783016372995844167666593043378905155, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492287, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]
 hxeq :=  rfl
 m := 6
 C := ![-942025009646687929027826020612227395622105483608343710519012972635803723986249492293, -270855559529643061568975126488647452733868395344919285285880601725139027226820379900, -35248395074553197951193518868529743090763272635034232101939360653245011171262590034]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] ![4445973603914535299, 311037384426852398, -92825645688721961] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![164497701806447881, 311037384426852398, -92825645688721961]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4445973603914535301, 311037384426852398, -92825645688721961]
 hxeq :=  rfl
 m := 2
 C := ![4445973603914535299, 311037384426852398, -92825645688721961]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat3
