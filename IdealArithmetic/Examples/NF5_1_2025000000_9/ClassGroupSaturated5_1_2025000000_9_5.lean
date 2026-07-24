import IdealArithmetic.Examples.NF5_1_2025000000_9.ClassGroupData5_1_2025000000_9
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_2025000000_9.RI5_1_2025000000_9

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![2, -3, 1, -1, 6], ![-72, -34, 4, 6, 1]]]
  hmulB := by decide  
  f := ![![![-31, -208, 0, -496, -96], ![0, -496, 7936, 496, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![15, 0, 16, 0, 0]], ![![-21, -141, 0, -336, -65], ![3, -336, 5376, 336, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![-21, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![-4, -3, 1, -1, 6], ![-3, -34, 4, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 1, -11, 2, 0], ![2, -3, 1, -12, 6], ![-72, -34, 4, 6, -10]]]
  hmulB := by decide  
  f := ![![![171408, -16519, -18138, -930, 2160], ![481027, -4557, -52545, -11160, 0]], ![![114276, -11013, -12092, -620, 1440], ![320696, -3038, -35030, -7440, 0]], ![![21412, -2056, -2302, -110, 270], ![60089, -557, -6665, -1395, 0]], ![![121422, -11704, -12846, -659, 1530], ![340750, -3234, -37215, -7905, 0]], ![![154840, -14919, -16383, -840, 1951], ![434532, -4107, -47460, -10080, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-20, 31, 0, 0, 0], ![-3, 0, 31, 0, 0], ![-22, 0, 0, 31, 0], ![-28, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![7, -11, 1, 0, 0], ![-1, 1, -11, 2, 0], ![5, -3, 1, -12, 6], ![24, -34, 4, 6, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![6, 1, 0, 0, 0], ![0, 6, 1, 0, 0], ![0, 1, 6, 2, 0], ![2, -3, 1, 5, 6], ![-72, -34, 4, 6, 7]]]
  hmulB := by decide  
  f := ![![![3613861, 3507480, 17783939, 5937679, 8514], ![-36712057, 563152, -180882812, -86559, 0]], ![![420192, 407831, 2067849, 690411, 990], ![-4268596, 65514, -21032373, -10065, 0]], ![![1512775, 1468248, 7444463, 2485548, 3564], ![-15367797, 235766, -75718629, -36234, 0]], ![![2605334, 2528645, 12820978, 4280652, 6138], ![-26466754, 406013, -130403878, -62403, 0]], ![![3199146, 3104980, 15743159, 5256306, 7537], ![-32499100, 498535, -160125768, -76626, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 61, 0, 0, 0], ![-25, 0, 61, 0, 0], ![-44, 0, 0, 61, 0], ![-54, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-1, 6, 1, 0, 0], ![-4, 1, 6, 2, 0], ![-9, -3, 1, 5, 6], ![-10, -34, 4, 6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] ![-128571, -93443, -10436, 5627, 8855] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-10146, -93443, -10436, 5627, 8855]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-128547, -93443, -10436, 5627, 8855]
 hxeq :=  rfl
 m := 24
 C := ![-128571, -93443, -10436, 5627, 8855]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] ![630777067824, 455760802015, 48555409531, -28976360690, -44398778352] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![50424239136, 455760802015, 48555409531, -28976360690, -44398778352]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]
 hxeq :=  rfl
 m := 29
 C := ![630777067824, 455760802015, 48555409531, -28976360690, -44398778352]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] ![7001890, 1456956, -648479, -339780, 395103] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-41783, 1456956, -648479, -339780, 395103]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![7001899, 1456956, -648479, -339780, 395103]
 hxeq :=  rfl
 m := 9
 C := ![7001890, 1456956, -648479, -339780, 395103]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![-128567, -93443, -10436, 5627, 8855] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![45157, -93443, -10436, 5627, 8855]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-128547, -93443, -10436, 5627, 8855]
 hxeq :=  rfl
 m := 20
 C := ![-128567, -93443, -10436, 5627, 8855]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![630777067850, 455760802015, 48555409531, -28976360690, -44398778352] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-217724499097, 455760802015, 48555409531, -28976360690, -44398778352]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]
 hxeq :=  rfl
 m := 3
 C := ![630777067850, 455760802015, 48555409531, -28976360690, -44398778352]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![7001896, 1456956, -648479, -339780, 395103] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-767081, 1456956, -648479, -339780, 395103]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![7001899, 1456956, -648479, -339780, 395103]
 hxeq :=  rfl
 m := 3
 C := ![7001896, 1456956, -648479, -339780, 395103]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![-128557, -93443, -10436, 5627, 8855] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-537, -93443, -10436, 5627, 8855]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-128547, -93443, -10436, 5627, 8855]
 hxeq :=  rfl
 m := 10
 C := ![-128557, -93443, -10436, 5627, 8855]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 23
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![630777067811, 455760802015, 48555409531, -28976360690, -44398778352] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![5816736374, 455760802015, 48555409531, -28976360690, -44398778352]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]
 hxeq :=  rfl
 m := 42
 C := ![630777067811, 455760802015, 48555409531, -28976360690, -44398778352]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 56
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![7001895, 1456956, -648479, -339780, 395103] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![132572, 1456956, -648479, -339780, 395103]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![7001899, 1456956, -648479, -339780, 395103]
 hxeq :=  rfl
 m := 4
 C := ![7001895, 1456956, -648479, -339780, 395103]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

end Sat5
