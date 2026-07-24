import IdealArithmetic.Examples.NF5_1_2025000000_5.ClassGroupData5_1_2025000000_5
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_2025000000_5.RI5_1_2025000000_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq41 : Fact $ Nat.Prime 41 := {out := by norm_num}
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R41 : IsOrderOf (6 : ZMod 41) 40 where
 m := 2
 P := ![2, 5]
 e := ![3, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 1, -1, 4, 0], ![0, 0, -1, -5, 1], ![58, 1, 4, -11, -3]]]
  hmulB := by decide  
  f := ![![![2050, -5788, 4867, -22072, 280], ![21173, 651, 160208, -8680, 0]], ![![1942, -5483, 4610, -20914, 266], ![20058, 620, 151776, -8246, 0]], ![![1528, -4320, 3633, -16486, 210], ![15782, 497, 119629, -6510, 0]], ![![926, -2604, 2190, -9935, 126], ![9564, 318, 72114, -3906, 0]], ![![1986, -5602, 4710, -21360, 271], ![20512, 630, 155040, -8400, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-28, 31, 0, 0, 0], ![-22, 0, 31, 0, 0], ![-14, 0, 0, 31, 0], ![-30, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![-2, 1, -1, 4, 0], ![2, 0, -1, -5, 1], ![6, 1, 4, -11, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-12, 1, 0, 0, 0], ![0, -12, 1, 0, 0], ![0, 1, -10, 4, 0], ![0, 0, -1, -14, 1], ![58, 1, 4, -11, -12]]]
  hmulB := by decide  
  f := ![![![-66287, 20650, -175984, 77736, -504], ![-226484, -8692, -724470, 20664, 0]], ![![-46907, 14611, -124513, 55006, -357], ![-160268, -6150, -512582, 14637, 0]], ![![-33212, 10350, -88182, 38944, -252], ![-113476, -4345, -363014, 10332, 0]], ![![-19308, 6024, -51314, 22667, -147], ![-65970, -2519, -211242, 6027, 0]], ![![-38808, 12088, -103015, 45504, -295], ![-132596, -5089, -424080, 12096, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-29, 41, 0, 0, 0], ![-20, 0, 41, 0, 0], ![-12, 0, 0, 41, 0], ![-24, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![8, -12, 1, 0, 0], ![3, 1, -10, 4, 0], ![4, 0, -1, -14, 1], ![9, 1, 4, -11, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 41 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-6, 1, 0, 0, 0], ![0, -6, 1, 0, 0], ![0, 1, -4, 4, 0], ![0, 0, -1, -8, 1], ![58, 1, 4, -11, -6]]]
  hmulB := by decide  
  f := ![![![31507, -36757, 127334, -133224, 645], ![320311, 5185, 1952976, -39345, 0]], ![![29365, -34270, 118742, -124240, 602], ![298535, 4880, 1821216, -36722, 0]], ![![14623, -17077, 59179, -61928, 301], ![148663, 2441, 907680, -18361, 0]], ![![29403, -34303, 118849, -124347, 602], ![298921, 4881, 1822848, -36722, 0]], ![![27894, -32534, 112721, -117936, 571], ![283580, 4645, 1728864, -34830, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-55, 61, 0, 0, 0], ![-25, 0, 61, 0, 0], ![-57, 0, 0, 61, 0], ![-54, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![5, -6, 1, 0, 0], ![-3, 1, -4, 4, 0], ![7, 0, -1, -8, 1], ![14, 1, 4, -11, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] ![94320, 49754, 42647, 22399, 6349] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-88422, 49754, 42647, 22399, 6349]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![94349, 49754, 42647, 22399, 6349]
 hxeq :=  rfl
 m := 29
 C := ![94320, 49754, 42647, 22399, 6349]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] ![-4436600, -499539, -81866, 425045, 249983] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-67696, -499539, -81866, 425045, 249983]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4436583, -499539, -81866, 425045, 249983]
 hxeq :=  rfl
 m := 17
 C := ![-4436600, -499539, -81866, 425045, 249983]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] ![-27, -30, 3, -4, 3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![23, -30, 3, -4, 3]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, -30, 3, -4, 3]
 hxeq :=  rfl
 m := 30
 C := ![-27, -30, 3, -4, 3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![94323, 49754, 42647, 22399, 6349] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-63967, 49754, 42647, 22399, 6349]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![94349, 49754, 42647, 22399, 6349]
 hxeq :=  rfl
 m := 26
 C := ![94323, 49754, 42647, 22399, 6349]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![-4436617, -499539, -81866, 425045, 249983] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![14322, -499539, -81866, 425045, 249983]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4436583, -499539, -81866, 425045, 249983]
 hxeq :=  rfl
 m := 34
 C := ![-4436617, -499539, -81866, 425045, 249983]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 19
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![-7, -30, 3, -4, 3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![19, -30, 3, -4, 3]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, -30, 3, -4, 3]
 hxeq :=  rfl
 m := 10
 C := ![-7, -30, 3, -4, 3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![94311, 49754, 42647, 22399, 6349] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-87343, 49754, 42647, 22399, 6349]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![94349, 49754, 42647, 22399, 6349]
 hxeq :=  rfl
 m := 38
 C := ![94311, 49754, 42647, 22399, 6349]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 27
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![-4436593, -499539, -81866, 425045, 249983] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-207245, -499539, -81866, 425045, 249983]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4436583, -499539, -81866, 425045, 249983]
 hxeq :=  rfl
 m := 10
 C := ![-4436593, -499539, -81866, 425045, 249983]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 23
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![-55, -30, 3, -4, 3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![26, -30, 3, -4, 3]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![3, -30, 3, -4, 3]
 hxeq :=  rfl
 m := 58
 C := ![-55, -30, 3, -4, 3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 36
 hpow := by zmod_pow
 heql := by decide

end Sat5
