import IdealArithmetic.Examples.NF5_1_6250000_1.ClassGroupData5_1_6250000_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_6250000_1.RI5_1_6250000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq151 : Fact $ Nat.Prime 151 := {out := by norm_num}
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R151 : IsOrderOf (6 : ZMod 151) 150 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0], ![-48, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 1, 4, 2, 0], ![3, -1, 2, 7, 12], ![0, 0, 0, -2, 1]]]
  hmulB := by decide  
  f := ![![![1130, 286, 225, 319, 420], ![-2816, -77, -407, -385, 0]], ![![485, 123, 97, 137, 180], ![-1209, -33, -176, -165, 0]], ![![646, 163, 128, 182, 240], ![-1610, -43, -231, -220, 0]], ![![807, 205, 161, 228, 300], ![-2011, -57, -291, -275, 0]], ![![510, 128, 102, 145, 191], ![-1270, -32, -185, -175, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-8, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 4, 1, 0, 0], ![-4, 1, 4, 2, 0], ![-11, -1, 2, 7, 12], ![1, 0, 0, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![3, -1, 2, -1, 12], ![0, 0, 0, -2, -7]]]
  hmulB := by decide  
  f := ![![![14579, -45687, 173495, -86924, 360], ![112282, 10943, 1346857, -930, 0]], ![![14551, -45611, 173219, -86786, 360], ![112066, 10943, 1344718, -930, 0]], ![![14467, -45326, 172118, -86234, 360], ![111418, 10851, 1336162, -930, 0]], ![![7, -19, 85, -43, 0], ![54, 33, 667, 0, 0]], ![![6113, -19159, 72756, -36452, 151], ![47080, 4588, 564811, -390, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-27, 31, 0, 0, 0], ![-15, 0, 31, 0, 0], ![-1, 0, 0, 31, 0], ![-13, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-5, -1, 2, -1, 12], ![3, 0, 0, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![151, 0, 0, 0, 0], ![-48, 1, 0, 0, 0]] 
 ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]], ![![-48, 1, 0, 0, 0], ![0, -48, 1, 0, 0], ![0, 1, -48, 2, 0], ![3, -1, 2, -45, 12], ![0, 0, 0, -2, -51]]]
  hmulB := by decide  
  f := ![![![-1125302885, 60112449, -2148657559, 89680410, -39000], ![-3539984657, -25485931, -6759829080, 490750, 0]], ![![-810222539, 43281204, -1547042101, 64570256, -28080], ![-2548802989, -18349973, -4867104178, 353340, 0]], ![![-855232418, 45685577, -1632984074, 68157292, -29640], ![-2690395340, -19369373, -5137483721, 372970, 0]], ![![-1080290729, 57707945, -2062711194, 86093191, -37440], ![-3398385143, -24466506, -6489435720, 471120, 0]], ![![-134142006, 7165738, -256131365, 10690380, -4649], ![-421984738, -3038005, -805807440, 58500, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-103, 151, 0, 0, 0], ![-112, 0, 151, 0, 0], ![-145, 0, 0, 151, 0], ![-18, 0, 0, 0, 151]], ![![-1, 1, 0, 0, 0], ![32, -48, 1, 0, 0], ![33, 1, -48, 2, 0], ![41, -1, 2, -45, 12], ![8, 0, 0, -2, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 151 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-16, 18, -2, 2, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-7, 18, -2, 2, -3]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-11, 18, -2, 2, -3]
 hxeq :=  rfl
 m := 5
 C := ![-16, 18, -2, 2, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-1, 3, 5, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-9, 3, 5, 2, 8]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![5, 3, 5, 2, 8]
 hxeq :=  rfl
 m := 6
 C := ![-1, 3, 5, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-8, 1, -1, -1, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, 1, -1, -1, -4]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, -1, -1, -4]
 hxeq :=  rfl
 m := 8
 C := ![-8, 1, -1, -1, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] ![-15, 18, -2, 2, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-14, 18, -2, 2, -3]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-11, 18, -2, 2, -3]
 hxeq :=  rfl
 m := 4
 C := ![-15, 18, -2, 2, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 18
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] ![-17, 3, 5, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-9, 3, 5, 2, 8]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![5, 3, 5, 2, 8]
 hxeq :=  rfl
 m := 22
 C := ![-17, 3, 5, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] ![-10, 1, -1, -1, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, 1, -1, -1, -4]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, -1, -1, -4]
 hxeq :=  rfl
 m := 10
 C := ![-10, 1, -1, -1, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] ![-97, 18, -2, 2, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-13, 18, -2, 2, -3]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-11, 18, -2, 2, -3]
 hxeq :=  rfl
 m := 86
 C := ![-97, 18, -2, 2, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 78
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] ![-56, 3, 5, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-9, 3, 5, 2, 8]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![5, 3, 5, 2, 8]
 hxeq :=  rfl
 m := 61
 C := ![-56, 3, 5, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 119
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] ![-75, 1, -1, -1, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, 1, -1, -1, -4]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, -1, -1, -4]
 hxeq :=  rfl
 m := 75
 C := ![-75, 1, -1, -1, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

end Sat5
