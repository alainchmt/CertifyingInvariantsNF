import IdealArithmetic.Examples.NF5_1_10125000000_1.ClassGroupData5_1_10125000000_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_10125000000_1.RI5_1_10125000000_1

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 0, 5, 6, 0], ![-18, 7, 4, -10, 72], ![9, -2, 0, -3, 11]]]
  hmulB := by decide  
  f := ![![![-675, -62, -5751, -7098, 432], ![1988, -630, 8211, -42, 0]], ![![-678, -61, -5795, -7152, 432], ![1996, -637, 8274, -42, 0]], ![![-679, -62, -5795, -7152, 432], ![2000, -636, 8274, -42, 0]], ![![-1, -2, 10, 13, 0], ![4, 5, -15, 0, 0]], ![![-384, -34, -3286, -4056, 247], ![1130, -362, 4692, -24, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 7, 0, 0, 0], ![-3, 0, 7, 0, 0], ![-1, 0, 0, 7, 0], ![-4, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-3, 0, 5, 6, 0], ![-46, 7, 4, -10, 72], ![-4, -2, 0, -3, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 0, 1, 6, 0], ![-18, 7, 4, -14, 72], ![9, -2, 0, -3, 7]]]
  hmulB := by decide  
  f := ![![![13703, -6813, 6265, 38760, -2376], ![124526, -266, -121277, 627, 0]], ![![12455, -6191, 5695, 35238, -2160], ![113184, -228, -110257, 570, 0]], ![![11211, -5573, 5125, 31710, -1944], ![101880, -208, -99218, 513, 0]], ![![4985, -2478, 2278, 14095, -864], ![45302, -92, -44102, 228, 0]], ![![725, -359, 329, 2040, -125], ![6590, 0, -6383, 33, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-17, 19, 0, 0, 0], ![-15, 0, 19, 0, 0], ![-7, 0, 0, 19, 0], ![-1, 0, 0, 0, 19]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-3, 0, 1, 6, 0], ![-9, 7, 4, -14, 72], ![3, -2, 0, -3, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 0, 1, 6, 0], ![-18, 7, 4, -14, 72], ![9, -2, 0, -3, 7]]]
  hmulB := by decide  
  f := ![![![1961, -982, 706, 4550, -720], ![6230, -77, -5145, 70, 0]], ![![1571, -787, 565, 3640, -576], ![4992, -63, -4116, 56, 0]], ![![1177, -588, 422, 2724, -432], ![3740, -41, -3080, 42, 0]], ![![785, -392, 282, 1821, -288], ![2494, -27, -2059, 28, 0]], ![![1682, -842, 605, 3900, -617], ![5344, -65, -4410, 60, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 7, 0, 0, 0], ![-3, 0, 7, 0, 0], ![-3, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-3, 0, 1, 6, 0], ![-65, 7, 4, -14, 72], ![-2, -2, 0, -3, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-2288805750138074, 620125621715449, 93403693655176, 22466222402355, 682300270585169] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-937276482753933, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2288805750138070, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hxeq :=  rfl
 m := 4
 C := ![-2288805750138074, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-54324600083209633796, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![4133287722028053918, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-54324600083209633790, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hxeq :=  rfl
 m := 6
 C := ![-54324600083209633796, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![10068117025306292741202, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-766036442054232916799, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10068117025306292741207, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hxeq :=  rfl
 m := 5
 C := ![10068117025306292741202, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-2288805750138078, 620125621715449, 93403693655176, 22466222402355, 682300270585169] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-793240029027895, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2288805750138070, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hxeq :=  rfl
 m := 8
 C := ![-2288805750138078, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-54324600083209633793, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![5434186294059764886, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-54324600083209633790, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hxeq :=  rfl
 m := 3
 C := ![-54324600083209633793, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![10068117025306292741206, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1007131950276855411004, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10068117025306292741207, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hxeq :=  rfl
 m := 1
 C := ![10068117025306292741206, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-2288805750138075, 620125621715449, 93403693655176, 22466222402355, 682300270585169] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1404406461485561, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2288805750138070, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hxeq :=  rfl
 m := 5
 C := ![-2288805750138075, 620125621715449, 93403693655176, 22466222402355, 682300270585169]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-54324600083209633796, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![10269954128612000128, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-54324600083209633790, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hxeq :=  rfl
 m := 6
 C := ![-54324600083209633796, -4967282771824132614, -4453797873765804231, 1284007303743294015, -15311415569050906829]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![10068117025306292741202, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1903361838166782983186, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10068117025306292741207, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hxeq :=  rfl
 m := 5
 C := ![10068117025306292741202, 920598809183421036433, 825434632072257476354, -237969304875711315349, 2837709977494504993054]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

end Sat3
