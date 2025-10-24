import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF6.RI6

open BigOperators Classical Matrix Polynomial

noncomputable section
instance hq151 : Fact $ Nat.Prime 151 := by decide
instance hq11 : Fact $ Nat.Prime 11 := by decide
instance hq31 : Fact $ Nat.Prime 31 := by decide

def R151 : IsOrderOf (6 : ZMod 151) 150 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 2]
 hP := by decide
 hm := by rfl
 hid := by
  suffices h : ((6 : ZMod 151) ^ 15) ^ 10 = 1 by
    rw [← pow_mul] at h
    convert h
  decide
 hnid := by decide

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0], ![-48, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 1, 4, 2, 0], ![3, -1, 2, 7, 12], ![0, 0, 0, -2, 1]]]
  hmulB := by decide
  f := ![![![1130, 286, 225, 319, 420], ![-2816, -77, -407, -385, 0]], ![![485, 123, 97, 137, 180], ![-1209, -33, -176, -165, 0]], ![![646, 163, 128, 182, 240], ![-1610, -43, -231, -220, 0]], ![![807, 205, 161, 228, 300], ![-2011, -57, -291, -275, 0]], ![![510, 128, 102, 145, 191], ![-1270, -32, -185, -175, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-8, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 4, 1, 0, 0], ![-4, 1, 4, 2, 0], ![-11, -1, 2, 7, 12], ![1, 0, 0, -2, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 11 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![3, -1, 2, -1, 12], ![0, 0, 0, -2, -7]]]
  hmulB := by decide
  f := ![![![14579, -45687, 173495, -86924, 360], ![112282, 10943, 1346857, -930, 0]], ![![14551, -45611, 173219, -86786, 360], ![112066, 10943, 1344718, -930, 0]], ![![14467, -45326, 172118, -86234, 360], ![111418, 10851, 1336162, -930, 0]], ![![7, -19, 85, -43, 0], ![54, 33, 667, 0, 0]], ![![6113, -19159, 72756, -36452, 151], ![47080, 4588, 564811, -390, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-27, 31, 0, 0, 0], ![-15, 0, 31, 0, 0], ![-1, 0, 0, 31, 0], ![-13, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-5, -1, 2, -1, 12], ![3, 0, 0, -2, -7]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 31 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![151, 0, 0, 0, 0], ![-48, 1, 0, 0, 0]]
 ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]], ![![-48, 1, 0, 0, 0], ![0, -48, 1, 0, 0], ![0, 1, -48, 2, 0], ![3, -1, 2, -45, 12], ![0, 0, 0, -2, -51]]]
  hmulB := by decide
  f := ![![![-1125302885, 60112449, -2148657559, 89680410, -39000], ![-3539984657, -25485931, -6759829080, 490750, 0]], ![![-810222539, 43281204, -1547042101, 64570256, -28080], ![-2548802989, -18349973, -4867104178, 353340, 0]], ![![-855232418, 45685577, -1632984074, 68157292, -29640], ![-2690395340, -19369373, -5137483721, 372970, 0]], ![![-1080290729, 57707945, -2062711194, 86093191, -37440], ![-3398385143, -24466506, -6489435720, 471120, 0]], ![![-134142006, 7165738, -256131365, 10690380, -4649], ![-421984738, -3038005, -805807440, 58500, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-103, 151, 0, 0, 0], ![-112, 0, 151, 0, 0], ![-145, 0, 0, 151, 0], ![-18, 0, 0, 0, 151]], ![![-1, 1, 0, 0, 0], ![32, -48, 1, 0, 0], ![33, 1, -48, 2, 0], ![41, -1, 2, -45, 12], ![8, 0, 0, -2, -51]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 151 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![-11, 18, -2, 2, -3]

def zeta2 := B.equivFun.symm ![5, 3, 5, 2, 8]

def alpha := B.equivFun.symm ![0, 1, -1, -1, -4]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-16, 18, -2, 2, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-7, 18, -2, 2, -3]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-11, 18, -2, 2, -3]
 hxeq :=  rfl
 m:= 5
 C := ![-16, 18, -2, 2, -3]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-1, 3, 5, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-9, 3, 5, 2, 8]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 3, 5, 2, 8]
 hxeq :=  rfl
 m:= 6
 C := ![-1, 3, 5, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  9
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-8, 1, -1, -1, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![2, 1, -1, -1, -4]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, -1, -1, -4]
 hxeq :=  rfl
 m:= 8
 C := ![-8, 1, -1, -1, -4]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] ![-15, 18, -2, 2, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-14, 18, -2, 2, -3]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-11, 18, -2, 2, -3]
 hxeq :=  rfl
 m:= 4
 C := ![-15, 18, -2, 2, -3]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  18
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] ![-17, 3, 5, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-9, 3, 5, 2, 8]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 3, 5, 2, 8]
 hxeq :=  rfl
 m:= 22
 C := ![-17, 3, 5, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  17
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] ![-10, 1, -1, -1, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![1, 1, -1, -1, -4]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, -1, -1, -4]
 hxeq :=  rfl
 m:= 10
 C := ![-10, 1, -1, -1, -4]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  14
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] ![-97, 18, -2, 2, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-13, 18, -2, 2, -3]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-11, 18, -2, 2, -3]
 hxeq :=  rfl
 m:= 86
 C := ![-97, 18, -2, 2, -3]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  78
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] ![-56, 3, 5, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-9, 3, 5, 2, 8]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 3, 5, 2, 8]
 hxeq :=  rfl
 m:= 61
 C := ![-56, 3, 5, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  119
 hpow := by
  show (6 : ZMod 151) ^ 119 = 61
  suffices h : ((6 : ZMod 151) ^ 7) ^ 17 = 61 by
    rw [← pow_mul] at h
    convert h
  decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![151, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] ![-75, 1, -1, -1, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![1, 1, -1, -1, -4]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R151) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![0, 1, -1, -1, -4]
 hxeq :=  rfl
 m:= 75
 C := ![-75, 1, -1, -1, -4]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  5
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![4, 0, -4, -2, -6], ![10, 7, -3, -1, -6]]]
 hmul := by decide
 f :=  ![![![![-66232, 10472, -17929, -13613, -36906], ![13872, -31416, -5749, 3412, 0]], ![![0, 0, 0, 0, 0], ![-1425, -175, 21, -1, 0]]], ![![![-209684, 33154, -56766, -43101, -116851], ![43914, -99462, -18202, 10803, 0]], ![![0, 0, 0, 0, 0], ![-4512, -554, 66, -3, 0]]]]
 g :=  ![![![![36, -30, 8, -3, 20], ![-2, 16, -4, 0, 0]], ![![32, -32, 8, -3, 21], ![0, 16, -4, 0, 0]]], ![![![32, -32, 8, -3, 21], ![0, 16, -4, 0, 0]], ![![32, -34, 9, -4, 21], ![3, 19, -3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![8, 4, -4, -2, -8], ![8, 8, -12, -5, -20]]]
 hmul := by decide
 f :=  ![![![![114, -28, 147, -63, -13], ![26, 84, -60, 116, 0]], ![![0, 0, 0, 0, 0], ![-20, 16, -4, 0, 0]]], ![![![-718, 119, -255, -101, -352], ![123, -357, -17, -28, 0]], ![![0, 0, 0, 0, 0], ![7, -5, 3, 0, 0]]]]
 g :=  ![![![![20, -124, -95, -68, -96], ![44, 96, 4, 0, 0]], ![![-253, 1408, 1115, 795, 1131], ![-493, -1119, -45, 3, 0]]], ![![![-488, 2759, 2173, 1551, 2200], ![-968, -2184, -88, 6, 0]], ![![-1294, 7334, 5772, 4120, 5845], ![-2574, -5802, -234, 15, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![4, 7, -3, -1, -6]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![8, 0, -8, -4, -12]], ![![8, 14, -6, -2, -12], ![-4, 15, -23, -9, -36]]]
 hmul := by decide
 f :=  ![![![![-42537978769, 9340402926, -13771349688, -7546020842, -22188968907], ![8289834707, -21794273494, -1138509278, 400316779, 0]], ![![-174527976, -28197456, 1028736, 0, 0], ![-94043, 3397, 1131, -49, 0]]], ![![![-54752732986, 12022493832, -17725784207, -9712856047, -28560517565], ![10670255602, -28052485608, -1465431512, 515267496, 0]], ![![-224643576, -36294336, 1324136, 0, 0], ![-121048, 4372, 1456, -63, 0]]]]
 g :=  ![![![![-484, 834, 24, 303, 108], ![-252, -1104, -120, 0, 0]], ![![-452, 780, 20, 282, 97], ![-236, -1032, -112, 0, 0]]], ![![![350, -618, -20, -227, -87], ![198, 822, 94, 0, 0]], ![![1181, -2070, -62, -753, -273], ![645, 2739, 303, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![0, 1, -1, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![8, 0, -8, -4, -12]], ![![8, 4, -4, -2, -8], ![8, 8, -12, -5, -20]]]
 hmul := by decide
 f :=  ![![![![-606792, 133416, -197518, -106843, -315632], ![117600, -311304, -15085, 4897, 0]], ![![-2429, -2445, 105, 0, 0], ![119, -3, 1, 0, 0]]]]
 g :=  ![![![![-8, -17, -13, -8, -17]], ![![37, 17, 31, 15, 40]]], ![![![0, -10, -10, -6, -14]], ![![30, 14, 14, 7, 16]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![1, 2, 0, -6, -9])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![27, -105, 67, 16, 104])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide
