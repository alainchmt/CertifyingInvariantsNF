import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.SmallDisc.RISmallDisc

open BigOperators Classical Matrix Polynomial

noncomputable section
instance hq37 : Fact $ Nat.Prime 37 := by decide
instance hq7 : Fact $ Nat.Prime 7 := by decide

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 2, 0, 0], ![0, 1, -3, 2, 0], ![0, 0, -1, -3, 1], ![4, -5, 0, 0, -3]]]
  hmulB := by decide
  f := ![![![124, -80, 200, -126, -6], ![287, 77, 504, 42, 0]], ![![82, -54, 134, -84, -4], ![190, 49, 336, 28, 0]], ![![102, -65, 166, -105, -5], ![236, 67, 420, 35, 0]], ![![6, 0, 0, -1, 0], ![14, 6, 4, 0, 0]], ![![108, -70, 172, -108, -5], ![250, 64, 432, 36, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -3, 2, 0, 0], ![2, 1, -3, 2, 0], ![0, 0, -1, -3, 1], ![6, -5, 0, 0, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 7 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![7, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-2, 1, 0, 0, 0], ![0, -2, 2, 0, 0], ![0, 1, -2, 2, 0], ![0, 0, -1, -2, 1], ![4, -5, 0, 0, -2]]]
  hmulB := by decide
  f := ![![![-91, 200, -382, 336, 30], ![-322, -154, -1386, -210, 0]], ![![-77, 171, -325, 286, 25], ![-272, -126, -1176, -175, 0]], ![![-73, 164, -314, 274, 25], ![-258, -122, -1134, -175, 0]], ![![-74, 168, -321, 281, 25], ![-262, -122, -1158, -175, 0]], ![![-39, 86, -164, 144, 13], ![-138, -65, -594, -90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-6, 0, 0, 7, 0], ![-3, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -2, 2, 0, 0], ![-1, 1, -2, 2, 0], ![2, 0, -1, -2, 1], ![5, -5, 0, 0, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 7 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![1, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 1, 1, 2, 0], ![0, 0, -1, 1, 1], ![4, -5, 0, 0, 1]]]
  hmulB := by decide
  f := ![![![0, -1220, -2403, -1258, 1188], ![37, -148, 45251, -43956, 0]], ![![0, -37, -73, -38, 36], ![1, 0, 1369, -1332, 0]], ![![0, -628, -1238, -646, 612], ![18, -55, 23273, -22644, 0]], ![![0, -296, -583, -305, 288], ![9, -28, 10971, -10656, 0]], ![![0, -297, -585, -306, 289], ![9, -27, 11007, -10692, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 37, 0, 0, 0], ![-18, 0, 37, 0, 0], ![-9, 0, 0, 37, 0], ![-9, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-1, 1, 2, 0, 0], ![-1, 1, 1, 2, 0], ![0, 0, -1, 1, 1], ![0, -5, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 37 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![-5, -1, 0, -1, -1]

def zeta2 := B.equivFun.symm ![1, 0, -1, 2, -1]

def alpha := B.equivFun.symm ![1, -1, 1, 0, 0]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-10, -1, 0, -1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![0, -1, 0, -1, -1]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-5, -1, 0, -1, -1]
 hxeq :=  rfl
 m:= 5
 C := ![-10, -1, 0, -1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-5, 0, -1, 2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![1, 0, -1, 2, -1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![1, 0, -1, 2, -1]
 hxeq :=  rfl
 m:= 6
 C := ![-5, 0, -1, 2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-5, -1, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, -1, 1, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![1, -1, 1, 0, 0]
 hxeq :=  rfl
 m:= 6
 C := ![-5, -1, 1, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![-7, -1, 0, -1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![1, -1, 0, -1, -1]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-5, -1, 0, -1, -1]
 hxeq :=  rfl
 m:= 2
 C := ![-7, -1, 0, -1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![-3, 0, -1, 2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, -1, 2, -1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![1, 0, -1, 2, -1]
 hxeq :=  rfl
 m:= 4
 C := ![-3, 0, -1, 2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![0, -1, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![0, -1, 1, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![1, -1, 1, 0, 0]
 hxeq :=  rfl
 m:= 1
 C := ![0, -1, 1, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-19, -1, 0, -1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![0, -1, 0, -1, -1]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-5, -1, 0, -1, -1]
 hxeq :=  rfl
 m:= 14
 C := ![-19, -1, 0, -1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  33
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-9, 0, -1, 2, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![0, 0, -1, 2, -1]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![1, 0, -1, 2, -1]
 hxeq :=  rfl
 m:= 10
 C := ![-9, 0, -1, 2, -1]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  24
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-20, -1, 1, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-1, -1, 1, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![1, -1, 1, 0, 0]
 hxeq :=  rfl
 m:= 21
 C := ![-20, -1, 1, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  22
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![2, 2, 0, 2, 0]], ![![2, 2, 0, 2, 0], ![1, 3, -2, 2, 1]]]
 hmul := by decide
 f :=  ![![![![476, -137, 153, 340, 92], ![-186, -184, -383, -75, 0]], ![![0, 0, 0, 0, 0], ![-18, 7, -2, 0, 0]]], ![![![3710, -1065, 1191, 2652, 718], ![-1454, -1432, -2983, -585, 0]], ![![0, 0, 0, 0, 0], ![-145, 53, -15, 1, 0]]]]
 g :=  ![![![![3, 0, 1, 0, 0], ![-2, 0, 0, 0, 0]], ![![-1, 4, -1, 1, -1], ![0, 0, 2, 2, 0]]], ![![![-1, 4, -1, 1, -1], ![0, 0, 2, 2, 0]], ![![-2, 6, -2, 1, -1], ![-1, 0, 3, 3, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![1, 0, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 1, 0]]
  ![![1, -1, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![2, 2, 0, 2, 0]], ![![2, 0, 2, 0, 0], ![3, -1, 1, 2, 0]]]
 hmul := by decide
 f :=  ![![![![144, -42, 44, 98, 28], ![-58, -55, -106, -27, 0]], ![![0, 0, 0, 0, 0], ![-9, 0, -2, 0, 0]]]]
 g :=  ![![![![8, 0, 0, 2, 2]], ![![6, 0, -1, 0, 1]]], ![![![6, -1, -1, 0, 1]], ![![3, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J3 : J ^ 3 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1, 1, 1, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![17, 2, 1, 2, 3])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide
