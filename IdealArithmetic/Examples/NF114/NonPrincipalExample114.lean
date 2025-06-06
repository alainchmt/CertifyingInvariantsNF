import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF114.RI114

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr 

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O

noncomputable section
instance hq11 : Fact $ Nat.Prime 11 := by decide
instance hq3 : Fact $ Nat.Prime 3 := by decide
instance hq7 : Fact $ Nat.Prime 7 := by decide

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 2, 0], ![-38, -14, -9, -28, 83], ![-12, -5, -1, -8, 27]]]
  hmulB := by decide
  f := ![![![39, 24, -43, -84, -83], ![-30, -12, 168, 3, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![26, 16, -29, -56, -55], ![-20, -7, 112, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 2, 0], ![-68, -14, -9, -28, 83], ![-22, -5, -1, -8, 27]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 2, 2, 0], ![-38, -14, -9, -27, 83], ![-12, -5, -1, -8, 28]]]
  hmulB := by decide
  f := ![![![111, -15, -98, 21, -83], ![-504, 707, 21, 7, 0]], ![![108, -14, -95, 21, -83], ![-489, 686, 21, 7, 0]], ![![111, -13, -96, 21, -83], ![-505, 694, 21, 7, 0]], ![![0, -2, -3, -1, 0], ![1, 13, 4, 0, 0]], ![![96, -12, -84, 18, -71], ![-438, 606, 18, 6, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-1, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 0, 2, 2, 0], ![-63, -14, -9, -27, 83], ![-23, -5, -1, -8, 28]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-38, -14, -9, -31, 83], ![-12, -5, -1, -8, 24]]]
  hmulB := by decide
  f := ![![![19609, -19408, 4911, 113, -1245], ![44422, -30968, 1232, 105, 0]], ![![13068, -12930, 3271, 76, -830], ![29604, -20629, 819, 70, 0]], ![![19595, -19394, 4906, 115, -1245], ![44390, -30946, 1225, 105, 0]], ![![13075, -12938, 3274, 75, -830], ![29620, -20642, 823, 70, 0]], ![![16809, -16635, 4208, 98, -1067], ![38079, -26542, 1052, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-5, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![1, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-40, -14, -9, -31, 83], ![-13, -5, -1, -8, 24]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![5, 1, 0, 0, 0], ![0, 5, 1, 0, 0], ![0, 0, 6, 2, 0], ![-38, -14, -9, -23, 83], ![-12, -5, -1, -8, 32]]]
  hmulB := by decide
  f := ![![![10966, 774, 68856, 23353, -1245], ![-22869, 3333, -126544, 165, 0]], ![![6572, 462, 41311, 14011, -747], ![-13705, 2002, -75922, 99, 0]], ![![8764, 614, 55077, 18680, -996], ![-18276, 2674, -101222, 132, 0]], ![![8770, 617, 55086, 18683, -996], ![-18289, 2670, -101238, 132, 0]], ![![5976, 417, 37557, 12738, -679], ![-12462, 1827, -69024, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-9, 0, 0, 11, 0], ![-6, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-3, 5, 1, 0, 0], ![-6, 0, 6, 2, 0], ![-17, -14, -9, -23, 83], ![-9, -5, -1, -8, 32]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)

def A4: IdealEqSpanCertificate O ℤ timesTableO I4
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 2, 2, 0], ![-38, -14, -9, -27, 83], ![-12, -5, -1, -8, 28]]]
  hmulB := by decide
  f := ![![![0, -4, -5, -2, 0], ![3, 9, 3, 0, 0]], ![![0, -2, -2, 0, 0], ![1, 6, 0, 0, 0]], ![![0, -2, -3, -2, 0], ![2, 4, 3, 0, 0]], ![![0, -1, 2, 3, 0], ![1, 2, -4, 0, 0]], ![![-33, 1, 27, -5, 28], ![61, -78, -6, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 0, 2, 2, 0], ![7, -14, -9, -27, 83], ![1, -5, -1, -8, 28]]]
  hle1 := by decide
  hle2 := by decide

lemma N4 : Nat.card (O ⧸ I4) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A4)

def zeta1 := B.equivFun.symm ![4629, -546, 3982, 3216, -8528]

def zeta2 := B.equivFun.symm ![24437, -3151, 21323, 16824, -44838]

def zeta3 := B.equivFun.symm ![-474917, -10979, -332883, -369502, 919008]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def alpha := B.equivFun.symm ![-7, 3, -8, -5, 11]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![4628, -546, 3982, 3216, -8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![7228, -546, 3982, 3216, -8528]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4629, -546, 3982, 3216, -8528]
 hxeq :=  rfl
 m:= 1
 C := ![4628, -546, 3982, 3216, -8528]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![38037, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m:= 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-474918, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-770978, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m:= 1
 C := ![-474918, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log03Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log04Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-8, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-10, 3, -8, -5, 11]
 hmem := by decide

def Log04: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m:= 1
 C := ![-8, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log04Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![4626, -546, 3982, 3216, -8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![4176, -546, 3982, 3216, -8528]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4629, -546, 3982, 3216, -8528]
 hxeq :=  rfl
 m:= 3
 C := ![4626, -546, 3982, 3216, -8528]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![24434, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![21693, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m:= 3
 C := ![24434, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-474919, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-515884, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m:= 2
 C := ![-474919, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log13Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log14Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-12, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-4, 3, -8, -5, 11]
 hmem := by decide

def Log14: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m:= 5
 C := ![-12, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log14Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![4625, -546, 3982, 3216, -8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![3141, -546, 3982, 3216, -8528]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4629, -546, 3982, 3216, -8528]
 hxeq :=  rfl
 m:= 4
 C := ![4625, -546, 3982, 3216, -8528]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![16476, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m:= 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-474923, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-347590, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m:= 6
 C := ![-474923, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log23Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log24Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-8, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-3, 3, -8, -5, 11]
 hmem := by decide

def Log24: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m:= 1
 C := ![-8, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log24Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![4625, -546, 3982, 3216, -8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-207, -546, 3982, 3216, -8528]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4629, -546, 3982, 3216, -8528]
 hxeq :=  rfl
 m:= 4
 C := ![4625, -546, 3982, 3216, -8528]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1162, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m:= 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-474924, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![4955, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m:= 7
 C := ![-474924, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 10
 C := ![-11, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log34Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-17, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![1, 3, -8, -5, 11]
 hmem := by decide

def Log34: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m:= 10
 C := ![-17, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log34Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log40Mem : IdealMemCertificate O ℤ B I4
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![4628, -546, 3982, 3216, -8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![-2002, -546, 3982, 3216, -8528]
 hmem := by decide

def Log40: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4629, -546, 3982, 3216, -8528]
 hxeq :=  rfl
 m:= 1
 C := ![4628, -546, 3982, 3216, -8528]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log40Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log41Mem : IdealMemCertificate O ℤ B I4
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![-10628, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log41: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m:= 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log41Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log42Mem : IdealMemCertificate O ℤ B I4
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-474918, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![190443, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log42: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m:= 1
 C := ![-474918, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log42Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log43Mem : IdealMemCertificate O ℤ B I4
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log43: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log43Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log44Mem : IdealMemCertificate O ℤ B I4
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-9, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![3, 3, -8, -5, 11]
 hmem := by decide

def Log44: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m:= 2
 C := ![-9, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log44Mem
 k :=  1
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![2, 0, 0, 0, 0], ![1, 19, 8, 5, -15]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-10, 20, 10, 6, -18]], ![![-10, 20, 10, 6, -18], ![27, -131, -44, -25, 79]]]
 hmul := by decide
 f :=  ![![![![11070755965, -1863144039, 2599910895, 1766567840, -6375571612], ![847091162, 2541233556, 0, 164497545, 2654544]], ![![0, 0, 0, 0, 0], ![-10616, -21137, 0, -169, 9]]], ![![![98338543214, -16549807848, 23094308449, 15691946328, -56632486526], ![7524482738, 22573092645, 0, 1461187578, 23579535]], ![![0, 0, 0, 0, 0], ![-94305, -187702, 0, -1500, 78]]]]
 g :=  ![![![![1998, -1798, 384, 704, -1706], ![80, 352, 0, 4, 0]], ![![-14928, 13408, -2884, -5272, 12781], ![-594, -2630, 0, -30, 0]]], ![![![-14928, 13408, -2884, -5272, 12781], ![-594, -2630, 0, -30, 0]], ![![78649, -70698, 15188, 27775, -67330], ![3133, 13860, 0, 158, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![1, 19, 8, 5, -15]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![4, 0, 0, 0, 0], ![-1, 19, 8, 5, -15]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-10, 20, 10, 6, -18]], ![![2, 38, 16, 10, -30], ![-17, -127, -36, -19, 63]]]
 hmul := by decide
 f :=  ![![![![-52211320624, 8790524624, -12262221724, -8331519339, 30071878060], ![-3995359804, -11983379928, 0, -776350932, -12452760]], ![![0, 0, 0, 0, 0], ![64428, 1808, 0, 4, 0]]], ![![![260820732216, -43912910900, 61255712531, 41619958038, -150223536913], ![19958749509, 59862763284, 0, 3878247399, 62207544]], ![![0, 0, 0, 0, 0], ![-321849, -9032, 0, -20, 0]]]]
 g :=  ![![![![992746, -682890, 172372, 315783, -750414], ![61764, 388908, -612, 4, 0]], ![![1565336024, -1076739117, 271803284, 497926425, -1183256726], ![97382608, 613220673, -965032, 6291, 147]]], ![![![2815649559, -1936785427, 488906400, 895645598, -2128384085], ![175167050, 1103031228, -1735852, 11316, 264]], ![![-8253849640, 5677530265, -1433189700, -2625512856, 6239186343], ![-513488075, -3233447100, 5088510, -33172, -774]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![-1, 19, 8, 5, -15]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![-7, 3, -8, -5, 11]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![-20, 40, 20, 12, -36]], ![![-2, 38, 16, 10, -30], ![-7, -147, -46, -25, 81]]]
 hmul := by decide
 f :=  ![![![![-83885993269078362335, 10710548320910940657, -19384884201272469769, -13570012036853136783, 44600570738640597389], ![-6252072105092958724, -21153203617853426602, 0, -596972155002971048, -4084982552383467]], ![![-62671820339602, 5955512551941, 0, 22587826974, 0], ![-106325555, -4497412, 0, -10426, -112]]]]
 g :=  ![![![![60, -54, 36, 50, -118]], ![![274, 83, 141, 148, -378]]], ![![![-196, -65, -195, -204, 518]], ![![-663, 438, -212, -330, 764]]]]
 hle1 := by decide
 hle2 := by decide

lemma J4 : J ^ 4 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![90797, 55698, -15334, 45000, -215896])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1279203, -35191, -888351, -992590, 2479592])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![35218795, 35595917, 8752395, 4943356, -16282674])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_v : IsUnit v := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1, 0, 0, 0, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table T B _ _ timesTableT_eq_Table _ (by norm_num)
  decide
