import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF30.RI30

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
instance hq31 : Fact $ Nat.Prime 31 := by decide
instance hq13 : Fact $ Nat.Prime 13 := by decide
instance hq7 : Fact $ Nat.Prime 7 := by decide

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![1, 1, 0, 0, 2], ![6, 15, 12, 9, -2]]]
  hmulB := by decide
  f := ![![![56, -7, 0, 0, 48], ![217, 0, 0, -168, 0]], ![![56, -7, 0, 0, 48], ![218, 0, 0, -168, 0]], ![![46, -5, 0, 0, 40], ![176, 1, 0, -140, 0]], ![![0, 0, 0, -1, 0], ![0, 4, 4, 0, 0]], ![![8, -1, 0, 0, 7], ![31, 0, 0, -24, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-1, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![-1, 1, 0, 0, 2], ![-22, 15, 12, 9, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![1, 1, 0, 1, 2], ![6, 15, 12, 9, -1]]]
  hmulB := by decide
  f := ![![![0, 5, 0, 13, -2], ![13, 0, -91, 13, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![6, 0, 7, 0, 0]], ![![0, 3, 0, 7, -1], ![3, 0, -49, 7, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![-7, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![-1, 1, 0, 1, 2], ![1, 15, 12, 9, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![31, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-10, 1, 0, 0, 0], ![0, -10, 1, 0, 0], ![0, 1, -10, 2, 0], ![1, 1, 0, -9, 2], ![6, 15, 12, 9, -11]]]
  hmulB := by decide
  f := ![![![-24453, 5666, -39290, 7998, -28], ![-75764, -2170, -122016, 434, 0]], ![![-24983, 5783, -40128, 8166, -28], ![-77406, -2232, -124620, 434, 0]], ![![-24830, 5754, -39889, 8118, -28], ![-76932, -2200, -123876, 434, 0]], ![![71, -14, 85, -17, 0], ![220, 5, 264, 0, 0]], ![![-7890, 1836, -12675, 2580, -9], ![-24446, -675, -39360, 140, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-21, 31, 0, 0, 0], ![-24, 0, 31, 0, 0], ![-1, 0, 0, 31, 0], ![-10, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![6, -10, 1, 0, 0], ![7, 1, -10, 2, 0], ![-1, 1, 0, -9, 2], ![-16, 15, 12, 9, -11]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![5, 22, 16, 12, -8]

def zeta2 := B.equivFun.symm ![15916, -121319, -63617, -104665, 61214]

def alpha := B.equivFun.symm ![-2, -1, 0, 0, 0]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![3, 22, 16, 12, -8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-31, 22, 16, 12, -8]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 22, 16, 12, -8]
 hxeq :=  rfl
 m:= 2
 C := ![3, 22, 16, 12, -8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![15913, -121319, -63617, -104665, 61214] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![152045, -121319, -63617, -104665, 61214]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![15916, -121319, -63617, -104665, 61214]
 hxeq :=  rfl
 m:= 3
 C := ![15913, -121319, -63617, -104665, 61214]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-6, -1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![0, -1, 0, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, -1, 0, 0, 0]
 hxeq :=  rfl
 m:= 4
 C := ![-6, -1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-4, 22, 16, 12, -8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![4, 22, 16, 12, -8]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 22, 16, 12, -8]
 hxeq :=  rfl
 m:= 9
 C := ![-4, 22, 16, 12, -8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![15904, -121319, -63617, -104665, 61214] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-31738, -121319, -63617, -104665, 61214]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![15916, -121319, -63617, -104665, 61214]
 hxeq :=  rfl
 m:= 12
 C := ![15904, -121319, -63617, -104665, 61214]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  6
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-13, -1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, -1, 0, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, -1, 0, 0, 0]
 hxeq :=  rfl
 m:= 11
 C := ![-13, -1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![3, 22, 16, 12, -8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-25, 22, 16, 12, -8]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![5, 22, 16, 12, -8]
 hxeq :=  rfl
 m:= 2
 C := ![3, 22, 16, 12, -8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  24
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![15886, -121319, -63617, -104665, 61214] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![115578, -121319, -63617, -104665, 61214]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![15916, -121319, -63617, -104665, 61214]
 hxeq :=  rfl
 m:= 30
 C := ![15886, -121319, -63617, -104665, 61214]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  15
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![-21, -1, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![0, -1, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, -1, 0, 0, 0]
 hxeq :=  rfl
 m:= 19
 C := ![-21, -1, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  4
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]], ![![0, 2, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![0, 5142, 3398, 1180, -4565], ![-3856, 1700, 0, 4192, -708]], ![![0, 0, 0, 0, 0], ![-212, -304, 0, 8, 4]]], ![![![0, 2548, 1684, 585, -2263], ![-1909, 844, 0, 2078, -351]], ![![0, 0, 0, 0, 0], ![-106, -151, 0, 4, 2]]]]
 g :=  ![![![![-2, 7, 0, -28, -13], ![4, -16, 32, 28, -4]], ![![-2, 13, 0, -28, -11], ![4, -28, 38, 24, -4]]], ![![![-2, 13, 0, -28, -11], ![4, -28, 38, 24, -4]], ![![1, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![-2, -1, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![0, 4, 0, 0, 0]], ![![4, 2, 0, 0, 0], ![0, 2, 1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![0, 2775962, 1827907, 598422, -2425143], ![-2081971, 913954, 0, 2242257, -380814]], ![![42627, -33228, 0, -16390, 2769], ![-1316, 1035, 0, -28, -2]]]]
 g :=  ![![![![7, 18, 15, 2, -4]], ![![-11, -18, -15, -2, 4]]], ![![![-2, 0, 0, 0, 0]], ![![0, -1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J3 : J ^ 3 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![1437, 818, 4, -92, 8])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![125956, 310429, 219097, 245985, 75296])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

