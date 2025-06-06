import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF60.RI60

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
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, 0, 0, 4], ![60, -2, 6, -4, 0]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, 0, 0, 0, 3], ![2, 0, 0, -2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, 0, 0, 4], ![20, -2, 6, -4, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, 0, 1, 4], ![60, -2, 6, -4, 1]]]
  hmulB := by decide
  f := ![![![0, 0, 3, 0, -8], ![3, -6, -3, 6, 0]], ![![0, 0, 1, -1, -4], ![1, -3, 0, 3, 0]], ![![0, 0, 2, -1, -4], ![2, -5, 0, 3, 0]], ![![0, -1, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![0, 0, 2, 0, -5], ![2, -4, -2, 4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-3, 1, 0, 1, 4], ![16, -2, 6, -4, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, 0, 1, 4], ![60, -2, 6, -4, 1]]]
  hmulB := by decide
  f := ![![![0, 16, 23, 42, -24], ![7, 7, -168, 42, 0]], ![![0, 2, 3, 7, -4], ![1, 7, -28, 7, 0]], ![![0, 13, 19, 35, -20], ![6, 8, -140, 35, 0]], ![![0, -1, -1, -1, 0], ![0, 3, 4, 0, 0]], ![![0, 11, 16, 30, -17], ![5, 8, -120, 30, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-3, 1, 0, 1, 4], ![3, -2, 6, -4, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![0, 1, 0, -4, 4], ![60, -2, 6, -4, -4]]]
  hmulB := by decide
  f := ![![![1045, -1489, 6227, -3080, -80], ![2871, 1023, 17380, 220, 0]], ![![777, -1113, 4651, -2300, -60], ![2135, 759, 12980, 165, 0]], ![![786, -1121, 4690, -2320, -60], ![2160, 771, 13090, 165, 0]], ![![261, -372, 1555, -769, -20], ![717, 255, 4340, 55, 0]], ![![380, -540, 2264, -1120, -29], ![1044, 376, 6320, 80, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-3, 0, 0, 11, 0], ![-4, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-1, 1, 0, -4, 4], ![6, -2, 6, -4, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)

def zeta1 := B.equivFun.symm ![6170728364, -1612948664, 343950842, -311415441, 68113181]

def zeta2 := B.equivFun.symm ![-61616422631, 17026004959, -3671410855, 4004626858, -1814584410]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def alpha := B.equivFun.symm ![286, 96, 56, 14, 16]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![6170728362, -1612948664, 343950842, -311415441, 68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![2056909454, -1612948664, 343950842, -311415441, 68113181]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6170728364, -1612948664, 343950842, -311415441, 68113181]
 hxeq :=  rfl
 m:= 2
 C := ![6170728362, -1612948664, 343950842, -311415441, 68113181]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-61616422632, 17026004959, -3671410855, 4004626858, -1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-20538807544, 17026004959, -3671410855, 4004626858, -1814584410]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-61616422631, 17026004959, -3671410855, 4004626858, -1814584410]
 hxeq :=  rfl
 m:= 1
 C := ![-61616422632, 17026004959, -3671410855, 4004626858, -1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log03Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![285, 96, 56, 14, 16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![95, 96, 56, 14, 16]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![286, 96, 56, 14, 16]
 hxeq :=  rfl
 m:= 1
 C := ![285, 96, 56, 14, 16]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![6170728362, -1612948664, 343950842, -311415441, 68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![2319849660, -1612948664, 343950842, -311415441, 68113181]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6170728364, -1612948664, 343950842, -311415441, 68113181]
 hxeq :=  rfl
 m:= 2
 C := ![6170728362, -1612948664, 343950842, -311415441, 68113181]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-61616422633, 17026004959, -3671410855, 4004626858, -1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-22556812354, 17026004959, -3671410855, 4004626858, -1814584410]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-61616422631, 17026004959, -3671410855, 4004626858, -1814584410]
 hxeq :=  rfl
 m:= 2
 C := ![-61616422633, 17026004959, -3671410855, 4004626858, -1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log13Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![285, 96, 56, 14, 16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![15, 96, 56, 14, 16]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![286, 96, 56, 14, 16]
 hxeq :=  rfl
 m:= 1
 C := ![285, 96, 56, 14, 16]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![6170728360, -1612948664, 343950842, -311415441, 68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![768486581, -1612948664, 343950842, -311415441, 68113181]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6170728364, -1612948664, 343950842, -311415441, 68113181]
 hxeq :=  rfl
 m:= 4
 C := ![6170728360, -1612948664, 343950842, -311415441, 68113181]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-61616422635, 17026004959, -3671410855, 4004626858, -1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-6791577202, 17026004959, -3671410855, 4004626858, -1814584410]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-61616422631, 17026004959, -3671410855, 4004626858, -1814584410]
 hxeq :=  rfl
 m:= 4
 C := ![-61616422635, 17026004959, -3671410855, 4004626858, -1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log23Mem : IdealMemCertificate O ℤ B I2
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![281, 96, 56, 14, 16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-33, 96, 56, 14, 16]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![286, 96, 56, 14, 16]
 hxeq :=  rfl
 m:= 5
 C := ![281, 96, 56, 14, 16]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![6170728362, -1612948664, 343950842, -311415441, 68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![1459950687, -1612948664, 343950842, -311415441, 68113181]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![6170728364, -1612948664, 343950842, -311415441, 68113181]
 hxeq :=  rfl
 m:= 2
 C := ![6170728362, -1612948664, 343950842, -311415441, 68113181]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-61616422634, 17026004959, -3671410855, 4004626858, -1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-14865957741, 17026004959, -3671410855, 4004626858, -1814584410]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-61616422631, 17026004959, -3671410855, 4004626858, -1814584410]
 hxeq :=  rfl
 m:= 3
 C := ![-61616422634, 17026004959, -3671410855, 4004626858, -1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![278, 96, 56, 14, 16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-76, 96, 56, 14, 16]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![286, 96, 56, 14, 16]
 hxeq :=  rfl
 m:= 8
 C := ![278, 96, 56, 14, 16]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  3
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]] ![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]]
  ![![286, 96, 56, 14, 16]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-54, 4, 0, 2, 2]], ![![-54, 4, 0, 2, 2], ![294, -80, 24, -14, 8]]]
 hmul := by decide
 f :=  ![![![![-185, -5852, 2444, -302, 1926], ![-2224, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![-405, 0, 0, 0, 0]]]]
 g :=  ![![![![34, 4, 0, -1, -2]], ![![-39, 22, -4, 3, -3]]], ![![![-39, 22, -4, 3, -3]], ![![9, -60, 12, -5, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma J2 : J ^ 2 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-3604887766, -1194129956, -710017642, -175319719, -205268011])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-24889956371, -8244775729, -4902258385, -1210469778, -1417239710])
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
