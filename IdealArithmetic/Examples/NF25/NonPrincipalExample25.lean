import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF25.RI25

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
instance hq31 : Fact $ Nat.Prime 31 := by decide

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![1, 1, 0, 0, 0], ![0, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 2, 5, 8], ![4, 1, 3, -3, -3]]]
  hmulB := by decide
  f := ![![![144, 63, 40, 0, 160], ![-693, 0, 1100, -220, 0]], ![![14, 6, 4, 0, 16], ![-65, 0, 110, -22, 0]], ![![130, 58, 37, 0, 144], ![-628, -5, 990, -198, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]], ![![118, 51, 32, 0, 131], ![-569, 4, 900, -180, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 11, 0, 0, 0], ![-10, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![-8, 0, 2, 5, 8], ![0, 1, 3, -3, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![6, 1, 0, 0, 0], ![0, 7, 2, 0, 0], ![0, 0, 5, 1, 0], ![4, 0, 2, 10, 8], ![4, 1, 3, -3, 2]]]
  hmulB := by decide
  f := ![![![65, -20, 405, 121, 32], ![-88, 44, -891, -44, 0]], ![![58, -21, 405, 121, 32], ![-76, 44, -891, -44, 0]], ![![31, -7, 181, 56, 16], ![-42, 17, -396, -22, 0]], ![![26, -13, 204, 61, 16], ![-32, 25, -450, -22, 0]], ![![-5, -10, 35, 11, 3], ![12, 14, -81, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-1, 0, 11, 0, 0], ![-6, 0, 0, 11, 0], ![-1, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-4, 7, 2, 0, 0], ![-1, 0, 5, 1, 0], ![-6, 0, 2, 10, 8], ![1, 1, 3, -3, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![3, 1, 0, 0, 0], ![0, 4, 2, 0, 0], ![0, 0, 2, 1, 0], ![4, 0, 2, 7, 8], ![4, 1, 3, -3, -1]]]
  hmulB := by decide
  f := ![![![6282, 1971, 15144, 7750, 208], ![-63829, 682, -234608, -806, 0]], ![![958, 298, 2336, 1196, 32], ![-9733, 124, -36208, -124, 0]], ![![5312, 1663, 12805, 6554, 176], ![-53973, 605, -198400, -682, 0]], ![![2416, 756, 5824, 2981, 80], ![-24548, 278, -90240, -310, 0]], ![![1416, 441, 3418, 1750, 47], ![-14387, 179, -52976, -182, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 31, 0, 0, 0], ![-25, 0, 31, 0, 0], ![-12, 0, 0, 31, 0], ![-7, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-2, 4, 2, 0, 0], ![-2, 0, 2, 1, 0], ![-6, 0, 2, 7, 8], ![-1, 1, 3, -3, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![-15, -12, 5, 5, 8]

def zeta2 := B.equivFun.symm ![26991, 99902, -36483, -33365, -61972]

def alpha := B.equivFun.symm ![658, 471, 553, 230, 264]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-22, -12, 5, 5, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-12, -12, 5, 5, 8]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-15, -12, 5, 5, 8]
 hxeq :=  rfl
 m:= 7
 C := ![-22, -12, 5, 5, 8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![26986, 99902, -36483, -33365, -61972] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![77242, 99902, -36483, -33365, -61972]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![26991, 99902, -36483, -33365, -61972]
 hxeq :=  rfl
 m:= 5
 C := ![26986, 99902, -36483, -33365, -61972]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![655, 471, 553, 230, 264] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-702, 471, 553, 230, 264]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![658, 471, 553, 230, 264]
 hxeq :=  rfl
 m:= 3
 C := ![655, 471, 553, 230, 264]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-18, -12, 5, 5, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![1, -12, 5, 5, 8]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-15, -12, 5, 5, 8]
 hxeq :=  rfl
 m:= 3
 C := ![-18, -12, 5, 5, 8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![26988, 99902, -36483, -33365, -61972] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-24889, 99902, -36483, -33365, -61972]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![26991, 99902, -36483, -33365, -61972]
 hxeq :=  rfl
 m:= 3
 C := ![26988, 99902, -36483, -33365, -61972]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![656, 471, 553, 230, 264] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-397, 471, 553, 230, 264]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![658, 471, 553, 230, 264]
 hxeq :=  rfl
 m:= 2
 C := ![656, 471, 553, 230, 264]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-43, -12, 5, 5, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-8, -12, 5, 5, 8]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-15, -12, 5, 5, 8]
 hxeq :=  rfl
 m:= 28
 C := ![-43, -12, 5, 5, 8]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  16
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![26970, 99902, -36483, -33365, -61972] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![47533, 99902, -36483, -33365, -61972]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![26991, 99902, -36483, -33365, -61972]
 hxeq :=  rfl
 m:= 21
 C := ![26970, 99902, -36483, -33365, -61972]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  29
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![657, 471, 553, 230, 264] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-619, 471, 553, 230, 264]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![658, 471, 553, 230, 264]
 hxeq :=  rfl
 m:= 1
 C := ![657, 471, 553, 230, 264]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  0
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![12, -4, 2, 0, 2], ![20, -15, 4, 3, 8]]]
 hmul := by decide
 f :=  ![![![![-15933728, -28565530, 12085710, 10708530, 22581086], ![-1902234, 9998736, -297984, -247086, 0]], ![![0, 0, 0, 0, 0], ![-45985, 3307, 168, 1, 0]]], ![![![-284184, -509476, 215554, 190990, 402741], ![-33924, 178332, -5313, -4407, 0]], ![![0, 0, 0, 0, 0], ![-820, 59, 3, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![10, -21, 3, 0, 13], ![2, 12, -6, 0, 0]]], ![![![10, -21, 3, 0, 13], ![2, 12, -6, 0, 0]], ![![29, -69, 10, 0, 42], ![0, 41, -19, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![4, 0, 0, 0, 0], ![-2, -3, 0, 1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![12, -4, 2, 0, 2]], ![![4, 2, 2, 0, 0], ![2, 1, -1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-201, -346, 144, 131, 274], ![-26, 120, -6, -3, 0]], ![![0, 0, 0, 0, 0], ![2, 2, 0, 0, 0]]], ![![![18, 35, -12, -15, -33], ![19, -6, 9, 0, 0]], ![![0, 0, 0, 0, 0], ![-4, -1, -3, 0, 0]]]]
 g :=  ![![![![16461, -6693, 1953, -2875, 217], ![-3818, -6798, -840, 6, 0]], ![![56908, -23140, 6753, -9939, 751], ![-13201, -23501, -2904, 21, 0]]], ![![![32810, -13342, 3894, -5730, 434], ![-7612, -13550, -1674, 12, 0]], ![![294, -116, 34, -52, 2], ![-64, -121, -15, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![-2, -3, 0, 1, 2]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![24, -8, 4, 0, 4]], ![![-4, -6, 0, 2, 4], ![-10, -9, 4, 3, 4]]]
 hmul := by decide
 f :=  ![![![![-26134559983, -46794025670, 19308773479, 17586789919, 36863358034], ![-3523588502, 16827392232, -462758751, -188770232, 0]], ![![-78760962, -12837735, 379824, 0, 0], ![-61713, 1483, -72, -9, 0]]], ![![![-26396490169, -47263012630, 19502293119, 17763051206, 37232816188], ![-3558903208, 16996042553, -467396692, -190662157, 0]], ![![-79550333, -12966399, 383631, 0, 0], ![-62331, 1498, -73, -9, 0]]]]
 g :=  ![![![![4, -13, 1, 0, 8], ![4, 16, -8, 0, 0]], ![![2, 3, -1, 0, -3], ![4, -8, 4, 0, 0]]], ![![![-12, 30, -6, 0, -21], ![0, -42, 22, 0, 0]], ![![-25, 56, -11, 0, -40], ![4, -79, 41, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![![658, 471, 553, 230, 264]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![24, -8, 4, 0, 4]], ![![4, 2, 2, 0, 0], ![2, 1, -1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-293568, -524900, 216686, 197471, 414092], ![-40394, 188419, -5719, -2121, 0]], ![![741, 879, -741, 0, 0], ![247, -224, -82, 0, 0]]]]
 g :=  ![![![![-156, 21, -95, 29, -13]], ![![229, -11, 126, -53, -18]]], ![![![102, 17, 37, -35, -53]], ![![-113, -35, -27, 47, 91]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1191, -846, -991, -411, -472])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-93249, -16708, -32775, 32563, 50708])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

