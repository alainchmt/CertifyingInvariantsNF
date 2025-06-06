import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF67.RI67

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
instance hq37 : Fact $ Nat.Prime 37 := by decide
instance hq13 : Fact $ Nat.Prime 13 := by decide
instance hq7 : Fact $ Nat.Prime 7 := by decide

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
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
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-2, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![10, -5, 11, -13, -1]]]
  hmulB := by decide
  f := ![![![662, -2235, -1402, 3066, 3426], ![2527, 28, 0, -12096, -210]], ![![662, -2235, -1402, 3066, 3426], ![2528, 28, 0, -12096, -210]], ![![662, -2232, -1399, 3060, 3420], ![2528, 29, 0, -12075, -210]], ![![364, -1226, -768, 1680, 1877], ![1394, 14, 0, -6627, -115]], ![![190, -639, -401, 876, 979], ![728, 11, 0, -3456, -60]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-4, 0, 0, 7, 0], ![-2, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![4, -5, 11, -13, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![-2, -1, -1, 7, 0], ![0, -1, -1, 5, 2], ![10, -5, 11, -13, 2]]]
  hmulB := by decide
  f := ![![![-119325, -60937, -5249, 32188, -128], ![715247, 8697, -60372, 832, 0]], ![![-29910, -15275, -1316, 8068, -32], ![179284, 2184, -15132, 208, 0]], ![![-89417, -45663, -3933, 24120, -96], ![535975, 6514, -45240, 624, 0]], ![![-44757, -22857, -1969, 12073, -48], ![268279, 3265, -22644, 312, 0]], ![![-55074, -28126, -2423, 14856, -59], ![330120, 4019, -27864, 384, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 13, 0, 0, 0], ![-9, 0, 13, 0, 0], ![-5, 0, 0, 13, 0], ![-6, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, -1, -1, 7, 0], ![-2, -1, -1, 5, 2], ![-2, -5, 11, -13, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![-2, -1, 6, 7, 0], ![0, -1, -1, 12, 2], ![10, -5, 11, -13, 9]]]
  hmulB := by decide
  f := ![![![-91781774, -11343018, 1440336, 1807857, 768], ![375206973, 3882114, -9531459, -14208, 0]], ![![-22939830, -2835069, 359995, 451854, 192], ![93778795, 970325, -2382282, -3552, 0]], ![![-74573166, -9216264, 1170280, 1468893, 624], ![304857606, 3154251, -7744359, -11544, 0]], ![![-17208830, -2126792, 270058, 338968, 144], ![70350275, 727916, -1787121, -2664, 0]], ![![-81859422, -10116746, 1284624, 1612413, 685], ![334644065, 3462426, -8501031, -12672, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 37, 0, 0, 0], ![-30, 0, 37, 0, 0], ![-7, 0, 0, 37, 0], ![-33, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-3, 9, 1, 0, 0], ![-6, -1, 6, 7, 0], ![-3, -1, -1, 12, 2], ![-13, -5, 11, -13, 9]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![732565, -518780, 105501, -76167, 48164]

def zeta2 := B.equivFun.symm ![-43063, 19747, -1913, 6064, -38]

def alpha := B.equivFun.symm ![-515, 169, 6, 80, 17]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![732564, -518780, 105501, -76167, 48164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![488654, -518780, 105501, -76167, 48164]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![732565, -518780, 105501, -76167, 48164]
 hxeq :=  rfl
 m:= 1
 C := ![732564, -518780, 105501, -76167, 48164]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-43067, 19747, -1913, 6064, -38] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-24893, 19747, -1913, 6064, -38]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-43063, 19747, -1913, 6064, -38]
 hxeq :=  rfl
 m:= 4
 C := ![-43067, 19747, -1913, 6064, -38]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-521, 169, 6, 80, 17] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-275, 169, 6, 80, 17]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-515, 169, 6, 80, 17]
 hxeq :=  rfl
 m:= 6
 C := ![-521, 169, 6, 80, 17]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![732555, -518780, 105501, -76167, 48164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![70189, -518780, 105501, -76167, 48164]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![732565, -518780, 105501, -76167, 48164]
 hxeq :=  rfl
 m:= 10
 C := ![732555, -518780, 105501, -76167, 48164]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  10
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-43064, 19747, -1913, 6064, -38] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-7341, 19747, -1913, 6064, -38]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-43063, 19747, -1913, 6064, -38]
 hxeq :=  rfl
 m:= 1
 C := ![-43064, 19747, -1913, 6064, -38]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-523, 169, 6, 80, 17] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-109, 169, 6, 80, 17]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-515, 169, 6, 80, 17]
 hxeq :=  rfl
 m:= 8
 C := ![-523, 169, 6, 80, 17]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] ![732553, -518780, 105501, -76167, 48164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![31900, -518780, 105501, -76167, 48164]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![732565, -518780, 105501, -76167, 48164]
 hxeq :=  rfl
 m:= 12
 C := ![732553, -518780, 105501, -76167, 48164]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  28
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] ![-43083, 19747, -1913, 6064, -38] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-5530, 19747, -1913, 6064, -38]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-43063, 19747, -1913, 6064, -38]
 hxeq :=  rfl
 m:= 20
 C := ![-43083, 19747, -1913, 6064, -38]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  25
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] ![-545, 169, 6, 80, 17] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-91, 169, 6, 80, 17]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-515, 169, 6, 80, 17]
 hxeq :=  rfl
 m:= 30
 C := ![-545, 169, 6, 80, 17]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  14
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]]
  ![![4, 0, 0, 0, 0], ![9, -5, 2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![14, -10, 4, 0, 2]], ![![14, -10, 4, 0, 2], ![19, -24, 11, 4, 7]]]
 hmul := by decide
 f :=  ![![![![857052, 679556, -409540, 0, -598009], ![592264, -963704, 314988, -10708, 0]], ![![0, 0, 0, 0, 0], ![-1348, -24, -4, 0, 0]]], ![![![1654588, 1311923, -790635, 0, -1154480], ![1143394, -1860479, 608097, -20675, 0]], ![![0, 0, 0, 0, 0], ![-2601, -47, -7, 0, 0]]]]
 g :=  ![![![![3745, 3683, -1754, 0, -1660], ![2536, -6264, 2088, -36, 0]], ![![8864, 8720, -4154, 0, -3931], ![6006, -14832, 4944, -84, 0]]], ![![![8864, 8720, -4154, 0, -3931], ![6006, -14832, 4944, -84, 0]], ![![7174, 7058, -3365, 0, -3184], ![4865, -12011, 4005, -66, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![4, 0, 0, 0, 0], ![9, -5, 2, 0, 1]] ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]]
  ![![-515, 169, 6, 80, 17]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![28, -20, 8, 0, 4]], ![![18, -10, 4, 0, 2], ![33, -34, 15, 4, 9]]]
 hmul := by decide
 f :=  ![![![![116736590424, 99057828510, -48352941456, 0, -71961019025], ![76600044256, -126303521910, 38254401780, -5770158285, 0]], ![![4878983685, 267482790, -89378280, 2636454, 0], ![330143, 7045, -1879, -80, 0]]]]
 g :=  ![![![![2395984, -1333210, 1050089, 526014, 617933]], ![![5964356, -3318778, 2614001, 1309414, 1538229]]], ![![![4180170, -2325994, 1832045, 917714, 1078081]], ![![10405755, -5790129, 4560535, 2284478, 2683682]]]]
 hle1 := by decide
 hle2 := by decide

lemma J3 : J ^ 3 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-42117, 23900, -46157, 69239, -52194])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![13145817655579315, -7314796502938757, 5761423464721343, 2886031062176506, 3390354069449008])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

