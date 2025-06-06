import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF31.RI31

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
instance hq19 : Fact $ Nat.Prime 19 := by decide
instance hq7 : Fact $ Nat.Prime 7 := by decide

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![3, -1, -2, 4, 6], ![-6, -1, 2, -1, -2]]]
  hmulB := by decide
  f := ![![![140, -324, -415, -672, 144], ![-469, -119, 2688, -168, 0]], ![![22, -56, -70, -112, 24], ![-69, -14, 448, -28, 0]], ![![116, -270, -345, -560, 120], ![-386, -104, 2240, -140, 0]], ![![0, -1, -1, -1, 0], ![0, 3, 4, 0, 0]], ![![100, -231, -296, -480, 103], ![-335, -88, 1920, -120, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-2, -1, -2, 4, 6], ![-1, -1, 2, -1, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 1, -3, 2, 0], ![3, -1, -2, 0, 6], ![-6, -1, 2, -1, -6]]]
  hmulB := by decide
  f := ![![![-1118, 619, -898, 630, -72], ![-2527, -161, -2205, 84, 0]], ![![-842, 467, -676, 474, -54], ![-1903, -119, -1659, 63, 0]], ![![-838, 466, -676, 474, -54], ![-1894, -118, -1659, 63, 0]], ![![-274, 154, -224, 157, -18], ![-619, -37, -549, 21, 0]], ![![-638, 353, -513, 360, -41], ![-1442, -93, -1260, 48, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-2, 0, 0, 7, 0], ![-4, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![1, -3, 1, 0, 0], ![1, 1, -3, 2, 0], ![-1, -1, -2, 0, 6], ![2, -1, 2, -1, -6]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![19, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 1, -2, 2, 0], ![3, -1, -2, 1, 6], ![-6, -1, 2, -1, -5]]]
  hmulB := by decide
  f := ![![![2925, -7304, 11846, -11932, 144], ![27094, 1178, 113582, -456, 0]], ![![2919, -7294, 11832, -11918, 144], ![27038, 1178, 113449, -456, 0]], ![![2433, -6079, 9862, -9934, 120], ![22536, 989, 94563, -380, 0]], ![![2436, -6086, 9873, -9945, 120], ![22564, 989, 94668, -380, 0]], ![![1848, -4614, 7482, -7536, 91], ![17118, 738, 71736, -288, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-17, 19, 0, 0, 0], ![-15, 0, 19, 0, 0], ![-16, 0, 0, 19, 0], ![-12, 0, 0, 0, 19]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-1, 1, -2, 2, 0], ![-2, -1, -2, 1, 6], ![3, -1, 2, -1, -5]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![-3, 3, -1, 0, 2]

def zeta2 := B.equivFun.symm ![23660192637015, 2254937192931, -7939006997157, 5704386158684, 4933097265316]

def alpha := B.equivFun.symm ![39385593, 5185057, -14008882, 9338801, 13238284]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-7, 3, -1, 0, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-2, 3, -1, 0, 2]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 3, -1, 0, 2]
 hxeq :=  rfl
 m:= 4
 C := ![-7, 3, -1, 0, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![23660192637013, 2254937192931, -7939006997157, 5704386158684, 4933097265316] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![6339115871492, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![23660192637015, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hxeq :=  rfl
 m:= 2
 C := ![23660192637013, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![39385587, 5185057, -14008882, 9338801, 13238284] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![7437486, 5185057, -14008882, 9338801, 13238284]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![39385593, 5185057, -14008882, 9338801, 13238284]
 hxeq :=  rfl
 m:= 6
 C := ![39385587, 5185057, -14008882, 9338801, 13238284]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-6, 3, -1, 0, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-3, 3, -1, 0, 2]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 3, -1, 0, 2]
 hxeq :=  rfl
 m:= 3
 C := ![-6, 3, -1, 0, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![23660192637009, 2254937192931, -7939006997157, 5704386158684, 4933097265316] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![3313473924634, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![23660192637015, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hxeq :=  rfl
 m:= 6
 C := ![23660192637009, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![39385591, 5185057, -14008882, 9338801, 13238284] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![2437005, 5185057, -14008882, 9338801, 13238284]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![39385593, 5185057, -14008882, 9338801, 13238284]
 hxeq :=  rfl
 m:= 2
 C := ![39385591, 5185057, -14008882, 9338801, 13238284]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![-16, 3, -1, 0, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-4, 3, -1, 0, 2]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 3, -1, 0, 2]
 hxeq :=  rfl
 m:= 13
 C := ![-16, 3, -1, 0, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![23660192637001, 2254937192931, -7939006997157, 5704386158684, 4933097265316] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-2423998968853, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![23660192637015, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hxeq :=  rfl
 m:= 14
 C := ![23660192637001, 2254937192931, -7939006997157, 5704386158684, 4933097265316]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![39385590, 5185057, -14008882, 9338801, 13238284] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-7731967, 5185057, -14008882, 9338801, 13238284]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![39385593, 5185057, -14008882, 9338801, 13238284]
 hxeq :=  rfl
 m:= 3
 C := ![39385590, 5185057, -14008882, 9338801, 13238284]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  13
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
 f :=  ![![![![127600, -57966, -64532, 116656, 235839], ![43476, -32264, 0, -76560, 4104]], ![![0, 0, 0, 0, 0], ![-340, 512, 0, 64, -4]]], ![![![63890, -29024, -32312, 58410, 118086], ![21769, -16154, 0, -38334, 2055]], ![![0, 0, 0, 0, 0], ![-170, 257, 0, 32, -2]]]]
 g :=  ![![![![24, -36, 0, 76, 43], ![8, 96, -80, -28, 4]], ![![20, -28, 0, 64, 37], ![8, 76, -66, -24, 4]]], ![![![20, -28, 0, 64, 37], ![8, 76, -66, -24, 4]], ![![1, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![4, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![39385593, 5185057, -14008882, 9338801, 13238284]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![0, 4, 0, 0, 0]], ![![4, 2, 0, 0, 0], ![0, 2, 1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![118167501486771, -58738876154952, -61577125358852, 113606029551933, 228160843007951], ![44054157116214, -30788562679424, 0, -75197500946127, 1773905752437]], ![![-201044456724, 128987091630, 0, 61187301711, -3306244104], ![951331071, -442269189, 0, -50754783, 30046792]]]]
 g :=  ![![![![831769086765, -341059815510, -13825664259, 59290224306, 240325941260]], ![![-632042487321, 259163628470, 10505809199, -45053298430, -182618238972]]], ![![![99863299722, -40948093520, -1659927530, 7118462938, 28853851144]], ![![-75883859025, 31115529055, 1261341446, -5409158695, -21925387902]]]]
 hle1 := by decide
 hle2 := by decide

lemma J3 : J ^ 3 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![3, -1, -3, -10, -10])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-23584247655287866223380575, 9670519486412793918203507, 392017323521799411850117, -1681134052174844745054038, -6814278879505475012377484])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

