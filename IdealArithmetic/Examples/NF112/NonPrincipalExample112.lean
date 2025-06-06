import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF112.RI112

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
instance hq131 : Fact $ Nat.Prime 131 := by decide
instance hq31 : Fact $ Nat.Prime 31 := by decide

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R131 : IsOrderOf (2 : ZMod 131) 130 where
 m := 3
 P := ![2, 5, 13]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by sorry
 hnid := by decide

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![-45, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 5, 0], ![98, -82, 57, 68, 222], ![-32, 24, -17, -22, -68]]]
  hmulB := by decide
  f := ![![![99, -246, 112, 53, 222], ![1804, -605, 33, -11, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, -4, 0], ![0, 0, 9, 0, 0]], ![![45, -111, 50, 25, 101], ![811, -265, 13, -5, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 5, 0], ![-92, -82, 57, 68, 222], ![28, 24, -17, -22, -68]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![7, 1, 0, 0, 0], ![0, 7, 1, 0, 0], ![0, 0, 7, 5, 0], ![98, -82, 57, 75, 222], ![-32, 24, -17, -22, -61]]]
  hmulB := by decide
  f := ![![![2830668, 291689, 12551136, 8989380, 115884], ![-12309263, 277140, -55491426, -16182, 0]], ![![786282, 81018, 3486405, 2497035, 32190], ![-3419175, 77004, -15414192, -4495, 0]], ![![1258070, 129641, 5578262, 3995265, 51504], ![-5470763, 123164, -24662763, -7192, 0]], ![![1729844, 178253, 7670140, 5493511, 70818], ![-7522289, 169364, -33911433, -9889, 0]], ![![456558, 47041, 2024376, 1449900, 18691], ![-1985359, 44724, -8950230, -2610, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 31, 0, 0, 0], ![-13, 0, 31, 0, 0], ![-19, 0, 0, 31, 0], ![-5, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-2, 7, 1, 0, 0], ![-6, 0, 7, 5, 0], ![-84, -82, 57, 75, 222], ![24, 24, -17, -22, -61]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![131, 0, 0, 0, 0], ![-45, 1, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]], ![![-45, 1, 0, 0, 0], ![0, -45, 1, 0, 0], ![0, 0, -45, 5, 0], ![98, -82, 57, 23, 222], ![-32, 24, -17, -22, -113]]]
  hmulB := by decide
  f := ![![![4489873156, -140159570, -13057846029, 1451231100, 1978020], ![13067977705, -115493661, -38016885654, -1167210, 0]], ![![2993248756, -93439713, -8705230686, 967487400, 1318680], ![8711985094, -76995774, -25344590436, -778140, 0]], ![![2444486524, -76309095, -7109272024, 790114743, 1076922], ![7114787943, -62879868, -20698083054, -635481, 0]], ![![3941110868, -123028948, -11461887061, 1273858409, 1736262], ![11470780391, -101377747, -33370377381, -1024551, 0]], ![![3872944018, -120901034, -11263638177, 1251825300, 1706231], ![11272377709, -99624393, -32793191442, -1006830, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-86, 131, 0, 0, 0], ![-71, 0, 131, 0, 0], ![-115, 0, 0, 131, 0], ![-113, 0, 0, 0, 131]], ![![-1, 1, 0, 0, 0], ![29, -45, 1, 0, 0], ![20, 0, -45, 5, 0], ![-188, -82, 57, 23, 222], ![110, 24, -17, -22, -113]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![416355, -88799, 67875, 113988, 357834]

def zeta2 := B.equivFun.symm ![-27871707746025729, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]

def alpha := B.equivFun.symm ![-15494, 74713, -35713, -46552, -141563]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![416348, -88799, 67875, 113988, 357834] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-124802, -88799, 67875, 113988, 357834]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![416355, -88799, 67875, 113988, 357834]
 hxeq :=  rfl
 m:= 7
 C := ![416348, -88799, 67875, 113988, 357834]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-27871707746025736, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![20765475697636234, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-27871707746025729, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hxeq :=  rfl
 m:= 7
 C := ![-27871707746025736, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-15497, 74713, -35713, -46552, -141563] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![62938, 74713, -35713, -46552, -141563]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-15494, 74713, -35713, -46552, -141563]
 hxeq :=  rfl
 m:= 3
 C := ![-15497, 74713, -35713, -46552, -141563]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![416333, -88799, 67875, 113988, 357834] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-122561, -88799, 67875, 113988, 357834]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![416355, -88799, 67875, 113988, 357834]
 hxeq :=  rfl
 m:= 22
 C := ![416333, -88799, 67875, 113988, 357834]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  17
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-27871707746025754, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![18131959490855752, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-27871707746025729, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hxeq :=  rfl
 m:= 25
 C := ![-27871707746025754, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  10
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-15511, 74713, -35713, -46552, -141563] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![48970, 74713, -35713, -46552, -141563]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-15494, 74713, -35713, -46552, -141563]
 hxeq :=  rfl
 m:= 17
 C := ![-15511, 74713, -35713, -46552, -141563]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] ![416247, -88799, 67875, 113988, 357834] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-384046, -88799, 67875, 113988, 357834]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![416355, -88799, 67875, 113988, 357834]
 hxeq :=  rfl
 m:= 108
 C := ![416247, -88799, 67875, 113988, 357834]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  88
 hpow := by sorry
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] ![-27871707746025783, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![53667031026502928, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-27871707746025729, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hxeq :=  rfl
 m:= 54
 C := ![-27871707746025783, 14999638523133007, -12892911205012467, -14266322923120986, -51258388084004862]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  87
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] ![-15527, 74713, -35713, -46552, -141563] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![133167, 74713, -35713, -46552, -141563]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-15494, 74713, -35713, -46552, -141563]
 hxeq :=  rfl
 m:= 33
 C := ![-15527, 74713, -35713, -46552, -141563]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  128
 hpow := by sorry
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![2, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 4, -2, -2, -6]], ![![4, 4, -2, -2, -6], ![24, -23, 13, 16, 57]]]
 hmul := by decide
 f :=  ![![![![787757463012, 594326684286, -677500745700, -374895859389, -1797746007139], ![-1319797673460, 297509780143, -15104406810, 0, 110284596]], ![![0, 0, 0, 0, 0], ![3063461, -37457, -267, 0, 1]]], ![![![-717177250451, -541077168199, 616799135264, 341306549631, 1636674482897], ![1201548587041, -270853982506, 13751106723, 0, -100403496]], ![![0, 0, 0, 0, 0], ![-2788986, 34101, 243, 0, -1]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-454, -225, 103, 108, 322], ![-54, -62, -6, 0, 0]]], ![![![-454, -225, 103, 108, 322], ![-54, -62, -6, 0, 0]], ![![2719, 1382, -638, -670, -2001], ![335, 376, 36, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![4, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![4, 4, -2, -2, -6]], ![![28, -10, 6, 8, 26], ![30, -9, 11, 12, 43]]]
 hmul := by decide
 f :=  ![![![![-20762481539, -15664260656, 17857109620, 9881178573, 47383518888], ![34786698178, -7841529056, 398104929, 0, -2873796]], ![![0, 0, 0, 0, 0], ![-206916, 680, -2, 0, 0]]], ![![![-124693901709, -94075352909, 107245016310, 59343711254, 284572719993], ![208919589627, -47094122704, 2390911548, 0, -17259249]], ![![0, 0, 0, 0, 0], ![-1242681, 4084, -12, 0, 0]]]]
 g :=  ![![![![735, 370, -167, -176, -522], ![176, 200, 20, 0, 0]], ![![-517013, -255072, 114988, 120741, 357816], ![-120741, -139213, -13877, 0, -21]]], ![![![1483814, 732089, -330031, -346546, -1026991], ![346546, 399548, 39828, 0, 60]], ![![1705241, 841333, -379279, -398258, -1180240], ![398258, 459171, 45771, 0, 69]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![14, -5, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![4, 0, 0, 0, 0], ![14, -3, 3, 4, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![8, 8, -4, -4, -12]], ![![28, -10, 6, 8, 26], ![30, -9, 11, 12, 43]]]
 hmul := by decide
 f :=  ![![![![7718748430448975294, 6715719576793255731, -5333439518363879532, -3762199554395027845, -14780874828517048306], ![-10486507580246295733, 1544628811773717193, -78455626016353502, 0, 247481404941848]], ![![14231315267498, -150641176562, -14818082931, 0, 0], ![401696805, -1320169, 3877, 0, -9]]], ![![![15425546079890459684, 13421041341727094862, -10658621380933559672, -7518574171834772702, -29538864729540162599], ![-20956779114357113618, 3086866106213542621, -156789780784644511, 0, 494579639464225]], ![![28440596479379, -301049118458, -29613223326, 0, 0], ![802771671, -2638294, 7748, 0, -18]]]]
 g :=  ![![![![-160, 429, 123, -252, 381], ![252, 0, 96, 0, 0]], ![![118, -375, -105, 220, -334], ![-220, -4, -84, 0, 0]]], ![![![-864, 2482, 710, -1454, 2223], ![1454, 8, 556, 0, 0]], ![![-844, 2477, 703, -1451, 2208], ![1451, 12, 554, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![14, -3, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![-15494, 74713, -35713, -46552, -141563]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![8, 8, -4, -4, -12]], ![![28, -6, 6, 8, 26], ![26, 15, 3, -2, 7]]]
 hmul := by decide
 f :=  ![![![![-1480281362021619458, -1287923275669945914, 1022836108419653740, 721506666749980507, 2834645135540032961], ![2011083944390820594, -296225749882369811, 15046029040530999, 0, -47240167730693]], ![![-4585522873015, 18587558925, 39341487759, 0, 0], ![23714749101, -37153552, 82460, 0, 0]]]]
 g :=  ![![![![-5470, 2849, -1814, -1781, -6574]], ![![28409, -10866, 9007, 11215, 38623]]], ![![![18958, -9805, 8728, 9903, 35320]], ![![-87169, 15379, -11278, -21555, -65380]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-7357150742275, 2482701464523, -1426969328867, -1755669472306, -5949858965136])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-53244018700387351, -475661232740110983, 165572817600232159, 231313712475559748, 731897584179683280])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

