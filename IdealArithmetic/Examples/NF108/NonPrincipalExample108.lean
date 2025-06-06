import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF108.RI108

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
instance hq61 : Fact $ Nat.Prime 61 := by decide
instance hq31 : Fact $ Nat.Prime 31 := by decide

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![2, -3, 1, -1, 6], ![-72, -34, 4, 6, 1]]]
  hmulB := by decide
  f := ![![![-31, -208, 0, -496, -96], ![0, -496, 7936, 496, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![15, 0, 16, 0, 0]], ![![-21, -141, 0, -336, -65], ![3, -336, 5376, 336, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![-21, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![-4, -3, 1, -1, 6], ![-3, -34, 4, 6, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 1, -11, 2, 0], ![2, -3, 1, -12, 6], ![-72, -34, 4, 6, -10]]]
  hmulB := by decide
  f := ![![![171408, -16519, -18138, -930, 2160], ![481027, -4557, -52545, -11160, 0]], ![![114276, -11013, -12092, -620, 1440], ![320696, -3038, -35030, -7440, 0]], ![![21412, -2056, -2302, -110, 270], ![60089, -557, -6665, -1395, 0]], ![![121422, -11704, -12846, -659, 1530], ![340750, -3234, -37215, -7905, 0]], ![![154840, -14919, -16383, -840, 1951], ![434532, -4107, -47460, -10080, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-20, 31, 0, 0, 0], ![-3, 0, 31, 0, 0], ![-22, 0, 0, 31, 0], ![-28, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![7, -11, 1, 0, 0], ![-1, 1, -11, 2, 0], ![5, -3, 1, -12, 6], ![24, -34, 4, 6, -10]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![6, 1, 0, 0, 0], ![0, 6, 1, 0, 0], ![0, 1, 6, 2, 0], ![2, -3, 1, 5, 6], ![-72, -34, 4, 6, 7]]]
  hmulB := by decide
  f := ![![![3613861, 3507480, 17783939, 5937679, 8514], ![-36712057, 563152, -180882812, -86559, 0]], ![![420192, 407831, 2067849, 690411, 990], ![-4268596, 65514, -21032373, -10065, 0]], ![![1512775, 1468248, 7444463, 2485548, 3564], ![-15367797, 235766, -75718629, -36234, 0]], ![![2605334, 2528645, 12820978, 4280652, 6138], ![-26466754, 406013, -130403878, -62403, 0]], ![![3199146, 3104980, 15743159, 5256306, 7537], ![-32499100, 498535, -160125768, -76626, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 61, 0, 0, 0], ![-25, 0, 61, 0, 0], ![-44, 0, 0, 61, 0], ![-54, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-1, 6, 1, 0, 0], ![-4, 1, 6, 2, 0], ![-9, -3, 1, 5, 6], ![-10, -34, 4, 6, 7]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![-128547, -93443, -10436, 5627, 8855]

def zeta2 := B.equivFun.symm ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]

def alpha := B.equivFun.symm ![7001899, 1456956, -648479, -339780, 395103]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] ![-128571, -93443, -10436, 5627, 8855] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-10146, -93443, -10436, 5627, 8855]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-128547, -93443, -10436, 5627, 8855]
 hxeq :=  rfl
 m:= 24
 C := ![-128571, -93443, -10436, 5627, 8855]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  13
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] ![630777067824, 455760802015, 48555409531, -28976360690, -44398778352] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![50424239136, 455760802015, 48555409531, -28976360690, -44398778352]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]
 hxeq :=  rfl
 m:= 29
 C := ![630777067824, 455760802015, 48555409531, -28976360690, -44398778352]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  9
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] ![7001890, 1456956, -648479, -339780, 395103] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-41783, 1456956, -648479, -339780, 395103]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![7001899, 1456956, -648479, -339780, 395103]
 hxeq :=  rfl
 m:= 9
 C := ![7001890, 1456956, -648479, -339780, 395103]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![-128567, -93443, -10436, 5627, 8855] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![45157, -93443, -10436, 5627, 8855]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-128547, -93443, -10436, 5627, 8855]
 hxeq :=  rfl
 m:= 20
 C := ![-128567, -93443, -10436, 5627, 8855]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![630777067850, 455760802015, 48555409531, -28976360690, -44398778352] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-217724499097, 455760802015, 48555409531, -28976360690, -44398778352]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]
 hxeq :=  rfl
 m:= 3
 C := ![630777067850, 455760802015, 48555409531, -28976360690, -44398778352]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] ![7001896, 1456956, -648479, -339780, 395103] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-767081, 1456956, -648479, -339780, 395103]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![7001899, 1456956, -648479, -339780, 395103]
 hxeq :=  rfl
 m:= 3
 C := ![7001896, 1456956, -648479, -339780, 395103]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![-128557, -93443, -10436, 5627, 8855] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-537, -93443, -10436, 5627, 8855]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-128547, -93443, -10436, 5627, 8855]
 hxeq :=  rfl
 m:= 10
 C := ![-128557, -93443, -10436, 5627, 8855]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  23
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![630777067811, 455760802015, 48555409531, -28976360690, -44398778352] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![5816736374, 455760802015, 48555409531, -28976360690, -44398778352]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![630777067853, 455760802015, 48555409531, -28976360690, -44398778352]
 hxeq :=  rfl
 m:= 42
 C := ![630777067811, 455760802015, 48555409531, -28976360690, -44398778352]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  56
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![7001895, 1456956, -648479, -339780, 395103] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![132572, 1456956, -648479, -339780, 395103]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![7001899, 1456956, -648479, -339780, 395103]
 hxeq :=  rfl
 m:= 4
 C := ![7001895, 1456956, -648479, -339780, 395103]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  2
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]] ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]]
  ![![2, 0, 0, 0, 0], ![33, 4, -4, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![110, 18, -12, -4, 6]], ![![110, 18, -12, -4, 6], ![99, 60, -8, -15, 12]]]
 hmul := by decide
 f :=  ![![![![646760235767385, -9179423088449871, -4292325306564235, -22944529395458, 2567180042404146], ![-6770806901726852, -1683488947101927, 0, -556636539015, -2654268930]], ![![0, 0, 0, 0, 0], ![-10507340, 11628, 0, 9, 0]]], ![![![4775737172029307584, -67781705857780854522, -31694925549463618978, -169424519116569049, 18956293967662398346], ![-49996262010206863262, -12431037498518627226, 0, -4110255491402490, -19599366337872]], ![![0, 0, 0, 0, 0], ![-77587166649, 85862236, 0, 66456, -2]]]]
 g :=  ![![![![-31, -4, 4, 1, -2], ![2, 0, 0, 0, 0]], ![![-17, 1051, 416, -36, -304], ![712, 168, 0, 0, -6]]], ![![![-17, 1051, 416, -36, -304], ![712, 168, 0, 0, -6]], ![![-58, 1972, 782, -72, -567], ![1351, 320, 0, 0, -12]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![33, 4, -4, -1, 2]] ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]]
  ![![4, 0, 0, 0, 0], ![37, 10, -5, -2, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![110, 18, -12, -4, 6]], ![![66, 8, -8, -2, 4], ![-135, -2, 11, -2, -1]]]
 hmul := by decide
 f :=  ![![![![-73304490867020, 1040405522822558, 486496683600811, 2600551011955, -290966892861771], ![767410412751786, 190808417072325, 0, 63089767083, 300426936]], ![![0, 0, 0, 0, 0], ![-1354460, 20082, 0, 0, -4]]], ![![![-769708462820104, 10924418493460734, 5108290229868782, 27306186813688, -3055197262640876], ![8057927722640266, 2003517815358984, 0, 662452287258, 3154529175]], ![![0, 0, 0, 0, 0], ![-14222039, 210864, 0, 0, -42]]]]
 g :=  ![![![![31362346463585, 54029014346290, 93375346758139, 17285171422455, -86122711733154], ![235220437695496, 40129994843112, -10049280, 1248, -4]], ![![954968319882391, 1645157421975293, 2843234262317825, 526325131039733, -2622395024649114], ![7162348851946412, 1221938983317720, -305995728, 38001, -122]]], ![![![579298686155614, 997978166633652, 1724750275272164, 319277038362435, -1590785747266829], ![4344792589802070, 741247256961846, -185621784, 23052, -74]], ![![-1143820894399375, -1970500376455683, -3405506433251879, -630410108478634, 3140994481295399], ![-8578760257557411, -1463587128180363, 366508815, -45516, 146]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![37, 10, -5, -2, 3]] ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]]
  ![![4, 0, 0, 0, 0], ![31, 4, -4, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![220, 36, -24, -8, 12]], ![![74, 20, -10, -4, 6], ![-447, -68, 44, 5, -12]]]
 hmul := by decide
 f :=  ![![![![2350772123456639922218149, -33367788468207812260177673, -15600357860608365120652758, -84584797580508100736111, 9332758482663829540224469], ![-24624018608476209536768886, -6129434111919172557991782, 0, -868142832441950396121, -1772208432717477461]], ![![-9651869172881106, 14624211385035, 0, 0, 15967570167], ![-21630686, 24786, 0, 9, 0]]], ![![![13091417027118422002429176868, -185824746580562749041749334880, -86878174403907131296773135076, -471051552905337864563945919, 51974001261455210141705186824], ![-137130814709966218653628510720, -34134732711304938953671519214, 0, -4834675273369174148871249, -9869403937615808173497]], ![![-53751124225336154400, 81442028354798818, 0, 0, 88923174594492], ![-120460987349, 138032880, 0, 50118, -6]]]]
 g :=  ![![![![-4172, -66040, -26192, 1138, 18208], ![-63320, -13608, -24, 0, 0]], ![![-4505904, -71441638, -28334309, 1231097, 19696972], ![-68487272, -14719743, -26661, 0, 42]]], ![![![-2129547, -33764030, -13391069, 581830, 9308980], ![-32367710, -6956691, -12603, 0, 20]], ![![8390757, 133036729, 52763411, -2292517, -36679185], ![127535259, 27410724, 49644, 0, -78]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![31, 4, -4, -1, 2]] ![![2, 0, 0, 0, 0], ![55, 9, -6, -2, 3]]
  ![![7001899, 1456956, -648479, -339780, 395103]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![220, 36, -24, -8, 12]], ![![62, 8, -8, -2, 4], ![-245, -20, 23, 2, -7]]]
 hmul := by decide
 f :=  ![![![![-9680930965923710767117982639, 137414959666901174325957838242, 64245268985660839278567096901, 348336427709172034454735782, -38434091342997938259624229160], ![101406436538964641111473379689, 25242186548421671655603437927, 0, 3575178826552430245906128, 7297065936908231017940]], ![![52858754170027933983, -122802167730112029, 0, 0, 1576399374981718], ![4532420791015, -8884274292, 0, 0, -7650378]]]]
 g :=  ![![![![1052, 1329, -277, -200, 198]], ![![-64158, -11568, 6692, 1895, -2826]]], ![![![-27194, -5411, 2909, 878, -1264]], ![![149873, 17285, -14207, -2984, 5308]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-609307, 155029, 24866, -21233, 8267])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-119655258297208879370401570668697119, -24897875605938232957612576843259477, 11081841423197789437942793796535971, 5806491070781033663530911374803324, -6751905473927252215729268177059776])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

