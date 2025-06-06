import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF126.RI126

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
instance hq61 : Fact $ Nat.Prime 61 := by decide

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![11, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-9, 1, 0, 0, 0], ![0, -9, 1, 0, 0], ![0, 1, -9, 2, 0], ![0, 1, -1, -8, 2], ![15, -19, 0, 0, -10]]]
  hmulB := by decide
  f := ![![![1612, -256, 3429, -704, -16], ![1969, 385, 4224, 88, 0]], ![![406, -62, 857, -176, -4], ![496, 99, 1056, 22, 0]], ![![1232, -195, 2643, -544, -12], ![1505, 298, 3256, 66, 0]], ![![402, -61, 844, -173, -4], ![491, 98, 1040, 22, 0]], ![![1314, -213, 2806, -576, -13], ![1605, 310, 3456, 72, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 11, 0, 0, 0], ![-7, 0, 11, 0, 0], ![-3, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![1, -9, 1, 0, 0], ![5, 1, -9, 2, 0], ![1, 1, -1, -8, 2], ![13, -19, 0, 0, -10]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![8, 1, 0, 0, 0], ![0, 8, 1, 0, 0], ![0, 1, 8, 2, 0], ![0, 1, -1, 9, 2], ![15, -19, 0, 0, 7]]]
  hmulB := by decide
  f := ![![![1069161, 1469157, 11061376, 2757444, -2024], ![-8152345, 356484, -84379836, 61732, 0]], ![![185944, 255528, 1923935, 479610, -352], ![-1417822, 62037, -14676417, 10736, 0]], ![![1022690, 1405289, 10580506, 2637570, -1936], ![-7798004, 340991, -80711601, 59048, 0]], ![![139448, 191622, 1442781, 359665, -264], ![-1063290, 46539, -11006016, 8052, 0]], ![![876362, 1204222, 9066701, 2260200, -1659], ![-6682254, 292239, -69163800, 50600, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-8, 61, 0, 0, 0], ![-58, 0, 61, 0, 0], ![-8, 0, 0, 61, 0], ![-50, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-2, 8, 1, 0, 0], ![-8, 1, 8, 2, 0], ![-2, 1, -1, 9, 2], ![-3, -19, 0, 0, 7]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 3, 2, 0], ![0, 1, -1, 4, 2], ![15, -19, 0, 0, 2]]]
  hmulB := by decide
  f := ![![![-11, -40, -160, -66, 18], ![44, -22, 561, -99, 0]], ![![-21, -39, -148, -58, 18], ![78, -22, 517, -99, 0]], ![![-20, -38, -145, -56, 18], ![74, -21, 506, -99, 0]], ![![-1, -2, -2, -1, 0], ![4, 4, 6, 0, 0]], ![![-3, -12, -44, -18, 5], ![12, -2, 153, -27, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 11, 0, 0, 0], ![-2, 0, 11, 0, 0], ![-1, 0, 0, 11, 0], ![-3, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-1, 1, 3, 2, 0], ![-1, 1, -1, 4, 2], ![6, -19, 0, 0, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![31, 17, -3, 2, 4]

def zeta2 := B.equivFun.symm ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]

def alpha := B.equivFun.symm ![-11265398958422, -492985128159, 54800616190, -536592492194, -597626313393]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![22, 17, -3, 2, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-3, 17, -3, 2, 4]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![31, 17, -3, 2, 4]
 hxeq :=  rfl
 m:= 9
 C := ![22, 17, -3, 2, 4]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  6
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-4295384860860502876347593465084835634, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-350868632930530368271411447720429175, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hxeq :=  rfl
 m:= 5
 C := ![-4295384860860502876347593465084835634, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-11265398958427, -492985128159, 54800616190, -536592492194, -597626313393] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-334056247120, -492985128159, 54800616190, -536592492194, -597626313393]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-11265398958422, -492985128159, 54800616190, -536592492194, -597626313393]
 hxeq :=  rfl
 m:= 5
 C := ![-11265398958427, -492985128159, 54800616190, -536592492194, -597626313393]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] ![-5, 17, -3, 2, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-3, 17, -3, 2, 4]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![31, 17, -3, 2, 4]
 hxeq :=  rfl
 m:= 36
 C := ![-5, 17, -3, 2, 4]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  14
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] ![-4295384860860502876347593465084835650, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![1482683539386249181543469181685136352, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hxeq :=  rfl
 m:= 21
 C := ![-4295384860860502876347593465084835650, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  55
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] ![-11265398958473, -492985128159, 54800616190, -536592492194, -597626313393] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![388100031721, -492985128159, 54800616190, -536592492194, -597626313393]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-11265398958422, -492985128159, 54800616190, -536592492194, -597626313393]
 hxeq :=  rfl
 m:= 51
 C := ![-11265398958473, -492985128159, 54800616190, -536592492194, -597626313393]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  53
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![26, 17, -3, 2, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-3, 17, -3, 2, 4]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![31, 17, -3, 2, 4]
 hxeq :=  rfl
 m:= 5
 C := ![26, 17, -3, 2, 4]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![-4295384860860502876347593465084835631, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-2160558893907211524223807497004562764, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hxeq :=  rfl
 m:= 2
 C := ![-4295384860860502876347593465084835631, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![-11265398958423, -492985128159, 54800616190, -536592492194, -597626313393] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-687870306723, -492985128159, 54800616190, -536592492194, -597626313393]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-11265398958422, -492985128159, 54800616190, -536592492194, -597626313393]
 hxeq :=  rfl
 m:= 1
 C := ![-11265398958423, -492985128159, 54800616190, -536592492194, -597626313393]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  0
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![16, 2, 1, 2, 1]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![16, 2, 1, 2, 1]] ![![2, 0, 0, 0, 0], ![16, 2, 1, 2, 1]]
  ![![2, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![32, 4, 2, 4, 2]], ![![32, 4, 2, 4, 2], ![391, -60, -32, 15, 24]]]
 hmul := by decide
 f :=  ![![![![-335912286, 3635723497, 1981010221, -3382225427, -3411689392], ![-3149139691, 3329873454, 0, 38414511, 4833072]], ![![0, 0, 0, 0, 0], ![-216722, -594, 0, 3, 0]]], ![![![667289649390, -7222363831253, -3935276319159, 6718789946023, 6777320117873], ![6255765209371, -6614792781438, 0, -76310417517, -9600897417]], ![![0, 0, 0, 0, 0], ![430518359, 1180000, 0, -5955, -2]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-83, 100, 0, 34, 69], ![78, -66, 0, 0, 4]]], ![![![-83, 100, 0, 34, 69], ![78, -66, 0, 0, 4]], ![![1625, -1609, 0, -527, -1006], ![-1059, 988, 0, 0, -60]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![16, 2, 1, 2, 1]]
  ![![4, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![32, 4, 2, 4, 2]], ![![2, 4, 0, 2, 0], ![76, -23, -20, 6, 7]]]
 hmul := by decide
 f :=  ![![![![-23791596, 258067372, 140363034, -240601484, -242698071], ![-224034268, 236878140, 0, 2686824, 351270]], ![![0, 0, 0, 0, 0], ![-42456, -604, 0, 0, 4]]], ![![![-5946787, 64504737, 35084174, -60139085, -60663133], ![-55998057, 59208423, 0, 671580, 87801]], ![![0, 0, 0, 0, 0], ![-10612, -151, 0, 0, 1]]]]
 g :=  ![![![![-1302, 1328, 0, -188, 19], ![292, -44, 164, 6, 0]], ![![78778, -80388, 0, 11341, -1239], ![-17660, 2832, -9918, -351, 4]]], ![![![88559, -90364, 0, 12753, -1382], ![-19854, 3162, -11150, -396, 4]], ![![-525021, 535712, 0, -75614, 8167], ![117700, -18694, 66105, 2352, -23]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![1, 2, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![16, 2, 1, 2, 1]]
  ![![4, 0, 0, 0, 0], ![-1, 0, 0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![64, 8, 4, 8, 4]], ![![2, 4, 0, 2, 0], ![76, -23, -20, 6, 7]]]
 hmul := by decide
 f :=  ![![![![-719177864887730, 9179535931555811, 4776073467014166, -9691787370941169, -9500926755466057], ![-8628101002713035, 9211469834078190, 0, 43864142067039, 1449473953739]], ![![-192902707768, -103767794493, 0, 0, 6207458760], ![172429410, 2389196, 0, -3983, 4]]], ![![![179478405174108, -2290849801796150, -1191919399504856, 2418687539687854, 2371056264382442], ![2153233411723494, -2298819243259140, 0, -10946758301234, -361731480152]], ![![48140900929, 25896345221, 0, 0, -1549136664], ![-43031574, -596249, 0, 994, -1]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1508, 2088, 0, 19, 45], ![384, -84, 216, 0, 8]]], ![![![-761, 1044, 0, 8, 21], ![194, -40, 108, 0, 4]], ![![4399, -6003, 0, -48, -129], ![-1110, 250, -621, 0, -23]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![-1, 0, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![16, 2, 1, 2, 1]]
  ![![-11265398958422, -492985128159, 54800616190, -536592492194, -597626313393]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![64, 8, 4, 8, 4]], ![![-2, 0, 0, 2, 0], ![14, -27, -22, -6, -1]]]
 hmul := by decide
 f :=  ![![![![-249008754791665664496, 3180586852313812189688, 1654743839954492955517, -3359103317908550563626, -3292617459752761907218], ![-2989523313827198165688, 3191629563355938810000, 0, 15198236015980661000, 400704873096932173]], ![![16453762859092565, 1103043820611992939, 0, 0, 65579663229668574], ![1561420553087347, -690477373435142, 0, 0, -11320199574612]]]]
 g :=  ![![![![386, -265, -321, -70, -270]], ![![-7172, 7900, 1840, 2189, -602]]], ![![![-2504, 3952, -686, 1428, -30]], ![![15593, -7260, -14844, 1487, 3006]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-29, 21, 29, 36, 12])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![2477525262805708468802905859622830116575201031605206463961231, 108418983979997255831765033762583768364598269284080374018797, -12051939885053328353498969036651499432195859919376318730293, 118009265375252040870300184501030988199553323674656950216962, 131432033132007124394154076233743832633779632265363190012284])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

