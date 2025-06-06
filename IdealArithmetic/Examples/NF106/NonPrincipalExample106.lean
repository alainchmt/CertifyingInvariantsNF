import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF106.RI106

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
instance hq41 : Fact $ Nat.Prime 41 := by decide
instance hq61 : Fact $ Nat.Prime 61 := by decide
instance hq31 : Fact $ Nat.Prime 31 := by decide

def R41 : IsOrderOf (6 : ZMod 41) 40 where
 m := 2
 P := ![2, 5]
 e := ![3, 1]
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

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![31, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 1, -1, 4, 0], ![0, 0, -1, -5, 1], ![58, 1, 4, -11, -3]]]
  hmulB := by decide
  f := ![![![2050, -5788, 4867, -22072, 280], ![21173, 651, 160208, -8680, 0]], ![![1942, -5483, 4610, -20914, 266], ![20058, 620, 151776, -8246, 0]], ![![1528, -4320, 3633, -16486, 210], ![15782, 497, 119629, -6510, 0]], ![![926, -2604, 2190, -9935, 126], ![9564, 318, 72114, -3906, 0]], ![![1986, -5602, 4710, -21360, 271], ![20512, 630, 155040, -8400, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-28, 31, 0, 0, 0], ![-22, 0, 31, 0, 0], ![-14, 0, 0, 31, 0], ![-30, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![-2, 1, -1, 4, 0], ![2, 0, -1, -5, 1], ![6, 1, 4, -11, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![41, 0, 0, 0, 0], ![-12, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-12, 1, 0, 0, 0], ![0, -12, 1, 0, 0], ![0, 1, -10, 4, 0], ![0, 0, -1, -14, 1], ![58, 1, 4, -11, -12]]]
  hmulB := by decide
  f := ![![![-66287, 20650, -175984, 77736, -504], ![-226484, -8692, -724470, 20664, 0]], ![![-46907, 14611, -124513, 55006, -357], ![-160268, -6150, -512582, 14637, 0]], ![![-33212, 10350, -88182, 38944, -252], ![-113476, -4345, -363014, 10332, 0]], ![![-19308, 6024, -51314, 22667, -147], ![-65970, -2519, -211242, 6027, 0]], ![![-38808, 12088, -103015, 45504, -295], ![-132596, -5089, -424080, 12096, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-29, 41, 0, 0, 0], ![-20, 0, 41, 0, 0], ![-12, 0, 0, 41, 0], ![-24, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![8, -12, 1, 0, 0], ![3, 1, -10, 4, 0], ![4, 0, -1, -14, 1], ![9, 1, 4, -11, -12]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![61, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-6, 1, 0, 0, 0], ![0, -6, 1, 0, 0], ![0, 1, -4, 4, 0], ![0, 0, -1, -8, 1], ![58, 1, 4, -11, -6]]]
  hmulB := by decide
  f := ![![![31507, -36757, 127334, -133224, 645], ![320311, 5185, 1952976, -39345, 0]], ![![29365, -34270, 118742, -124240, 602], ![298535, 4880, 1821216, -36722, 0]], ![![14623, -17077, 59179, -61928, 301], ![148663, 2441, 907680, -18361, 0]], ![![29403, -34303, 118849, -124347, 602], ![298921, 4881, 1822848, -36722, 0]], ![![27894, -32534, 112721, -117936, 571], ![283580, 4645, 1728864, -34830, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-55, 61, 0, 0, 0], ![-25, 0, 61, 0, 0], ![-57, 0, 0, 61, 0], ![-54, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![5, -6, 1, 0, 0], ![-3, 1, -4, 4, 0], ![7, 0, -1, -8, 1], ![14, 1, 4, -11, -6]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![-94349, -49754, -42647, -22399, -6349]

def zeta2 := B.equivFun.symm ![4436583, 499539, 81866, -425045, -249983]

def alpha := B.equivFun.symm ![-3, 30, -3, 4, -3]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] ![-94351, -49754, -42647, -22399, -6349] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![88421, -49754, -42647, -22399, -6349]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-94349, -49754, -42647, -22399, -6349]
 hxeq :=  rfl
 m:= 2
 C := ![-94351, -49754, -42647, -22399, -6349]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  24
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] ![4436569, 499539, 81866, -425045, -249983] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![67695, 499539, 81866, -425045, -249983]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4436583, 499539, 81866, -425045, -249983]
 hxeq :=  rfl
 m:= 14
 C := ![4436569, 499539, 81866, -425045, -249983]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  22
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] ![-4, 30, -3, 4, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-24, 30, -3, 4, -3]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 30, -3, 4, -3]
 hxeq :=  rfl
 m:= 1
 C := ![-4, 30, -3, 4, -3]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![-94364, -49754, -42647, -22399, -6349] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![63966, -49754, -42647, -22399, -6349]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-94349, -49754, -42647, -22399, -6349]
 hxeq :=  rfl
 m:= 15
 C := ![-94364, -49754, -42647, -22399, -6349]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  37
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![4436576, 499539, 81866, -425045, -249983] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-14323, 499539, 81866, -425045, -249983]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4436583, 499539, 81866, -425045, -249983]
 hxeq :=  rfl
 m:= 7
 C := ![4436576, 499539, 81866, -425045, -249983]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  39
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![-34, 30, -3, 4, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-20, 30, -3, 4, -3]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 30, -3, 4, -3]
 hxeq :=  rfl
 m:= 31
 C := ![-34, 30, -3, 4, -3]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  28
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![-94372, -49754, -42647, -22399, -6349] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![87342, -49754, -42647, -22399, -6349]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-94349, -49754, -42647, -22399, -6349]
 hxeq :=  rfl
 m:= 23
 C := ![-94372, -49754, -42647, -22399, -6349]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  57
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![4436532, 499539, 81866, -425045, -249983] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![207244, 499539, 81866, -425045, -249983]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![4436583, 499539, 81866, -425045, -249983]
 hxeq :=  rfl
 m:= 51
 C := ![4436532, 499539, 81866, -425045, -249983]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  53
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] ![-6, 30, -3, 4, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-27, 30, -3, 4, -3]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 30, -3, 4, -3]
 hxeq :=  rfl
 m:= 3
 C := ![-6, 30, -3, 4, -3]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  6
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]] ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-10, -14, 4, 0, 2]], ![![-10, -14, 4, 0, 2], ![-265, 123, 13, 43, -4]]]
 hmul := by decide
 f :=  ![![![![-1289195021830, 859282094960, -90282808812, 162007939555, -69869209239], ![90282808812, 52041183865, -16751419956, -198908013, 0]], ![![0, 0, 0, 0, 0], ![911588, -54317, -5417, 3, 0]]], ![![![3867091500868, -2577517311234, 270813861807, -485961794444, 209580878461], ![-270813861807, -156103627772, 50247846645, 596647878, 0]], ![![0, 0, 0, 0, 0], ![-2734413, 162931, 16249, -9, 0]]]]
 g :=  ![![![![52, 36, 22, 0, 0], ![-44, 8, -4, 0, 0]], ![![48, 30, 21, -3, 0], ![-42, 10, -4, 0, 0]]], ![![![48, 30, 21, -3, 0], ![-42, 10, -4, 0, 0]], ![![-4816, -3490, -2179, -30, 0], ![4379, -780, 388, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]]
  ![![4, 0, 0, 0, 0], ![-1, -17, 1, -3, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-10, -14, 4, 0, 2]], ![![-6, 2, 2, 2, 0], ![15, 49, 7, 9, -2]]]
 hmul := by decide
 f :=  ![![![![173632846183, -115739993622, 12144401688, -21827315979, 9406668735], ![-12144401688, -7008076086, 2257960299, 26147385, 0]], ![![0, 0, 0, 0, 0], ![-342436, 2934, -4, 0, 0]]], ![![![694169648445, -462718848744, 48552305838, -87263790195, 37607077653], ![-48552305838, -28017704138, 9027137097, 104535066, 0]], ![![0, 0, 0, 0, 0], ![-1369031, 11730, -16, 0, 0]]]]
 g :=  ![![![![3654324388107, -145003942848, -114184670885, -416045718479, -70328234815], ![-48990336172, -126432885582, 420454, 18, 0]], ![![-10128592247570, 401903513608, 316482569549, 1153142685565, 194926869724], ![135785192144, 350430615549, -1165361, -51, 0]]], ![![![-6110125216789, 242450355713, 190919733129, 695639238843, 117590633822], ![81913113518, 211399065978, -703010, -30, 0]], ![![10886515129305, -431977966366, -340164970343, -1239432389590, -209513253620], ![-145946002425, -376653349713, 1252565, 57, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![-1, -17, 1, -3, 2]] ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]]
  ![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![-20, -28, 8, 0, 4]], ![![-2, -34, 2, -6, 4], ![-575, 99, 5, 59, -2]]]
 hmul := by decide
 f :=  ![![![![-689572453279286222522447, 460452645111509950904027, -46910899680763979054332, 87328250915965972544130, -37050151892805540066735], ![46910899680763979054332, 27777260722888425607564, -9123548981466937116022, -45142810945925087549, 0]], ![![-680334777252593874, -5854319971386894, 7078347354987, 0, 0], ![7042124814, 60377943, -11185, 3, 0]]], ![![![689572453180794769566187, -460452645045743620159631, 46910899674063707535258, -87328250903492901330308, 37050151887513676572450], ![-46910899674063707535258, -27777260718921006731227, 9123548980163823003750, 45142810939477351681, 0]], ![![680334777155421836, 5854319970550723, -7078347353976, 0, 0], ![-7042124813, -60377943, 11185, -3, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-353, -126, -58, 39, 0], ![232, -68, 36, 0, 0]]], ![![![-350, -127, -59, 38, 0], ![230, -68, 36, 0, 0]], ![![824, 320, 134, -111, 0], ![-527, 186, -94, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![-3, 1, 1, 1, 0]] ![![2, 0, 0, 0, 0], ![-5, -7, 2, 0, 1]]
  ![![-3, 30, -3, 4, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![-20, -28, 8, 0, 4]], ![![-6, 2, 2, 2, 0], ![15, 49, 7, 9, -2]]]
 hmul := by decide
 f :=  ![![![![-640166110980752, 427461170750013, -43551699756614, 81067826049107, -34395560627270], ![43551699756614, 25786595720630, -8470260736651, -43131236568, 0]], ![![20065663746, 2562194548, -115643835, 0, 0], ![2348481, -20097, 33, 0, 0]]]]
 g :=  ![![![![-22, 18, 1, 11, -3]], ![![84, -5, 2, -14, -1]]], ![![![118, 2, 2, -16, -4]], ![![-5, -36, 2, -13, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![6540991, -13889124, 1249807, -2240413, 1315887])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1728271045, -771064391, -677595114, -313890231, -96712103])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

