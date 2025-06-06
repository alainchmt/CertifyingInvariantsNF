import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF66.RI66

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![5, 1, 0, 0, 0], ![0, 5, 1, 0, 0], ![0, 0, 6, 3, 0], ![2, -8, -6, 6, 18], ![2, -2, 3, 0, 3]]]
  hmulB := by decide
  f := ![![![-147895, 2624951, 552087, 7506, -6804], ![912268, -16438401, -100998, 11718, 0]], ![![-24656, 437508, 92018, 1251, -1134], ![152087, -2739842, -16833, 1953, 0]], ![![-32877, 583405, 122703, 1668, -1512], ![202797, -3653504, -22444, 2604, 0]], ![![-90388, 1604128, 337381, 4585, -4158], ![557545, -10045645, -61700, 7161, 0]], ![![-138365, 2455597, 516471, 7023, -6365], ![853484, -15377859, -94495, 10962, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 31, 0, 0, 0], ![-6, 0, 31, 0, 0], ![-19, 0, 0, 31, 0], ![-29, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-1, 5, 1, 0, 0], ![-3, 0, 6, 3, 0], ![-18, -8, -6, 6, 18], ![-3, -2, 3, 0, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![13, 1, 0, 0, 0], ![0, 13, 1, 0, 0], ![0, 0, 14, 3, 0], ![2, -8, -6, 14, 18], ![2, -2, 3, 0, 11]]]
  hmulB := by decide
  f := ![![![-2982160, 99808546, 8095691, 60996, -29484], ![13977845, -469346139, -1706536, 99918, 0]], ![![-639028, 21387586, 1734796, 13071, -6318], ![2995223, -100574360, -365695, 21411, 0]], ![![-710057, 23764183, 1927565, 14523, -7020], ![3328147, -111750230, -406321, 23790, 0]], ![![-781057, 26140307, 2120288, 15973, -7722], ![3660935, -122923870, -446906, 26169, 0]], ![![-1564415, 52358577, 4246920, 31998, -15467], ![7332655, -246214348, -895234, 52416, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-13, 61, 0, 0, 0], ![-14, 0, 61, 0, 0], ![-16, 0, 0, 61, 0], ![-32, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-3, 13, 1, 0, 0], ![-4, 0, 14, 3, 0], ![-10, -8, -6, 14, 18], ![-6, -2, 3, 0, 11]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![17, 1, 0, 0, 0], ![0, 17, 1, 0, 0], ![0, 0, 18, 3, 0], ![2, -8, -6, 18, 18], ![2, -2, 3, 0, 15]]]
  hmulB := by decide
  f := ![![![-1536893, 19332778, 1242500, -10926, -26244], ![5504274, -69652484, -311466, 88938, 0]], ![![-455410, 5728328, 368138, -3240, -7776], ![1631019, -20638130, -92232, 26352, 0]], ![![-426944, 5370284, 345137, -3036, -7290], ![1529070, -19348162, -86498, 24705, 0]], ![![-654631, 8234315, 529204, -4655, -11178], ![2344515, -29666746, -132634, 37881, 0]], ![![-1209381, 15212677, 977702, -8598, -20651], ![4331313, -54808514, -245078, 69984, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-17, 61, 0, 0, 0], ![-16, 0, 61, 0, 0], ![-26, 0, 0, 61, 0], ![-48, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-5, 17, 1, 0, 0], ![-6, 0, 18, 3, 0], ![-18, -8, -6, 18, 18], ![-12, -2, 3, 0, 15]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def zeta1 := B.equivFun.symm ![27037, -23656, -848, 864, 9562]

def zeta2 := B.equivFun.symm ![-1193171, 1499625, -194433, -337974, -1287680]

def alpha := B.equivFun.symm ![-1032, 392, 34, 21, -95]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![27033, -23656, -848, 864, 9562] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-4623, -23656, -848, 864, 9562]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![27037, -23656, -848, 864, 9562]
 hxeq :=  rfl
 m:= 4
 C := ![27033, -23656, -848, 864, 9562]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  18
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![-1193172, 1499625, -194433, -337974, -1287680] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![1169017, 1499625, -194433, -337974, -1287680]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1193171, 1499625, -194433, -337974, -1287680]
 hxeq :=  rfl
 m:= 1
 C := ![-1193172, 1499625, -194433, -337974, -1287680]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![-1060, 392, 34, 21, -95] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-28, 392, 34, 21, -95]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1032, 392, 34, 21, -95]
 hxeq :=  rfl
 m:= 28
 C := ![-1060, 392, 34, 21, -95]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  16
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] ![27004, -23656, -848, 864, 9562] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![436, -23656, -848, 864, 9562]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![27037, -23656, -848, 864, 9562]
 hxeq :=  rfl
 m:= 33
 C := ![27004, -23656, -848, 864, 9562]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  21
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] ![-1193217, 1499625, -194433, -337974, -1287680] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![469624, 1499625, -194433, -337974, -1287680]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1193171, 1499625, -194433, -337974, -1287680]
 hxeq :=  rfl
 m:= 46
 C := ![-1193217, 1499625, -194433, -337974, -1287680]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  58
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] ![-1036, 392, 34, 21, -95] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-64, 392, 34, 21, -95]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1032, 392, 34, 21, -95]
 hxeq :=  rfl
 m:= 4
 C := ![-1036, 392, 34, 21, -95]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] ![26985, -23656, -848, 864, 9562] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-635, -23656, -848, 864, 9562]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![27037, -23656, -848, 864, 9562]
 hxeq :=  rfl
 m:= 52
 C := ![26985, -23656, -848, 864, 9562]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  42
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] ![-1193186, 1499625, -194433, -337974, -1287680] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![770821, 1499625, -194433, -337974, -1287680]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1193171, 1499625, -194433, -337974, -1287680]
 hxeq :=  rfl
 m:= 15
 C := ![-1193186, 1499625, -194433, -337974, -1287680]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  28
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] ![-1076, 392, 34, 21, -95] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-70, 392, 34, 21, -95]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1032, 392, 34, 21, -95]
 hxeq :=  rfl
 m:= 44
 C := ![-1076, 392, 34, 21, -95]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  17
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![0, -6, 2, 2, 6]], ![![0, -6, 2, 2, 6], ![70, -84, 8, 15, 69]]]
 hmul := by decide
 f :=  ![![![![603293701959, -271666372867, -187179085472, 37015701145, 125025767580], ![519956518513, -146660911881, -1035430269, 0, -13687557]], ![![0, 0, 0, 0, 0], ![-59139, -215, -9, 0, -1]]], ![![![1853680236162, -834722100659, -575126460365, 113734443805, 384154175041], ![1597618405270, -450630319674, -3181463058, 0, -42056388]], ![![0, 0, 0, 0, 0], ![-181710, -660, -28, 0, -3]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 3, 0, 4, 7], ![0, 0, -2, 0, 0]]], ![![![-4, 3, 0, 4, 7], ![0, 0, -2, 0, 0]], ![![-3, 22, 0, 30, 55], ![5, -7, -15, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![4, 0, 0, 0, 0], ![-22, 20, 2, 0, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![0, -6, 2, 2, 6]], ![![12, -4, 0, 0, 2], ![-4, -8, 2, 5, 15]]]
 hmul := by decide
 f :=  ![![![![7960615882, -3584709522, -2469880271, 488434462, 1649754102], ![6860972542, -1935231435, -13662873, 0, -180747]], ![![0, 0, 0, 0, 0], ![-3462, -294, -6, 0, 0]]], ![![![-43734042216, 19693682000, 13569031543, -2683361907, -9063421312], ![-37692820149, 10631777055, 75061110, 0, 992988]], ![![0, 0, 0, 0, 0], ![19019, 1615, 33, 0, 0]]]]
 g :=  ![![![![15, 8, -1, -6, -14], ![0, 4, 0, 0, 0]], ![![953682, 682802, -59808, -461319, -1038405], ![-43907, 319233, -7785, 0, -5]]], ![![![391812, 280510, -24572, -189524, -426609], ![-18036, 131150, -3198, 0, -2]], ![![1700824, 1217721, -106664, -822727, -1851913], ![-78304, 569328, -13884, 0, -9]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![-22, 20, 2, 0, -7]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![0, -12, 4, 4, 12]], ![![-44, 40, 4, 0, -14], ![140, -184, 10, 23, 123]]]
 hmul := by decide
 f :=  ![![![![4783837728614383386, -2161824300958366849, -1476191515577872436, 310624259884158571, 980263588573567285], ![4130348206451044270, -1181590648829775107, -3584476372727803, 0, -20397499630599]], ![![202162486708, -1620064134, -1914334236, 0, 0], ![-53175951, -997317, -1419, 0, -3]]], ![![![4793953914081800573, -2166395822154759670, -1479313157239689176, 311281124268347769, 982336511785333166], ![4139082484424468558, -1184089310119774590, -3592056317919755, 0, -20440633386600]], ![![202589991429, -1623490017, -1918382400, 0, 0], ![-53288400, -999426, -1422, 0, -3]]]]
 g :=  ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-8, -33, 0, -8, -3], ![8, 16, 12, 0, 0]]], ![![![-4, 3, 0, 0, 0], ![-6, 4, 0, 0, 0]], ![![-27, -198, 0, -46, -14], ![61, 79, 69, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![-1032, 392, 34, 21, -95]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![0, -12, 4, 4, 12]], ![![12, -4, 0, 0, 2], ![-4, -8, 2, 5, 15]]]
 hmul := by decide
 f :=  ![![![![953084725213204, -430700499856980, -294101751776143, 61885675830229, 195297971454412], ![822889668994133, -235408426461957, -714133308938, 0, -4063855586]], ![![-320274724, 33054629, 39206943, 0, 0], ![4356327, 390684, 1548, 0, 0]]]]
 g :=  ![![![![-22, 23, -13, -1, -2]], ![![-141, 214, 0, -17, -225]]], ![![![-10, 16, 8, -10, -32]], ![![-130, 119, -59, -52, -33]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![1237, 12952, 15792, 1268, -39958])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![10676839, -4412835, -348407, -177106, 1177610])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

