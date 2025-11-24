import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2

open BigOperators Classical Matrix Polynomial
noncomputable section

def zeta1 := B.equivFun.symm ![-3, 1, 1, -2]

def v := B.equivFun.symm ![-1, 0, 0, 0]

def alpha0 := B.equivFun.symm ![-1, 0, -1, 2]

def alpha1 := B.equivFun.symm ![-2, 0, -1, 2]


lemma isUnit_zeta1 : IsUnit zeta1 := by
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1, -1, -1, 2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_v : IsUnit v := by
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-1, 0, 0, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis)
    timesTableT_eq_Table _ (by norm_num)
  decide

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![3, -1, 0, 1]] i)))
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 1, 2, -5]] i)))

def MulJ00 : IdealMulEqCertificate O ℤ timesTableO (J0) J0
  ![![2, 0, 0, 0], ![3, -1, 0, 1]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![2, 0, 0, 0], ![1, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![6, -2, 0, 2]], ![![6, -2, 0, 2], ![-13, -2, 3, -4]]]
 hmul := by decide
 f :=  ![![![![-11459957, -12253048, -50509335, 85281661], ![31577420, -11284929, 112296, 0]], ![![0, 0, 0, 0], ![8588, -324, 9, 0]]], ![![![-7702552, -8235609, -33948706, 57320137], ![21224047, -7584909, 75477, 0]], ![![0, 0, 0, 0], ![5773, -218, 6, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![6, -1, 1, -2], ![2, 2, 0, 0]]], ![![![6, -1, 1, -2], ![2, 2, 0, 0]], ![![-13, -1, 0, 3], ![-3, -4, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate O ℤ timesTableO (J0*J0) J0
  ![![2, 0, 0, 0], ![1, 0, -1, 2]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![4, 0, 0, 0], ![3, 0, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![6, -2, 0, 2]], ![![2, 0, -2, 4], ![7, -6, -7, 14]]]
 hmul := by decide
 f :=  ![![![![145235, 155412, 641309, -1082743], ![-401220, 143403, -1485, 0]], ![![0, 0, 0, 0], ![-172, 6, 0, 0]]], ![![![73347, 78488, 323881, -546819], ![-202628, 72423, -750, 0]], ![![0, 0, 0, 0], ![-87, 3, 0, 0]]]]
 g :=  ![![![![907, -384, -786, 1650], ![72, -384, 0, 0]], ![![-12960, 5479, 11215, -23543], ![-1024, 5484, -3, 0]]], ![![![638, -270, -553, 1161], ![50, -270, 0, 0]], ![![-40766, 17238, 35285, -74071], ![-3231, 17253, -9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate O ℤ timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0], ![3, 0, 1, -1]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![4, 0, 0, 0], ![-1, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0], ![12, -4, 0, 4]], ![![6, 0, 2, -2], ![-11, -2, 1, 1]]]
 hmul := by decide
 f :=  ![![![![-371812745955, -389066587686, -1569220189207, 2656653104887], ![965140727358, -349557617311, 1507240903, 0]], ![![-114188274, -3772797, 0, 0], ![55798, -2496, 9, 0]]], ![![![247130812510, 258598832296, 1043005288520, -1765783576594], ![-641494985676, 232338613794, -1001809844, 0]], ![![75896916, 2507645, 0, 0], ![-37087, 1659, -6, 0]]]]
 g :=  ![![![![47, 24, -3, -6], ![-12, 48, 0, 0]], ![![112, 57, -7, -14], ![-28, 116, 0, 0]]], ![![![41, 21, -2, -6], ![-10, 42, 0, 0]], ![![-40, -21, 4, 3], ![15, -41, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate O ℤ timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0], ![-1, 0, -1, 2]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![8, 0, 0, 0], ![3, 2, 3, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0], ![12, -4, 0, 4]], ![![-2, 0, -2, 4], ![1, -4, -7, 12]]]
 hmul := by decide
 f :=  ![![![![-294351, -308040, -1242311, 2103189], ![764088, -276745, 1197, 0]], ![![168, -42, 0, 0], ![8, 0, 0, 0]]], ![![![4191558, 4386492, 17690495, -29949392], ![-10880604, 3940846, -17045, 0]], ![![-2408, 602, 0, 0], ![-117, -3, 0, 0]]]]
 g :=  ![![![![-22937, 1459, 5767, -15570], ![3660, 9580, -14, 0]], ![![-34368, 2185, 8640, -23327], ![5486, 14354, -21, 0]]], ![![![-418, 26, 104, -282], ![70, 174, 0, 0]], ![![-24259, 1542, 6098, -16466], ![3877, 10131, -14, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate O ℤ timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0, 0], ![3, 2, 3, -5]] ![![2, 0, 0, 0], ![3, -1, 0, 1]]
  ![![-1, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![16, 0, 0, 0], ![24, -8, 0, 8]], ![![6, 4, 6, -10], ![-7, -2, -3, 11]]]
 hmul := by decide
 f :=  ![![![![-667422370580600, -692572358654189, -2770064199838464, 4694543618432544], ![1692424432672470, -616264853027445, 1244714282130, 0]], ![![-41614348804, 330266876, 0, 0], ![-25801, 1389, -7, 0]]]]
 g :=  ![![![![-4, 0, 2, -4]], ![![-10, 7, 7, -15]]], ![![![-4, 1, 1, -3]], ![![3, 4, 2, -5]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl

def MulJ10 : IdealMulEqCertificate O ℤ timesTableO (J1) J1
  ![![6, 0, 0, 0], ![-4, 1, 2, -5]] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![-2, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![36, 0, 0, 0], ![-24, 6, 12, -30]], ![![-24, 6, 12, -30], ![-14, -24, -25, 50]]]
 hmul := by decide
 f :=  ![![![![-75474319793, -45200166028, -60785745348, 127329263502], ![-83586782504, 59058987961, 15471405, 0]], ![![0, 0, 0, 0], ![-4018850, -7314, 3, 0]]]]
 g :=  ![![![![-9, 0, 3, -6]], ![![2, -4, -6, 13]]], ![![![2, -4, -6, 13]], ![![8, 4, 3, -4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl


namespace Sat2

instance hq3 : Fact $ Nat.Prime 3 := by decide
instance hq13 : Fact $ Nat.Prime 13 := by decide
instance hq23 : Fact $ Nat.Prime 23 := by decide

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
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

def R23 : IsOrderOf (5 : ZMod 23) 22 where
 m := 2
 P := ![2, 11]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 1, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-5, 1, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-1, 1, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-5, 1, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
 ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![16, -15, -17, 35], ![6, -8, -8, 17]]]
  hmulB := by decide
  f := ![![![142, -143, -62, 140], ![231, -18, -12, 0]], ![![142, -143, -62, 140], ![232, -18, -12, 0]], ![![72, -72, -31, 70], ![118, -8, -6, 0]], ![![48, -48, -21, 47], ![79, -5, -4, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 3, 0, 0], ![-2, 0, 3, 0], ![-1, 0, 0, 3]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![15, -15, -17, 35], ![7, -8, -8, 17]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 3 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![13, 0, 0, 0], ![-5, 1, 0, 0]]
 ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-5, 1, 0, 0], ![0, -5, 1, 0], ![16, -15, -21, 35], ![6, -8, -8, 13]]]
  hmulB := by decide
  f := ![![![-795, 186, 18, -35], ![-2028, 39, 13, 0]], ![![-810, 189, 18, -35], ![-2066, 39, 13, 0]], ![![7, -1, 0, 0], ![18, 1, 0, 0]], ![![-175, 42, 4, -8], ![-446, 11, 3, 0]]]
  g := ![![![1, 0, 0, 0], ![-8, 13, 0, 0], ![-1, 0, 13, 0], ![-3, 0, 0, 13]], ![![-1, 1, 0, 0], ![3, -5, 1, 0], ![4, -15, -21, 35], ![3, -8, -8, 13]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 13 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![13, 0, 0, 0], ![-1, 1, 0, 0]]
 ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![16, -15, -17, 35], ![6, -8, -8, 17]]]
  hmulB := by decide
  f := ![![![1638, -1594, -811, 1680], ![11297, -65, -624, 0]], ![![1638, -1594, -811, 1680], ![11298, -65, -624, 0]], ![![1502, -1461, -744, 1540], ![10362, -51, -572, 0]], ![![504, -490, -250, 517], ![3476, -14, -192, 0]]]
  g := ![![![1, 0, 0, 0], ![-12, 13, 0, 0], ![-12, 0, 13, 0], ![-4, 0, 0, 13]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![20, -15, -17, 35], ![10, -8, -8, 17]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 13 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![23, 0, 0, 0], ![-5, 1, 0, 0]]
 ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] where
  T := Table
  heq := timesTableT_eq_Table
  hieq := rfl
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-5, 1, 0, 0], ![0, -5, 1, 0], ![16, -15, -21, 35], ![6, -8, -8, 13]]]
  hmulB := by decide
  f := ![![![146921, -31737, -2099, 3850], ![667736, -4853, -2530, 0]], ![![120206, -25963, -1718, 3150], ![546320, -3956, -2070, 0]], ![![133567, -28853, -1908, 3500], ![607044, -4415, -2300, 0]], ![![31945, -6897, -457, 837], ![145186, -1039, -550, 0]]]
  g := ![![![1, 0, 0, 0], ![-18, 23, 0, 0], ![-21, 0, 23, 0], ![-5, 0, 0, 23]], ![![-1, 1, 0, 0], ![3, -5, 1, 0], ![24, -15, -21, 35], ![11, -8, -8, 13]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 23 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)



def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] ![-4, 1, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-2, 1, 1, -2]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 1, 1, -2]
 hxeq :=  rfl
 m:= 1
 C := ![-4, 1, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] ![-3, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] ![-3, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, -1, 2]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, -1, 2]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log03Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] ![-3, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, -1, 2]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, -1, 2]
 hxeq :=  rfl
 m:= 1
 C := ![-3, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] ![-10, 1, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 1, 1, -2]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 1, 1, -2]
 hxeq :=  rfl
 m:= 7
 C := ![-10, 1, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] ![-13, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 12
 C := ![-13, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  6
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] ![-8, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, -1, 2]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, -1, 2]
 hxeq :=  rfl
 m:= 7
 C := ![-8, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log13Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] ![-8, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, -1, 2]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, -1, 2]
 hxeq :=  rfl
 m:= 6
 C := ![-8, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] ![-10, 1, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-2, 1, 1, -2]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 1, 1, -2]
 hxeq :=  rfl
 m:= 7
 C := ![-10, 1, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] ![-13, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 12
 C := ![-13, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  6
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] ![-4, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![0, 0, -1, 2]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, -1, 2]
 hxeq :=  rfl
 m:= 3
 C := ![-4, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log23Mem : IdealMemCertificate O ℤ B I2
  ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] ![-4, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![0, 0, -1, 2]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, -1, 2]
 hxeq :=  rfl
 m:= 2
 C := ![-4, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] ![-17, 1, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-2, 1, 1, -2]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-3, 1, 1, -2]
 hxeq :=  rfl
 m:= 14
 C := ![-17, 1, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  21
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] ![-23, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1, 0, 0, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0]
 hxeq :=  rfl
 m:= 22
 C := ![-23, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] ![-11, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![0, 0, -1, 2]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, -1, 2]
 hxeq :=  rfl
 m:= 10
 C := ![-11, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] ![-11, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![0, 0, -1, 2]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 4
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-2, 0, -1, 2]
 hxeq :=  rfl
 m:= 9
 C := ![-11, 0, -1, 2]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  10
 hpow := by decide
 heql := by decide




end Sat2
