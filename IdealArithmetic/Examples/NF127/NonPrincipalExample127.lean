import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF127.RI127

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
instance hq13 : Fact $ Nat.Prime 13 := by decide

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

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-574, 588, 579, 314, 1982], ![88, -94, -92, -50, -314]]]
  hmulB := by decide
  f := ![![![1149, -1059, 0, 0, -3964], ![-351, -3474, -1884, 6, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]], ![![383, -353, 0, 0, -1321], ![-117, -1158, -628, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-852, 588, 579, 314, 1982], ![134, -94, -92, -50, -314]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 1, 0], ![-574, 588, 579, 315, 1982], ![88, -94, -92, -50, -313]]]
  hmulB := by decide
  f := ![![![-938, 168, -613, -822, 1982], ![1095, 165, 3411, -3, 0]], ![![-940, 167, -614, -823, 1982], ![1099, 165, 3414, -3, 0]], ![![-940, 166, -614, -823, 1982], ![1100, 166, 3414, -3, 0]], ![![0, 0, 1, 1, 0], ![1, -1, -2, 0, 0]], ![![-314, 54, -205, -274, 661], ![369, 57, 1137, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 0, 1, 1, 0], ![-1539, 588, 579, 315, 1982], ![243, -94, -92, -50, -313]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 0, -5, 1, 0], ![-574, 588, 579, 309, 1982], ![88, -94, -92, -50, -319]]]
  hmulB := by decide
  f := ![![![-478711, 653418, -128101, 6863, 15856], ![-1043064, 1218558, -48301, -88, 0]], ![![-299204, 408402, -80064, 4289, 9910], ![-651936, 761629, -30184, -55, 0]], ![![-359036, 490062, -96074, 5147, 11892], ![-782304, 913914, -36223, -66, 0]], ![![-299193, 408382, -80060, 4289, 9910], ![-651912, 761590, -30183, -55, 0]], ![![-87037, 118803, -23287, 1247, 2883], ![-189645, 221556, -8773, -16, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-7, 0, 0, 11, 0], ![-2, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -5, 1, 0, 0], ![3, 0, -5, 1, 0], ![-1351, 588, 579, 309, 1982], ![216, -94, -92, -50, -319]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![13, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 0, -4, 1, 0], ![-574, 588, 579, 310, 1982], ![88, -94, -92, -50, -318]]]
  hmulB := by decide
  f := ![![![-301177, 74688, -480937, 125580, 21802], ![-958308, -17862, -1588210, -143, 0]], ![![-301189, 74691, -480977, 125590, 21802], ![-958346, -17862, -1588340, -143, 0]], ![![-301184, 74690, -480977, 125590, 21802], ![-958330, -17861, -1588340, -143, 0]], ![![9, -9, 2, 0, 0], ![29, -22, 1, 0, 0]], ![![-278012, 68944, -443942, 115920, 20125], ![-884600, -16486, -1466040, -132, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 13, 0, 0, 0], ![-10, 0, 13, 0, 0], ![-1, 0, 0, 13, 0], ![-12, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![2, -4, 1, 0, 0], ![3, 0, -4, 1, 0], ![-2750, 588, 579, 310, 1982], ![440, -94, -92, -50, -318]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)

def zeta1 := B.equivFun.symm ![522639039, 373208254, 253932382, 152549974, 973964986]

def zeta2 := B.equivFun.symm ![38713807666625831445398132749521321, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def alpha := B.equivFun.symm ![-6667430, 4728448, 3761190, 1848488, 12175998]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![522639037, 373208254, 253932382, 152549974, 973964986] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-150441983, 373208254, 253932382, 152549974, 973964986]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![522639039, 373208254, 253932382, 152549974, 973964986]
 hxeq :=  rfl
 m:= 2
 C := ![522639037, 373208254, 253932382, 152549974, 973964986]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![38713807666625831445398132749521320, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-56268338315489602232056769204517890, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![38713807666625831445398132749521321, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hxeq :=  rfl
 m:= 1
 C := ![38713807666625831445398132749521320, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
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
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-6667431, 4728448, 3761190, 1848488, 12175998] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-6281143, 4728448, 3761190, 1848488, 12175998]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-6667430, 4728448, 3761190, 1848488, 12175998]
 hxeq :=  rfl
 m:= 1
 C := ![-6667431, 4728448, 3761190, 1848488, 12175998]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![522639038, 373208254, 253932382, 152549974, 973964986] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-494982980, 373208254, 253932382, 152549974, 973964986]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![522639039, 373208254, 253932382, 152549974, 973964986]
 hxeq :=  rfl
 m:= 1
 C := ![522639038, 373208254, 253932382, 152549974, 973964986]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![38713807666625831445398132749521320, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-132754520339973097908053058849352625, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![38713807666625831445398132749521321, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hxeq :=  rfl
 m:= 1
 C := ![38713807666625831445398132749521320, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
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
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-6667431, 4728448, 3761190, 1848488, 12175998] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-10980915, 4728448, 3761190, 1848488, 12175998]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-6667430, 4728448, 3761190, 1848488, 12175998]
 hxeq :=  rfl
 m:= 1
 C := ![-6667431, 4728448, 3761190, 1848488, 12175998]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![522639036, 373208254, 253932382, 152549974, 973964986] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-614895394, 373208254, 253932382, 152549974, 973964986]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![522639039, 373208254, 253932382, 152549974, 973964986]
 hxeq :=  rfl
 m:= 3
 C := ![522639036, 373208254, 253932382, 152549974, 973964986]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![38713807666625831445398132749521315, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-141947283348644337130026067379123180, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![38713807666625831445398132749521321, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hxeq :=  rfl
 m:= 6
 C := ![38713807666625831445398132749521315, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  9
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log23Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-6667433, 4728448, 3761190, 1848488, 12175998] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-9310823, 4728448, 3761190, 1848488, 12175998]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-6667430, 4728448, 3761190, 1848488, 12175998]
 hxeq :=  rfl
 m:= 3
 C := ![-6667433, 4728448, 3761190, 1848488, 12175998]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![522639032, 373208254, 253932382, 152549974, 973964986] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1324283760, 373208254, 253932382, 152549974, 973964986]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![522639039, 373208254, 253932382, 152549974, 973964986]
 hxeq :=  rfl
 m:= 7
 C := ![522639032, 373208254, 253932382, 152549974, 973964986]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![38713807666625831445398132749521311, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-293120120885198116650284029114626518, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![38713807666625831445398132749521321, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hxeq :=  rfl
 m:= 10
 C := ![38713807666625831445398132749521311, 85215935613816451355167235822678670, 55982934604135449041367808920854075, 32276741251363137590086015270117385, 207518822613094638141568440363074990]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  10
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![-13, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 12
 C := ![-13, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  6
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] ![-6667438, 4728448, 3761190, 1848488, 12175998] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-18061218, 4728448, 3761190, 1848488, 12175998]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-6667430, 4728448, 3761190, 1848488, 12175998]
 hxeq :=  rfl
 m:= 8
 C := ![-6667438, 4728448, 3761190, 1848488, 12175998]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  3
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]] ![![2, 0, 0, 0, 0], ![40, 27, 18, 11, 70]]
  ![![-6667430, 4728448, 3761190, 1848488, 12175998]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![80, 54, 36, 22, 140]], ![![80, 54, 36, 22, 140], ![538, 504, 346, 204, 1306]]]
 hmul := by decide
 f :=  ![![![![410867660, -72522407, -73198911, -26231930, -186374933], ![-87884426, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![10001145, 0, 0, 0, 0]]]]
 g :=  ![![![![24519484392444, 17389466744996, 11832384059638, 7111901427725, 45402820068845]], ![![209104917001650, 148299325638999, 100907900309877, 60651094205989, 387200349329640]]], ![![![209104917001650, 148299325638999, 100907900309877, 60651094205989, 387200349329640]], ![![1783270219488889, 1264713306479652, 860553908124195, 517239343903619, 3302088070601353]]]]
 hle1 := by decide
 hle2 := by decide

lemma J2 : J ^ 2 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![5680453783, -2723711974, -3571773442, -1946139014, -11887509046])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![40361836033584012207962736373416606079185181, 28625023032266024058189980995879926936502830, 19477438336700166956474752701882523412401025, 11706991660938503323426989438545528946007265, 74738161282290023723164688025083459985227010])
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
