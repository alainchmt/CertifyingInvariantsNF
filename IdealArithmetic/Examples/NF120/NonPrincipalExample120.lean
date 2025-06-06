import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF120.RI120

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
instance hq29 : Fact $ Nat.Prime 29 := by decide

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

def R29 : IsOrderOf (2 : ZMod 29) 28 where
 m := 2
 P := ![2, 7]
 e := ![2, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![12, 0, 1, 2, 4]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![3, 0, 0, 0, 0], ![12, 0, 1, 2, 4]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![12, 0, 1, 2, 4], ![60, -45, 0, -10, 0], ![-60, 10, -25, -60, -120], ![-210, 190, 1, 40, 0], ![84, -75, 4, -6, 18]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![33710, -112123, -12338, -51150, -51900], ![27465, -7564, -382, -1, 0]], ![![33546, -111590, -12278, -50904, -51648], ![27336, -7528, -380, -1, 0]], ![![-16, 30, 2, 11, 8], ![-6, 2, 0, 0, 0]], ![![-33542, 111530, 12272, 50878, 51623], ![-27317, 7524, 380, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![4, 0, 1, 2, 4], ![20, -45, 0, -10, 0], ![-20, 10, -25, -60, -120], ![-70, 190, 1, 40, 0], ![28, -75, 4, -6, 18]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 5, 1, 10, 0], ![6, 5, -2, 7, 12], ![12, -18, 1, -8, -5]]]
  hmulB := by decide
  f := ![![![80, 165, 34, 408, -20], ![-93, 42, -132, 0, -12]], ![![38, 81, 17, 204, -10], ![-41, 21, -66, 0, -6]], ![![78, 155, 34, 388, -20], ![-88, 37, -126, 0, -12]], ![![40, 85, 17, 211, -10], ![-46, 23, -68, 0, -6]], ![![52, 109, 23, 272, -13], ![-58, 27, -88, 0, -8]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-2, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-9, 5, 1, 10, 0], ![-11, 5, -2, 7, 12], ![18, -18, 1, -8, -5]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 5, 2, 10, 0], ![6, 5, -2, 8, 12], ![12, -18, 1, -8, -4]]]
  hmulB := by decide
  f := ![![![31881, 99466, 33015, 173712, 288], ![-174548, 18051, -190872, -264, 0]], ![![10614, 33119, 10993, 57844, 96], ![-58112, 6017, -63558, -88, 0]], ![![21249, 66293, 22004, 115778, 192], ![-116338, 12035, -127215, -176, 0]], ![![5314, 16582, 5504, 28963, 48], ![-29094, 3016, -31824, -44, 0]], ![![14491, 45212, 15007, 78960, 131], ![-79338, 8203, -86760, -120, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 11, 0, 0, 0], ![-7, 0, 11, 0, 0], ![-2, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-4, 5, 2, 10, 0], ![-6, 5, -2, 8, 12], ![7, -18, 1, -8, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![29, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 5, -11, 10, 0], ![6, 5, -2, -5, 12], ![12, -18, 1, -8, -17]]]
  hmulB := by decide
  f := ![![![288475, 2554, -76068, 66700, 5520], ![753246, -21808, -200100, -13340, 0]], ![![188130, 1671, -49610, 43500, 3600], ![491232, -14210, -130500, -8700, 0]], ![![238312, 2112, -62839, 55100, 4560], ![622264, -18008, -165300, -11020, 0]], ![![22, -1, 1, -1, 0], ![58, 4, 3, 0, 0]], ![![258632, 2291, -68199, 59800, 4949], ![675322, -19549, -179400, -11960, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-18, 29, 0, 0, 0], ![-24, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![-26, 0, 0, 0, 29]], ![![-1, 1, 0, 0, 0], ![6, -11, 1, 0, 0], ![6, 5, -11, 10, 0], ![-12, 5, -2, -5, 12], ![26, -18, 1, -8, -17]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)

def zeta1 := B.equivFun.symm ![182324, 9067, 6907, 7553, 13056]

def zeta2 := B.equivFun.symm ![-72669884397944627058787560488909268342246905518, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def alpha := B.equivFun.symm ![-175286832746540796364, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![182322, 9067, 6907, 7553, 13056] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![60774, 9067, 6907, 7553, 13056]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![182324, 9067, 6907, 7553, 13056]
 hxeq :=  rfl
 m:= 2
 C := ![182322, 9067, 6907, 7553, 13056]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-72669884397944627058787560488909268342246905520, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-24223294799314875686262520162969756114082301840, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-72669884397944627058787560488909268342246905518, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m:= 2
 C := ![-72669884397944627058787560488909268342246905520, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
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
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-175286832746540796366, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-58428944248846932122, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-175286832746540796364, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hxeq :=  rfl
 m:= 2
 C := ![-175286832746540796366, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![182323, 9067, 6907, 7553, 13056] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![39408, 9067, 6907, 7553, 13056]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![182324, 9067, 6907, 7553, 13056]
 hxeq :=  rfl
 m:= 1
 C := ![182323, 9067, 6907, 7553, 13056]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-72669884397944627058787560488909268342246905520, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-83923022635056620774630968636878632456724200649, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-72669884397944627058787560488909268342246905518, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m:= 2
 C := ![-72669884397944627058787560488909268342246905520, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
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
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-175286832746540796366, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-36563091302326592300, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-175286832746540796364, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hxeq :=  rfl
 m:= 2
 C := ![-175286832746540796366, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![182322, 9067, 6907, 7553, 13056] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![3223, 9067, 6907, 7553, 13056]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![182324, 9067, 6907, 7553, 13056]
 hxeq :=  rfl
 m:= 2
 C := ![182322, 9067, 6907, 7553, 13056]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-72669884397944627058787560488909268342246905521, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-36406813500585645303534000582369536972244833008, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-72669884397944627058787560488909268342246905518, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m:= 3
 C := ![-72669884397944627058787560488909268342246905521, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
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
  ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-175286832746540796368, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-2412448623759105704, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-175286832746540796364, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hxeq :=  rfl
 m:= 4
 C := ![-175286832746540796368, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![182303, 9067, 6907, 7553, 13056] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-16763, 9067, 6907, 7553, 13056]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![182324, 9067, 6907, 7553, 13056]
 hxeq :=  rfl
 m:= 21
 C := ![182303, 9067, 6907, 7553, 13056]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  17
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![-72669884397944627058787560488909268342246905527, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-73657315215568578974323212439154518821917211757, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-72669884397944627058787560488909268342246905518, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m:= 9
 C := ![-72669884397944627058787560488909268342246905527, 82985971093890408022594220611166386447259808587, -3735936183153940820862254239694302055990969, 26147479080084701663246027607699450796542032423, 21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  10
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![-29, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 28
 C := ![-29, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  14
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![-175286832746540796382, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![17669518349834341662, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-175286832746540796364, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hxeq :=  rfl
 m:= 18
 C := ![-175286832746540796382, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  11
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]] ![![2, 0, 0, 0, 0], ![12, 1, 1, 2, 4]]
  ![![-175286832746540796364, -10347030789858541610, -6699466941848258956, -7823139234159720716, -13102657848843259256]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![24, 2, 2, 4, 8]], ![![24, 2, 2, 4, 8], ![120, 0, 6, 0, 0]]]
 hmul := by decide
 f :=  ![![![![19324184048290798433, -11002964441259362228, -1884054821233655593, -18788198296129383830, -36940491437389722116], ![16832413487589453651, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![-5471345772015423981, 0, 0, 0, 0]]]]
 g :=  ![![![![211634648193893, -107723351479138, 49247758873357, 48022243478474, 225422155622474]], ![![2482669213662912, -2901010573366097, -24097070242637, -954386055596758, -890929841407946]]], ![![![2482669213662912, -2901010573366097, -24097070242637, -954386055596758, -890929841407946]], ![![-16828644528438420, 14708941685534445, -1658088877540116, 1875778447689510, -4660732740144180]]]]
 hle1 := by decide
 hle2 := by decide

lemma J2 : J ^ 2 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![68078, -251247, -79053, -269863, -369426])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-32707014916392676823502412576923329918983295903666307693559684, -1930666925071420710533004967825244597131962159044631410841767, -1250062892720242287645494217143430672681366570779776837805005, -1459730474990433573349477125828298890409219249172968005906833, -2444843226337328222198209297348857493679866448050357471912496])
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
