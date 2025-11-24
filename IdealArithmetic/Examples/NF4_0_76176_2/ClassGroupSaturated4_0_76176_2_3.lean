import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2
import IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupSaturated4_0_76176_2_2

open BigOperators Classical Matrix Polynomial
noncomputable section

namespace Sat3

instance hq13 : Fact $ Nat.Prime 13 := by decide

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-5, 1, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-1, 1, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
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

lemma N0 : Nat.card (O ⧸ I0) = 13 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
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

lemma N1 : Nat.card (O ⧸ I1) = 13 :=
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] ![-10, 1, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 1, 1, -2]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] ![-8, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, -1, 2]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] ![-10, 1, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-2, 1, 1, -2]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
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
  ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] ![-4, 0, -1, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![0, 0, -1, 2]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
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
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  4
 hpow := by decide
 heql := by decide

end Sat3

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 1, 2, -5]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![3, -1, 0, 1]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulRJ0_1J1_1 : IdealMulEqCertificate O ℤ timesTableO (J0) J1
  ![![2, 0, 0, 0], ![3, -1, 0, 1]] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![6, 0, 0, 0], ![0, -1, -1, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![12, 0, 0, 0], ![-8, 2, 4, -10]], ![![18, -6, 0, 6], ![2, 13, 11, -23]]]
 hmul := by decide
 f :=  ![![![![11597040, 6949866, 9332922, -19547995], ![12827931, -9055080, -7140, 0]], ![![1179, 22, 0, 0], ![0, 0, 0, 0]]], ![![![-70090440, -42003766, -56406536, 118144641], ![-77529712, 54727298, 43154, 0]], ![![-7125, -132, 0, 0], ![1, 0, 0, 0]]]]
 g :=  ![![![![0, 8, 8, -16], ![-6, 6, 0, 0]], ![![0, -25, -25, 46], ![34, -19, -1, 0]]], ![![![0, -51, -51, 94], ![69, -36, -3, 0]], ![![0, 24, 24, -45], ![-28, 16, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![0, -1, -1, 3]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulRJ0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![1, 0, -1, 2]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ00]
 rfl
def MulRJ0_2J1_1 : IdealMulEqCertificate O ℤ timesTableO ((J0*J0)) J1
  ![![2, 0, 0, 0], ![1, 0, -1, 2]] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![6, 0, 0, 0], ![-2, 2, -2, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![12, 0, 0, 0], ![-8, 2, 4, -10]], ![![6, 0, -6, 12], ![4, 6, 8, -16]]]
 hmul := by decide
 f :=  ![![![![3330700, 1995923, 2679274, -5611595], ![3681609, -2598711, -2403, 0]], ![![-801, 22, 0, 0], ![0, 0, 0, 0]]], ![![![-7975, -4780, -6416, 13438], ![-8813, 6222, 6, 0]], ![![3, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![45, -27, -33, 65], ![9, 12, 0, 0]], ![![-33, 20, 26, -51], ![-5, -9, 0, 0]]], ![![![-5179, 3163, 3836, -7574], ![-1020, -1389, 15, 0]], ![![-3464, 2117, 2567, -5069], ![-684, -929, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-2, 2, -2, 2]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulRJ0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![3, 0, 1, -1]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ01]
 rfl
def MulRJ0_3J1_1 : IdealMulEqCertificate O ℤ timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0, 0], ![3, 0, 1, -1]] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![12, 0, 0, 0], ![6, 2, 8, -12]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![24, 0, 0, 0], ![-16, 4, 8, -20]], ![![18, 0, 6, -6], ![-4, 14, 14, -32]]]
 hmul := by decide
 f :=  ![![![![-248604757, -148918172, -200200822, 419368572], ![-275290605, 194473401, 72513, 0]], ![![-48342, -230, 0, 0], ![0, 0, 0, 0]]], ![![![-869222360, -520677908, -699982708, 1466281437], ![-962526841, 679957342, 253534, 0]], ![![-169029, -805, 0, 0], ![-3, 0, 0, 0]]]]
 g :=  ![![![![71357354781, -15360680021, -16602324918, 45187392368], ![-23137044918, -12811342992, 320628, 0]], ![![-51508119186, 11087851276, 11984111983, -32617767275], ![16701090884, 9247654762, -231440, 0]]], ![![![47583815007, -10243089290, -11071065625, 30132682549], ![-15428667003, -8543093796, 213807, 0]], ![![-11853723172, 2551681593, 2757940847, -7506427915], ![3843473830, 2128191463, -53262, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![6, 2, 8, -12]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulRJ0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![-1, 0, -1, 2]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ02]
 rfl
def MulRJ0_4J1_1 : IdealMulEqCertificate O ℤ timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0, 0], ![-1, 0, -1, 2]] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![12, 0, 0, 0], ![10, -4, -2, 8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![24, 0, 0, 0], ![-16, 4, 8, -20]], ![![-6, 0, -6, 12], ![12, 4, 4, -6]]]
 hmul := by decide
 f :=  ![![![![1859129, 1113622, 1496990, -3135702], ![2058279, -1454007, -591, 0]], ![![-378, 4, 0, 0], ![0, 0, 0, 0]]], ![![![160346, 96045, 129108, -270438], ![177524, -125403, -51, 0]], ![![-35, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![-207956, -220706, -524896, 890536], ![581448, -207288, 18, 0]], ![![138978, 147503, 350798, -595164], ![-388588, 138534, -12, 0]]], ![![![34803, 36938, 87847, -149041], ![-97311, 34692, -3, 0]], ![![-115124, -122183, -290583, 493002], ![321890, -114755, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![10, -4, -2, 8]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulRJ0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0, 0], ![3, 2, 3, -5]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ03]
 rfl
def MulRJ0_5J1_1 : IdealMulEqCertificate O ℤ timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0, 0], ![3, 2, 3, -5]] ![![6, 0, 0, 0], ![-4, 1, 2, -5]]
  ![![24, 0, 0, 0], ![-14, 16, 14, -34]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![48, 0, 0, 0], ![-32, 8, 16, -40]], ![![18, 12, 18, -30], ![-16, 16, 20, -50]]]
 hmul := by decide
 f :=  ![![![![566914390104, 339480700899, 456621455766, -956491643305], ![627920711433, -443706605574, -88480590, 0]], ![![-117683640, -145282, 0, 0], ![42, 0, 0, 0]]], ![![![-658166148431, -394124243942, -530120226408, 1110450593382], ![-728992178318, 515126574176, 102722616, 0]], ![![136626255, 168667, 0, 0], ![-49, 0, 0, 0]]]]
 g :=  ![![![![33438785589755, 6879862738788, 20021341835107, -27348310077297], ![35503172245188, -15274322116800, -1320, 0]], ![![2823337031187453, 580887460395050, 1690461983597344, -2309099903596170], ![2997639392597048, -1289656860979608, -111466, 0]]], ![![![4281819739521204, 880962976394549, 2563722789848067, -3501937401921215], ![4546163416342131, -1955869293517866, -169047, 0]], ![![5681784573073642, 1168998732601321, 3401946247887802, -4646915357611602], ![6032556888658942, -2595351662352069, -224318, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![-14, 16, 14, -34]] i)) := by
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulRJ0_5J1_1]
 rfl
