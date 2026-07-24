import IdealArithmetic.Examples.NF5_1_607500000_4.ClassGroupData5_1_607500000_4
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_607500000_4.RI5_1_607500000_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![5, 1, 0, 0, 0], ![0, 5, 1, 0, 0], ![0, 0, 6, 3, 0], ![2, -8, -6, 6, 18], ![2, -2, 3, 0, 3]]]
  hmulB := by decide  
  f := ![![![-147895, 2624951, 552087, 7506, -6804], ![912268, -16438401, -100998, 11718, 0]], ![![-24656, 437508, 92018, 1251, -1134], ![152087, -2739842, -16833, 1953, 0]], ![![-32877, 583405, 122703, 1668, -1512], ![202797, -3653504, -22444, 2604, 0]], ![![-90388, 1604128, 337381, 4585, -4158], ![557545, -10045645, -61700, 7161, 0]], ![![-138365, 2455597, 516471, 7023, -6365], ![853484, -15377859, -94495, 10962, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 31, 0, 0, 0], ![-6, 0, 31, 0, 0], ![-19, 0, 0, 31, 0], ![-29, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-1, 5, 1, 0, 0], ![-3, 0, 6, 3, 0], ![-18, -8, -6, 6, 18], ![-3, -2, 3, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![13, 1, 0, 0, 0], ![0, 13, 1, 0, 0], ![0, 0, 14, 3, 0], ![2, -8, -6, 14, 18], ![2, -2, 3, 0, 11]]]
  hmulB := by decide  
  f := ![![![-2982160, 99808546, 8095691, 60996, -29484], ![13977845, -469346139, -1706536, 99918, 0]], ![![-639028, 21387586, 1734796, 13071, -6318], ![2995223, -100574360, -365695, 21411, 0]], ![![-710057, 23764183, 1927565, 14523, -7020], ![3328147, -111750230, -406321, 23790, 0]], ![![-781057, 26140307, 2120288, 15973, -7722], ![3660935, -122923870, -446906, 26169, 0]], ![![-1564415, 52358577, 4246920, 31998, -15467], ![7332655, -246214348, -895234, 52416, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-13, 61, 0, 0, 0], ![-14, 0, 61, 0, 0], ![-16, 0, 0, 61, 0], ![-32, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-3, 13, 1, 0, 0], ![-4, 0, 14, 3, 0], ![-10, -8, -6, 14, 18], ![-6, -2, 3, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![17, 1, 0, 0, 0], ![0, 17, 1, 0, 0], ![0, 0, 18, 3, 0], ![2, -8, -6, 18, 18], ![2, -2, 3, 0, 15]]]
  hmulB := by decide  
  f := ![![![-1536893, 19332778, 1242500, -10926, -26244], ![5504274, -69652484, -311466, 88938, 0]], ![![-455410, 5728328, 368138, -3240, -7776], ![1631019, -20638130, -92232, 26352, 0]], ![![-426944, 5370284, 345137, -3036, -7290], ![1529070, -19348162, -86498, 24705, 0]], ![![-654631, 8234315, 529204, -4655, -11178], ![2344515, -29666746, -132634, 37881, 0]], ![![-1209381, 15212677, 977702, -8598, -20651], ![4331313, -54808514, -245078, 69984, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-17, 61, 0, 0, 0], ![-16, 0, 61, 0, 0], ![-26, 0, 0, 61, 0], ![-48, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-5, 17, 1, 0, 0], ![-6, 0, 18, 3, 0], ![-18, -8, -6, 18, 18], ![-12, -2, 3, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![-27064, 23656, 848, -864, -9562] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![4622, 23656, 848, -864, -9562]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-27037, 23656, 848, -864, -9562]
 hxeq :=  rfl
 m := 27
 C := ![-27064, 23656, 848, -864, -9562]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![-1193172, 1499625, -194433, -337974, -1287680] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1169017, 1499625, -194433, -337974, -1287680]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1193171, 1499625, -194433, -337974, -1287680]
 hxeq :=  rfl
 m := 1
 C := ![-1193172, 1499625, -194433, -337974, -1287680]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![-1060, 392, 34, 21, -95] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-28, 392, 34, 21, -95]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1032, 392, 34, 21, -95]
 hxeq :=  rfl
 m := 28
 C := ![-1060, 392, 34, 21, -95]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 16
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] ![-27065, 23656, 848, -864, -9562] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-437, 23656, 848, -864, -9562]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-27037, 23656, 848, -864, -9562]
 hxeq :=  rfl
 m := 28
 C := ![-27065, 23656, 848, -864, -9562]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 51
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] ![-1193217, 1499625, -194433, -337974, -1287680] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![469624, 1499625, -194433, -337974, -1287680]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1193171, 1499625, -194433, -337974, -1287680]
 hxeq :=  rfl
 m := 46
 C := ![-1193217, 1499625, -194433, -337974, -1287680]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 58
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] ![-1036, 392, 34, 21, -95] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-64, 392, 34, 21, -95]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1032, 392, 34, 21, -95]
 hxeq :=  rfl
 m := 4
 C := ![-1036, 392, 34, 21, -95]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] ![-27046, 23656, 848, -864, -9562] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![634, 23656, 848, -864, -9562]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-27037, 23656, 848, -864, -9562]
 hxeq :=  rfl
 m := 9
 C := ![-27046, 23656, 848, -864, -9562]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 12
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] ![-1193186, 1499625, -194433, -337974, -1287680] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![770821, 1499625, -194433, -337974, -1287680]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1193171, 1499625, -194433, -337974, -1287680]
 hxeq :=  rfl
 m := 15
 C := ![-1193186, 1499625, -194433, -337974, -1287680]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 28
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] ![-1076, 392, 34, 21, -95] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-70, 392, 34, 21, -95]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1032, 392, 34, 21, -95]
 hxeq :=  rfl
 m := 44
 C := ![-1076, 392, 34, 21, -95]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

end Sat5
