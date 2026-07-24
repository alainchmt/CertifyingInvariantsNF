import IdealArithmetic.Examples.NF5_1_10125000000_17.ClassGroupData5_1_10125000000_17
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_10125000000_17.RI5_1_10125000000_17

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-9, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-9, 1, 0, 0, 0], ![0, -9, 1, 0, 0], ![0, 1, -9, 2, 0], ![0, 1, -1, -8, 2], ![15, -19, 0, 0, -10]]]
  hmulB := by decide  
  f := ![![![1612, -256, 3429, -704, -16], ![1969, 385, 4224, 88, 0]], ![![406, -62, 857, -176, -4], ![496, 99, 1056, 22, 0]], ![![1232, -195, 2643, -544, -12], ![1505, 298, 3256, 66, 0]], ![![402, -61, 844, -173, -4], ![491, 98, 1040, 22, 0]], ![![1314, -213, 2806, -576, -13], ![1605, 310, 3456, 72, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 11, 0, 0, 0], ![-7, 0, 11, 0, 0], ![-3, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![1, -9, 1, 0, 0], ![5, 1, -9, 2, 0], ![1, 1, -1, -8, 2], ![13, -19, 0, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![8, 1, 0, 0, 0], ![0, 8, 1, 0, 0], ![0, 1, 8, 2, 0], ![0, 1, -1, 9, 2], ![15, -19, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1069161, 1469157, 11061376, 2757444, -2024], ![-8152345, 356484, -84379836, 61732, 0]], ![![185944, 255528, 1923935, 479610, -352], ![-1417822, 62037, -14676417, 10736, 0]], ![![1022690, 1405289, 10580506, 2637570, -1936], ![-7798004, 340991, -80711601, 59048, 0]], ![![139448, 191622, 1442781, 359665, -264], ![-1063290, 46539, -11006016, 8052, 0]], ![![876362, 1204222, 9066701, 2260200, -1659], ![-6682254, 292239, -69163800, 50600, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-8, 61, 0, 0, 0], ![-58, 0, 61, 0, 0], ![-8, 0, 0, 61, 0], ![-50, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-2, 8, 1, 0, 0], ![-8, 1, 8, 2, 0], ![-2, 1, -1, 9, 2], ![-3, -19, 0, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 1, 3, 2, 0], ![0, 1, -1, 4, 2], ![15, -19, 0, 0, 2]]]
  hmulB := by decide  
  f := ![![![-11, -40, -160, -66, 18], ![44, -22, 561, -99, 0]], ![![-21, -39, -148, -58, 18], ![78, -22, 517, -99, 0]], ![![-20, -38, -145, -56, 18], ![74, -21, 506, -99, 0]], ![![-1, -2, -2, -1, 0], ![4, 4, 6, 0, 0]], ![![-3, -12, -44, -18, 5], ![12, -2, 153, -27, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 11, 0, 0, 0], ![-2, 0, 11, 0, 0], ![-1, 0, 0, 11, 0], ![-3, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-1, 1, 3, 2, 0], ![-1, 1, -1, 4, 2], ![6, -19, 0, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![22, 17, -3, 2, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3, 17, -3, 2, 4]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![31, 17, -3, 2, 4]
 hxeq :=  rfl
 m := 9
 C := ![22, 17, -3, 2, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-4295384860860502876347593465084835634, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-350868632930530368271411447720429175, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hxeq :=  rfl
 m := 5
 C := ![-4295384860860502876347593465084835634, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-19939143752836451, -872556877448547, 96994111614622, -949739541230382, -1057766086864789] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-591261397615224, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-19939143752836442, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hxeq :=  rfl
 m := 9
 C := ![-19939143752836451, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] ![-5, 17, -3, 2, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-3, 17, -3, 2, 4]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![31, 17, -3, 2, 4]
 hxeq :=  rfl
 m := 36
 C := ![-5, 17, -3, 2, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] ![-4295384860860502876347593465084835650, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1482683539386249181543469181685136352, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hxeq :=  rfl
 m := 21
 C := ![-4295384860860502876347593465084835650, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 55
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] ![-19939143752836475, -872556877448547, 96994111614622, -949739541230382, -1057766086864789] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![686915958462071, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-19939143752836442, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hxeq :=  rfl
 m := 33
 C := ![-19939143752836475, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 21
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![26, 17, -3, 2, 4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-3, 17, -3, 2, 4]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![31, 17, -3, 2, 4]
 hxeq :=  rfl
 m := 5
 C := ![26, 17, -3, 2, 4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![-4295384860860502876347593465084835631, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2160558893907211524223807497004562764, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4295384860860502876347593465084835629, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hxeq :=  rfl
 m := 2
 C := ![-4295384860860502876347593465084835631, 7985121332494519147874150758241985881, -2952269487519506460585879238362277861, 1275467727902054332373616598638592896, 48156740590741678429992868441786652]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] ![-19939143752836445, -872556877448547, 96994111614622, -949739541230382, -1057766086864789] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1217493049263209, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-19939143752836442, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hxeq :=  rfl
 m := 3
 C := ![-19939143752836445, -872556877448547, 96994111614622, -949739541230382, -1057766086864789]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

end Sat5
