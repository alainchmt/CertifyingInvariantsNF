
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, -24, -16, 20, -37]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![79, -24, -16, 20, -37]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![79, -24, -16, 20, -37], ![-256, 78, 52, -65, 120], ![830, -253, -169, 211, -390], ![-708, 215, 144, -180, 332], ![102, -31, -21, 26, -48]]]
  hmulB := by decide  
  f := ![![![6, -1, -1, 0, 1]], ![![4, 4, 0, -1, 0]], ![![-2, 3, 1, -1, -6]], ![![-16, -1, 0, -2, -4]], ![![-1, -6, -2, 0, 2]]]
  g := ![![![58, -24, -16, 20, -37], ![-188, 78, 52, -65, 120], ![610, -253, -169, 211, -390], ![-520, 215, 144, -180, 332], ![75, -31, -21, 26, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, -20, -13, 16, -29]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![62, -20, -13, 16, -29]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![62, -20, -13, 16, -29], ![-200, 62, 41, -52, 96], ![664, -197, -135, 167, -312], ![-566, 173, 115, -145, 262], ![76, -28, -17, 21, -39]]]
  hmulB := by decide  
  f := ![![![3588, -1246, -155, 489, -1210]], ![![-4351, 1511, 188, -593, 1467]], ![![10550, -3665, -456, 1438, -3558]], ![![-6463, 2244, 279, -881, 2179]], ![![-1459, 507, 63, -199, 492]]]
  g := ![![![31, -20, -13, 16, -29], ![-100, 62, 41, -52, 96], ![332, -197, -135, 167, -312], ![-283, 173, 115, -145, 262], ![38, -28, -17, 21, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, -1, -1, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-7, 1, -1, -1, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-7, 1, -1, -1, 0], ![-2, -7, -1, -4, -6], ![-56, -11, -18, -13, -24], ![-92, -31, -17, -36, -36], ![-14, -13, -8, -7, -17]]]
  hmulB := by decide  
  f := ![![![-36, 17, 10, -1, -18]], ![![-91, -24, 7, 5, -12]], ![![-31, -64, -13, 8, 24]], ![![47, -11, -10, 0, 18]], ![![50, 60, 9, -8, -17]]]
  g := ![![![-3, 1, -1, -1, 0], ![5, -7, -1, -4, -6], ![-7, -11, -18, -13, -24], ![-4, -31, -17, -36, -36], ![7, -13, -8, -7, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![79, -24, -16, 20, -37]] ![![62, -20, -13, 16, -29]]
  ![![-15058, 4580, 3078, -3837, 7080]] where
 M := ![![![-15058, 4580, 3078, -3837, 7080]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-15058, 4580, 3078, -3837, 7080]] ![![62, -20, -13, 16, -29]]
  ![![2904018, -883287, -593611, 739983, -1365388]] where
 M := ![![![2904018, -883287, -593611, 739983, -1365388]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2904018, -883287, -593611, 739983, -1365388]] ![![-7, 1, -1, -1, 0]]
  ![![-34282340, 10427319, 7007660, -8735599, 16118594]] where
 M := ![![![-34282340, 10427319, 7007660, -8735599, 16118594]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-34282340, 10427319, 7007660, -8735599, 16118594]] ![![-7, 1, -1, -1, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![404707574, -123095986, -82726428, 103124890, -190282288]]]
 hmul := by decide  
 g := ![![![![202353787, -61547993, -41363214, 51562445, -95141144]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, -1, 1, -2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, -2, -1, 1, -2]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, -2, -1, 1, -2], ![-14, 3, 2, -4, 6], ![40, -14, -11, 8, -24], ![-50, 8, 4, -15, 10], ![-2, -4, -2, 0, -5]]]
  hmulB := by decide  
  f := ![![![-345, 120, 15, -47, 116]], ![![278, -97, -12, 38, -94]], ![![-676, 234, 29, -92, 228]], ![![184, -64, -8, 25, -62]], ![![-21, 8, 1, -3, 7]]]
  g := ![![![1, -2, -1, 1, -2], ![-4, 3, 2, -4, 6], ![16, -14, -11, 8, -24], ![-10, 8, 4, -15, 10], ![1, -4, -2, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 39, 10, -5, -16]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-3, 39, 10, -5, -16]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-3, 39, 10, -5, -16], ![-138, -34, 14, 9, -30], ![-222, -173, -21, 21, 54], ![38, -111, -32, 14, 50], ![200, 120, 4, -18, -11]]]
  hmulB := by decide  
  f := ![![![-589, 173, 116, -151, 268]], ![![614, -196, -132, 155, -302]], ![![-2106, 599, 401, -543, 930]], ![![1228, -457, -310, 300, -698]], ![![-682, 180, 120, -178, 281]]]
  g := ![![![13, 39, 10, -5, -16], ![-32, -34, 14, 9, -30], ![-124, -173, -21, 21, 54], ![-30, -111, -32, 14, 50], ![86, 120, 4, -18, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![447, 156, 115, 159, 212]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![447, 156, 115, 159, 212]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![447, 156, 115, 159, 212], ![2014, 703, 518, 716, 954], ![9064, 3166, 2333, 3224, 4296], ![17298, 6040, 4452, 6153, 8198], ![5082, 1774, 1308, 1808, 2409]]]
  hmulB := by decide  
  f := ![![![291, -86, -61, 75, -138]], ![![-124, 39, 26, -32, 58]], ![![1230, -374, -257, 318, -584]], ![![-700, 212, 144, -179, 330]], ![![332, -98, -68, 84, -155]]]
  g := ![![![-279, 156, 115, 159, 212], ![-1256, 703, 518, 716, 954], ![-5658, 3166, 2333, 3224, 4296], ![-10796, 6040, 4452, 6153, 8198], ![-3172, 1774, 1308, 1808, 2409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, -2, -1, 1, -2]] ![![-3, 39, 10, -5, -16]]
  ![![127, 7, -17, -4, 30]] where
 M := ![![![127, 7, -17, -4, 30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![127, 7, -17, -4, 30]] ![![447, 156, 115, 159, 212]]
  ![![47, -29, 2, 25, 48]] where
 M := ![![![47, -29, 2, 25, 48]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![47, -29, 2, 25, 48]] ![![447, 156, 115, 159, 212]]
  ![![657117, 229429, 169133, 233766, 311472]] where
 M := ![![![657117, 229429, 169133, 233766, 311472]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![657117, 229429, 169133, 233766, 311472]] ![![447, 156, 115, 159, 212]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![7915407789, 2763771885, 2037131574, 2815541133, 3751529154]]]
 hmul := by decide  
 g := ![![![![2638469263, 921257295, 679043858, 938513711, 1250509718]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2, I3N2, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N2
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 1, 0, -1, 4]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-11, 1, 0, -1, 4]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-11, 1, 0, -1, 4], ![30, -8, -2, 3, -6], ![-42, 29, 3, -9, 18], ![38, -5, 0, 4, -14], ![-4, -8, 0, 2, -3]]]
  hmulB := by decide  
  f := ![![![-67, 21, 14, -17, 32]], ![![31, -9, -6, 8, -14]], ![![-194, 61, 41, -49, 94]], ![![100, -27, -18, 26, -42]], ![![-16, 6, 4, -4, 9]]]
  g := ![![![-2, 1, 0, -1, 4], ![8, -8, -2, 3, -6], ![-13, 29, 3, -9, 18], ![7, -5, 0, 4, -14], ![0, -8, 0, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-11, 1, 0, -1, 4]] ![![-11, 1, 0, -1, 4]]
  ![![97, -46, -2, 18, -48]] where
 M := ![![![97, -46, -2, 18, -48]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![97, -46, -2, 18, -48]] ![![-11, 1, 0, -1, 4]]
  ![![-1487, 701, 86, -241, 520]] where
 M := ![![![-1487, 701, 86, -241, 520]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-1487, 701, 86, -241, 520]] ![![-11, 1, 0, -1, 4]]
  ![![22537, -7556, -1144, 2892, -6792]] where
 M := ![![![22537, -7556, -1144, 2892, -6792]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![22537, -7556, -1144, 2892, -6792]] ![![-11, 1, 0, -1, 4]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-289475, 89685, 11680, -36925, 94780]]]
 hmul := by decide  
 g := ![![![![-57895, 17937, 2336, -7385, 18956]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 4, 3, 3, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6, 1, 4, 6], [2, 1, 5, 0, 5], [0, 4, 4, 4, 4], [4, 2, 4, 6, 6], [0, 1]]
 g := ![![[6, 3, 1], []], ![[4, 0, 6, 5, 4, 1, 1, 3], [0, 1, 4, 0, 3, 6, 2, 6]], ![[2, 2, 5, 2, 5, 3, 6, 5], [6, 1, 1, 3, 4, 5, 4, 6]], ![[6, 4, 1, 6, 1, 3, 0, 4], [0, 1, 0, 6, 3, 0, 6, 1]], ![[1, 4, 5, 6, 5, 3, 6, 5], [4, 2, 4, 5, 4, 1, 1, 6]]]
 h' := ![![[4, 6, 1, 4, 6], [0, 0, 0, 1], [0, 1]], ![[2, 1, 5, 0, 5], [1, 4, 5, 1, 5], [4, 6, 1, 4, 6]], ![[0, 4, 4, 4, 4], [5, 5, 5, 3, 6], [2, 1, 5, 0, 5]], ![[4, 2, 4, 6, 6], [0, 3, 3, 2, 6], [0, 4, 4, 4, 4]], ![[0, 1], [6, 2, 1, 0, 4], [4, 2, 4, 6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4, 4, 1], [], [], []]
 b := ![[], [6, 3, 2, 5, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 4, 3, 3, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-149052003578695, -52290568547329, -38535368024944, -53056338895574, -71001049505337]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21293143368385, -7470081221047, -5505052574992, -7579476985082, -10143007072191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-561, 169, 120, -147, 268]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-561, 169, 120, -147, 268]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![4, 6, 7, 1, 0], ![4, 7, 4, 0, 1]] where
  M :=![![![-561, 169, 120, -147, 268], ![1850, -560, -392, 481, -882], ![-6094, 1841, 1275, -1577, 2886], ![5230, -1593, -1094, 1346, -2486], ![-812, 246, 160, -204, 375]]]
  hmulB := by decide  
  f := ![![![97, -13, -18, -1, 32]], ![![254, 146, 2, -23, -6]], ![![-94, 223, 75, -23, -138]], ![![84, 218, 47, -27, -88]], ![![154, 150, 18, -21, -35]]]
  g := ![![![-95, -75, 7, -147, 268], ![314, 248, -21, 481, -882], ![-1030, -809, 70, -1577, 2886], ![890, 703, -52, 1346, -2486], ![-136, -105, 8, -204, 375]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10, 2], [0, 0, 9], [0, 1]]
 g := ![![[2, 0, 3], [8, 8, 1], []], ![[1, 2, 3, 10], [1, 6], [6, 4]], ![[0, 3, 4, 3], [3, 0, 8, 9], [10, 4]]]
 h' := ![![[8, 10, 2], [10, 2, 5], [0, 0, 1], [0, 1]], ![[0, 0, 9], [4, 1, 4], [0, 5], [8, 10, 2]], ![[0, 1], [1, 8, 2], [7, 6, 10], [0, 0, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 1], []]
 b := ![[], [0, 5, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 1, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144651869115, -67462720733, -49567270463, -53922942187, -93383843061]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![40415933807, 82705621256, 63766245190, -53922942187, -93383843061]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -5, -1, 0, 4]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-3, -5, -1, 0, 4]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-3, -5, -1, 0, 4], ![32, 2, -4, 1, 0], ![2, 37, 9, -11, 6], ![20, 9, 0, 4, -20], ![-34, -18, 0, 2, 3]]]
  hmulB := by decide  
  f := ![![![-863, 299, 37, -118, 290]], ![![111, -39, -5, 15, -38]], ![![-1248, 431, 53, -171, 418]], ![![-36, 9, 0, -6, 8]], ![![-173, 59, 7, -24, 57]]]
  g := ![![![0, -5, -1, 0, 4], ![6, 2, -4, 1, 0], ![-9, 37, 9, -11, 6], ![5, 9, 0, 4, -20], ![-3, -18, 0, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 10, 1, -3, 6]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-13, 10, 1, -3, 6]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-13, 10, 1, -3, 6], ![42, -11, 0, 6, -18], ![-132, 30, 7, -12, 36], ![58, -32, -2, 13, -18], ![34, -2, -2, 2, -1]]]
  hmulB := by decide  
  f := ![![![-4721, 1436, 965, -1203, 2220]], ![![-2896, 881, 592, -738, 1362]], ![![-8830, 2686, 1805, -2250, 4152]], ![![-420, 128, 86, -107, 198]], ![![-993, 302, 203, -253, 467]]]
  g := ![![![-9, 10, 1, -3, 6], ![10, -11, 0, 6, -18], ![-38, 30, 7, -12, 36], ![26, -32, -2, 13, -18], ![5, -2, -2, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-561, 169, 120, -147, 268]] ![![-3, -5, -1, 0, 4]]
  ![![-4721, 1436, 965, -1203, 2220]] where
 M := ![![![-4721, 1436, 965, -1203, 2220]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-4721, 1436, 965, -1203, 2220]] ![![-13, 10, 1, -3, 6]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [12, 12, 0, 8, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 9, 9, 3, 8], [2, 5, 6, 12, 8], [7, 8, 3, 11, 2], [5, 3, 8, 0, 8], [0, 1]]
 g := ![![[9, 4, 6, 6, 1], [10, 1], []], ![[12, 9, 6, 5, 8, 10, 9, 7], [6, 0, 11, 4], [1, 5, 11, 11, 6, 0, 2, 5]], ![[12, 10, 0, 2, 2, 9, 10, 7], [6, 6, 5, 3], [2, 3, 0, 6, 7, 2, 1, 5]], ![[10, 0, 10, 11, 6, 0, 7, 5], [3, 8, 10, 4], [9, 0, 8, 9, 6, 10, 4, 8]], ![[8, 10, 8, 11, 4, 3, 8, 11], [4, 9, 8, 3], [11, 0, 7, 4, 12, 7, 11, 5]]]
 h' := ![![[9, 9, 9, 3, 8], [10, 11, 1, 11, 1], [0, 0, 0, 1], [0, 1]], ![[2, 5, 6, 12, 8], [10, 3, 11, 9, 3], [2, 9, 9, 9, 2], [9, 9, 9, 3, 8]], ![[7, 8, 3, 11, 2], [2, 12, 0, 3, 3], [10, 0, 4, 8, 9], [2, 5, 6, 12, 8]], ![[5, 3, 8, 0, 8], [4, 2, 7, 1, 10], [1, 2, 12, 1, 11], [7, 8, 3, 11, 2]], ![[0, 1], [1, 11, 7, 2, 9], [6, 2, 1, 7, 4], [5, 3, 8, 0, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 11, 9, 1], [], [], []]
 b := ![[], [8, 2, 4, 2, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [12, 12, 0, 8, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72624152226990, -25554722535966, -18830256435003, -25862944492203, -34705414164876]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5586473248230, -1965747887382, -1448481264231, -1989457268631, -2669647243452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5535, 1683, 1131, -1410, 2602]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-5535, 1683, 1131, -1410, 2602]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![6, 0, 7, 1, 0], ![1, 0, 2, 0, 1]] where
  M :=![![![-5535, 1683, 1131, -1410, 2602], ![17996, -5474, -3678, 4585, -8460], ![-58510, 17799, 11959, -14909, 27510], ![49916, -15181, -10202, 12718, -23468], ![-7270, 2210, 1486, -1852, 3417]]]
  hmulB := by decide  
  f := ![![![-17, 1, -1, -4, -4]], ![![-40, -24, -10, -11, -24]], ![![-214, -65, -47, -65, -66]], ![![-112, -34, -25, -35, -38]], ![![-31, -9, -7, -10, -11]]]
  g := ![![![19, 99, 341, -1410, 2602], ![-62, -322, -1109, 4585, -8460], ![202, 1047, 3606, -14909, 27510], ![-172, -893, -3076, 12718, -23468], ![25, 130, 448, -1852, 3417]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [1, 10, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 13, 12], [5, 3, 5], [0, 1]]
 g := ![![[5, 14, 16], [3, 15], [0, 1], []], ![[15, 16, 13, 12], [12, 13], [2, 9], [6, 8]], ![[7, 13, 3, 11], [12, 1], [14, 16], [13, 8]]]
 h' := ![![[12, 13, 12], [14, 6, 4], [0, 16, 7], [0, 0, 1], [0, 1]], ![[5, 3, 5], [9, 0, 16], [2, 12, 9], [2, 6, 3], [12, 13, 12]], ![[0, 1], [7, 11, 14], [11, 6, 1], [12, 11, 13], [5, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 10], []]
 b := ![[], [15, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [1, 10, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9328969893, 4432282449, 3256813737, 3489015720, 6142838377]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1043997812, 260722497, -1967763121, 3489015720, 6142838377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 1, -1, -4, -4]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-17, 1, -1, -4, -4]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![9, 12, 1, 0, 0], ![1, 4, 0, 1, 0], ![1, 14, 0, 0, 1]] where
  M :=![![![-17, 1, -1, -4, -4], ![-40, -24, -10, -11, -24], ![-214, -65, -47, -65, -66], ![-304, -129, -90, -116, -160], ![-82, -24, -24, -36, -51]]]
  hmulB := by decide  
  f := ![![![-5535, 1683, 1131, -1410, 2602]], ![![17996, -5474, -3678, 4585, -8460]], ![![6331, -1926, -1294, 1613, -2976]], ![![6845, -2082, -1399, 1744, -3218]], ![![14067, -4279, -2875, 3584, -6613]]]
  g := ![![![0, 5, -1, -4, -4], ![5, 28, -10, -11, -24], ![20, 99, -47, -65, -66], ![46, 215, -90, -116, -160], ![13, 66, -24, -36, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[7, 1], [2], [15], [1]], ![[0, 16], [2], [15], [1]]]
 h' := ![![[10, 16], [7, 1], [3, 11], [16, 10], [0, 1]], ![[0, 1], [0, 16], [11, 6], [14, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [4, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [1, 7, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20979, 78883, 63735, 15926, 123610]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-40716, -145893, 63735, 15926, 123610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-5535, 1683, 1131, -1410, 2602]] ![![-17, 1, -1, -4, -4]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [2, 18, 1, 7, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 6, 0, 9, 15], [15, 14, 14, 16, 3], [4, 8, 16, 18, 13], [4, 9, 8, 14, 7], [0, 1]]
 g := ![![[13, 6, 8, 4, 17], [5, 14, 2, 16, 1], [], []], ![[9, 12, 4, 11, 14, 16, 14, 3], [17, 9, 0, 11, 8, 15, 7, 15], [10, 18, 4, 4], [17, 6, 13, 16]], ![[15, 2, 18, 7, 0, 12], [9, 7, 4, 2, 18, 11, 16, 2], [3, 0, 14, 5], [1, 13, 12, 9]], ![[0, 1, 4, 15, 8, 9, 18, 18], [6, 16, 0, 12, 9, 18, 5, 12], [16, 17, 2, 5], [4, 16, 18, 17]], ![[15, 11, 4, 11, 2, 7, 5, 1], [13, 16, 18, 18, 14, 4, 6, 9], [3, 18, 8, 1], [10, 8, 11, 11]]]
 h' := ![![[12, 6, 0, 9, 15], [9, 15, 5, 16, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[15, 14, 14, 16, 3], [6, 2, 5, 17, 17], [15, 17, 17, 3, 18], [15, 16, 18, 15, 17], [12, 6, 0, 9, 15]], ![[4, 8, 16, 18, 13], [1, 14, 4, 2], [0, 5, 6, 10, 8], [14, 15, 15, 10, 10], [15, 14, 14, 16, 3]], ![[4, 9, 8, 14, 7], [18, 2, 10, 5, 15], [13, 7, 10, 14, 13], [8, 17, 16, 17, 10], [4, 8, 16, 18, 13]], ![[0, 1], [13, 5, 14, 17, 12], [10, 9, 5, 11, 17], [15, 9, 7, 15, 1], [4, 9, 8, 14, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 3, 17, 4], [], [], []]
 b := ![[], [18, 6, 11, 0, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [2, 18, 1, 7, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18030277769302, 5476924540688, 3733140084748, -4626764252076, 8520235177752]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-948961987858, 288259186352, 196481057092, -243513908004, 448433430408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [9, 13, 11, 20, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 19, 9, 3, 22], [16, 7, 6, 4, 9], [22, 18, 12, 21, 10], [15, 1, 19, 18, 5], [0, 1]]
 g := ![![[11, 14, 6, 12, 16], [1, 3, 9], [1], []], ![[20, 11, 4, 11, 6, 20, 21, 11], [10, 19, 19, 1, 8, 20, 17, 17], [9, 19, 20, 12, 8, 10, 11, 11], [10, 17, 17, 1]], ![[19, 12, 13, 9, 5, 16, 5, 4], [3, 8, 3, 10, 13, 19, 18, 12], [6, 20, 12, 19, 15, 9, 15, 6], [5, 22, 3, 12]], ![[20, 21, 11, 17, 14, 11], [21, 1, 16, 3, 18, 12, 14, 14], [6, 4, 6, 8, 15, 3, 12, 22], [12, 15, 6, 8]], ![[11, 11, 21, 6, 17, 9, 16, 22], [12, 8, 22, 9, 3, 18, 2, 11], [3, 5, 12, 9, 2, 2, 9, 14], [16, 14, 19, 2]]]
 h' := ![![[16, 19, 9, 3, 22], [14, 18, 11, 13, 4], [14, 10, 12, 3], [0, 0, 1], [0, 1]], ![[16, 7, 6, 4, 9], [8, 8, 10, 20, 9], [20, 0, 18, 1, 12], [5, 3, 4, 5, 14], [16, 19, 9, 3, 22]], ![[22, 18, 12, 21, 10], [5, 9, 18, 14, 7], [18, 14, 15, 15, 3], [4, 7, 11, 22, 4], [16, 7, 6, 4, 9]], ![[15, 1, 19, 18, 5], [9, 10, 22, 10], [20, 14, 13, 21, 12], [8, 18, 11, 19, 19], [22, 18, 12, 21, 10]], ![[0, 1], [18, 1, 8, 12, 3], [17, 8, 11, 6, 19], [12, 18, 19, 0, 9], [15, 1, 19, 18, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 18, 18, 12], [], [], []]
 b := ![[], [18, 4, 22, 8, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [9, 13, 11, 20, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6094655025691, 2128881471609, 1569139013740, 2168023200164, 2889809634243]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![264985001117, 92560063983, 68223435380, 94261878268, 125643897141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB696I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB696I0 : PrimesBelowBoundCertificateInterval O 1 23 696 where
  m := 9
  g := ![5, 5, 5, 1, 3, 1, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB696I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 11, 11]
    · exact ![371293]
    · exact ![4913, 289]
    · exact ![2476099]
    · exact ![6436343]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
      exact NI3N2
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I11N1, I11N2, I17N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1, I11N2], [], [I17N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
