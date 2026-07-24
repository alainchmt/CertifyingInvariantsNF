
import IdealArithmetic.Examples.NF5_3_42187500_1.RI5_3_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-494, 255, 61, -89, 18]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-494, 255, 61, -89, 18]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![8, 19, 5, 16, 1]] where
  M :=![![![-494, 255, 61, -89, 18], ![-181, -274, 485, 247, -338], ![2502, -474, -1097, -100, 494], ![-2404, 1468, 20, -603, 294], ![-1631, 335, 775, 73, -367]]]
  hmulB := by decide  
  f := ![![![218, -81, 19, -61, 62]], ![![-869, 262, -57, 223, -182]], ![![1688, -596, 137, -462, 446]], ![![-2270, 686, -150, 583, -478]], ![![-1424, 407, -87, 358, -275]]]
  g := ![![![-22, -3, -1, -13, 18], ![87, 212, 75, 195, -338], ![-50, -340, -123, -276, 494], ![-164, -142, -50, -183, 294], ![45, 252, 90, 205, -367]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [7, 13, 24, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 25, 8, 17], [7, 25, 4, 2], [23, 7, 17, 10], [0, 1]]
 g := ![![[23, 14, 22, 9], [13, 25, 16], [0, 27, 14, 1], []], ![[19, 2, 20, 23, 20, 27], [27, 26, 7], [4, 23, 22, 19, 7, 14], [7, 23, 27, 16, 28, 12]], ![[0, 20, 17, 27, 2, 18], [18, 27, 25], [13, 11, 27, 18, 25, 10], [21, 24, 10, 8, 15, 8]], ![[24, 19, 28, 12, 3, 18], [19, 9, 25], [14, 20, 22, 16, 1, 10], [16, 24, 4, 14, 18, 14]]]
 h' := ![![[13, 25, 8, 17], [25, 4, 27, 26], [0, 14, 15, 4], [0, 0, 0, 1], [0, 1]], ![[7, 25, 4, 2], [10, 10, 7, 11], [24, 24, 23, 6], [2, 11, 22, 9], [13, 25, 8, 17]], ![[23, 7, 17, 10], [13, 5, 19, 26], [20, 2, 12, 24], [22, 15, 9, 18], [7, 25, 4, 2]], ![[0, 1], [28, 10, 5, 24], [25, 18, 8, 24], [20, 3, 27, 1], [23, 7, 17, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 24, 22], []]
 b := ![[], [], [23, 26, 19, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [7, 13, 24, 15, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21772920860, -5281060744, 1696885104, 1725416568, 8209604104]
  a := ![15, -20, -8, 12, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3015508748, -5560811680, -1356935704, -4469939624, 8209604104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-218, 81, -19, 61, -62]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-218, 81, -19, 61, -62]] 
 ![![29, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-218, 81, -19, 61, -62], ![869, -262, 57, -223, 182], ![-1688, 596, -137, 462, -446], ![2270, -686, 150, -583, 478], ![-1351, 523, -123, 385, -405]]]
  hmulB := by decide  
  f := ![![![494, -255, -61, 89, -18]], ![![381, -184, -63, 59, -2]], ![![50, -54, 21, 28, -22]], ![![134, -77, -7, 30, -12]], ![![431, -205, -73, 65, -1]]]
  g := ![![![-23, 81, -19, 61, -62], ![98, -262, 57, -223, 182], ![-182, 596, -137, 462, -446], ![255, -686, 150, -583, 478], ![-142, 523, -123, 385, -405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-494, 255, 61, -89, 18]] ![![-218, 81, -19, 61, -62]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [24, 13, 18, 10, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 7, 27, 7, 15], [23, 27, 17, 18, 21], [3, 7, 29, 20, 24], [11, 20, 20, 17, 2], [0, 1]]
 g := ![![[17, 19, 17, 22, 16], [21, 9, 19, 10, 5], [22, 1, 1], []], ![[23, 26, 8, 28, 26, 18, 16, 6], [5, 4, 23, 19, 29, 5, 26, 11], [23, 21, 26, 24, 2, 5, 11, 26], [23, 28, 11, 6, 7, 19, 9, 27]], ![[27, 29, 19, 26, 19, 18, 8, 11], [1, 0, 28, 19, 20, 23, 5, 13], [4, 27, 1, 27, 18, 15, 25, 29], [11, 2, 6, 28, 29, 15, 29, 23]], ![[0, 12, 16, 27, 18, 11], [11, 2, 1, 27, 28, 23, 7, 24], [29, 9, 16, 3, 19, 20, 13, 23], [19, 2, 17, 15, 26, 30, 24, 29]], ![[8, 28, 29, 23, 16, 7, 0, 18], [22, 22, 16, 28, 15, 17, 26, 19], [0, 3, 16, 0, 0, 7, 17, 4], [27, 26, 27, 18, 23, 29, 26, 8]]]
 h' := ![![[26, 7, 27, 7, 15], [23, 8, 10, 7, 27], [30, 0, 1, 28, 25], [0, 0, 0, 1], [0, 1]], ![[23, 27, 17, 18, 21], [3, 19, 20, 24, 9], [5, 3, 5, 15, 28], [5, 19, 0, 5, 17], [26, 7, 27, 7, 15]], ![[3, 7, 29, 20, 24], [0, 23, 12, 17, 23], [20, 10, 4, 22, 15], [30, 2, 1, 25, 5], [23, 27, 17, 18, 21]], ![[11, 20, 20, 17, 2], [18, 14, 19, 5], [30, 29, 29, 4, 30], [5, 18, 14, 10, 17], [3, 7, 29, 20, 24]], ![[0, 1], [28, 29, 1, 9, 3], [11, 20, 23, 24, 26], [1, 23, 16, 21, 23], [11, 20, 20, 17, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 8, 16, 13], [], [], []]
 b := ![[], [30, 13, 8, 29, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [24, 13, 18, 10, 30, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![708620806529004186, 92455766625844770, -42305480431354632, -77695171888504038, -174921817591050336]
  a := ![120, -180, -58, 54, -477]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22858735694484006, 2982444084704670, -1364692917140472, -2506295867371098, -5642639277130656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [25, 4, 7, 5, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 3, 8, 26, 22], [35, 16, 23, 0, 28], [22, 7, 28, 30, 36], [8, 10, 15, 18, 25], [0, 1]]
 g := ![![[11, 16, 4, 9, 26], [32, 5, 21, 21], [3, 10, 28, 12, 1], [], []], ![[27, 18, 21, 17, 3, 36, 14, 18], [18, 31, 21, 16], [7, 33, 10, 26, 34, 27, 20, 18], [7, 0, 2, 1], [28, 3, 33, 3]], ![[31, 22, 21, 25, 33, 21, 3, 25], [31, 31, 27, 28], [21, 13, 12, 10, 7, 30, 14, 9], [2, 22, 17, 25], [31, 4, 10, 7]], ![[21, 0, 17, 28, 6, 31, 36, 30], [20, 8, 11, 34], [9, 1, 31, 0, 12, 28, 17, 16], [5, 33, 30, 7], [23, 4, 26, 1]], ![[14, 11, 0, 20, 26, 28, 17, 26], [32, 23, 2, 33], [1, 8, 7, 16, 11, 25, 7, 36], [15, 28, 20, 3], [16, 33, 1, 33]]]
 h' := ![![[21, 3, 8, 26, 22], [15, 12, 22, 20, 10], [36, 34, 16, 21, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[35, 16, 23, 0, 28], [32, 20, 2, 7, 24], [1, 8, 5, 26, 33], [10, 9, 33, 26, 13], [0, 13, 15, 32, 1], [21, 3, 8, 26, 22]], ![[22, 7, 28, 30, 36], [29, 2, 4, 22, 10], [8, 17, 11, 24, 19], [23, 19, 1, 19, 31], [6, 8, 14, 5, 5], [35, 16, 23, 0, 28]], ![[8, 10, 15, 18, 25], [6, 35, 28, 32, 28], [5, 13, 1, 2, 21], [16, 21, 26, 21, 13], [20, 5, 10, 34, 9], [22, 7, 28, 30, 36]], ![[0, 1], [4, 5, 18, 30, 2], [29, 2, 4, 1, 25], [4, 25, 14, 8, 16], [34, 11, 34, 3, 22], [8, 10, 15, 18, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 8, 18, 12], [], [], []]
 b := ![[], [36, 15, 28, 29, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [25, 4, 7, 5, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3168665230747, 459988330702, -205978167278, -325147957532, -832841404698]
  a := ![11, -15, -5, 6, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![85639600831, 12432117046, -5566977494, -8787782636, -22509227154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, 9, 8, 15, -16]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-52, 9, 8, 15, -16]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![34, 2, 20, 17, 1]] where
  M :=![![![-52, 9, 8, 15, -16], ![225, -76, -22, -31, 44], ![-427, 163, -10, 53, -62], ![225, -117, 101, -72, 44], ![-160, 34, -29, 84, -65]]]
  hmulB := by decide  
  f := ![![![25, 0, -3, -4, -6]], ![![94, 3, -9, -14, -22]], ![![125, 7, -10, -17, -28]], ![![281, 19, -21, -38, -62]], ![![210, 12, -17, -29, -47]]]
  g := ![![![12, 1, 8, 7, -16], ![-31, -4, -22, -19, 44], ![41, 7, 30, 27, -62], ![-31, -5, -19, -20, 44], ![50, 4, 31, 29, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [15, 18, 13, 30, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 8, 8, 4], [26, 40], [7, 33, 33, 37], [0, 1]]
 g := ![![[37, 24, 19, 39], [21, 25, 39], [25, 7, 20], [11, 1], []], ![[9, 30, 19, 9, 40, 5], [29, 25, 10], [16, 34, 36], [26, 20, 25, 19, 18, 9], [18, 35, 16]], ![[1, 10, 27, 2], [16, 38, 39], [33, 19, 20], [37, 40], []], ![[8, 34, 33, 38, 34, 36], [18, 29, 10], [21, 21, 36], [1, 33, 37, 40, 40, 32], [18, 35, 16]]]
 h' := ![![[19, 8, 8, 4], [38, 4, 0, 30], [36, 35, 4, 11], [40, 33, 3, 26], [0, 0, 1], [0, 1]], ![[26, 40], [24, 39, 6, 14], [7, 20, 27, 25], [1, 40, 37, 35], [9, 29, 2, 22], [19, 8, 8, 4]], ![[7, 33, 33, 37], [39, 0, 3, 11], [22, 40, 1, 30], [5, 14, 22, 15], [20, 30, 1], [26, 40]], ![[0, 1], [33, 39, 32, 27], [4, 28, 9, 16], [14, 36, 20, 6], [25, 23, 37, 19], [7, 33, 33, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35], []]
 b := ![[], [], [24, 6, 35, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [15, 18, 13, 30, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4336081574196, -836250581767, 298419397591, 429341649273, 1383228456674]
  a := ![-52, 75, 27, -35, 209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1252825587832, -87870914515, -667467066729, -563062002785, 1383228456674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 0, 3, 4, 6]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-25, 0, 3, 4, 6]] 
 ![![41, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-25, 0, 3, 4, 6], ![-94, -3, 9, 14, 22], ![-125, -7, 10, 17, 28], ![-281, -19, 21, 38, 62], ![-295, -23, 20, 39, 65]]]
  hmulB := by decide  
  f := ![![![52, -9, -8, -15, 16]], ![![11, -1, -2, -4, 4]], ![![51, -11, -6, -13, 14]], ![![11, 0, -5, -3, 4]], ![![28, -5, -3, -9, 9]]]
  g := ![![![-7, 0, 3, 4, 6], ![-23, -3, 9, 14, 22], ![-27, -7, 10, 17, 28], ![-58, -19, 21, 38, 62], ![-58, -23, 20, 39, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-52, 9, 8, 15, -16]] ![![-25, 0, 3, 4, 6]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1290, -541, -250, 157, 20]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1290, -541, -250, 157, 20]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![5, 16, 1, 0, 0], ![30, 42, 0, 1, 0], ![42, 26, 0, 0, 1]] where
  M :=![![![1290, -541, -250, 157, 20], ![-457, 966, -792, -617, 648], ![-4323, 435, 2406, 473, -1234], ![6857, -3341, -799, 1172, -288], ![2938, -256, -1679, -350, 871]]]
  hmulB := by decide  
  f := ![![![-1503, 170, -103, 290, -142]], ![![1840, -1469, 159, -780, 1018]], ![![320, -479, 33, -211, 326]], ![![903, -1395, 95, -610, 950]], ![![-529, -685, -18, -149, 447]]]
  g := ![![![-70, -85, -250, 157, 20], ![-121, 528, -792, -617, 648], ![495, -601, 2406, 473, -1234], ![-284, -751, -799, 1172, -288], ![-343, 434, -1679, -350, 871]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [35, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 42], [0, 1]]
 g := ![![[41, 16], [35, 21], [13], [34, 41], [1]], ![[0, 27], [0, 22], [13], [23, 2], [1]]]
 h' := ![![[27, 42], [22, 39], [42, 8], [14, 20], [8, 27], [0, 1]], ![[0, 1], [0, 4], [0, 35], [38, 23], [6, 16], [27, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [31, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [35, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49550, -12248, 17064, 305, 20395]
  a := ![14, -17, -7, 18, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23270, -19264, 17064, 305, 20395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 24, -12, -28, -48]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![229, 24, -12, -28, -48]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![23, 4, 1, 0, 0], ![27, 21, 0, 1, 0], ![23, 40, 0, 0, 1]] where
  M :=![![![229, 24, -12, -28, -48], ![748, 81, -36, -92, -160], ![872, 88, -43, -104, -184], ![1868, 196, -96, -227, -392], ![1864, 200, -92, -228, -395]]]
  hmulB := by decide  
  f := ![![![31, -24, 4, -12, 16]], ![![-228, 43, -20, 52, -32]], ![![3, -12, 1, -4, 8]], ![![-105, 9, -8, 21, -8]], ![![-189, 24, -16, 40, -19]]]
  g := ![![![55, 60, -12, -28, -48], ![180, 199, -36, -92, -160], ![207, 228, -43, -104, -184], ![447, 489, -96, -227, -392], ![447, 492, -92, -228, -395]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [8, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 42], [0, 1]]
 g := ![![[42, 11], [38, 40], [1], [40, 21], [1]], ![[1, 32], [14, 3], [1], [36, 22], [1]]]
 h' := ![![[8, 42], [40, 22], [9, 13], [24, 1], [35, 8], [0, 1]], ![[0, 1], [1, 21], [27, 30], [32, 42], [13, 35], [8, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [8, 35, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47798, -992, 3418, 6390, 11864]
  a := ![6, -12, -2, -14, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13298, -14498, 3418, 6390, 11864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 1, -1, -1, -2]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![10, 1, -1, -1, -2]] 
 ![![43, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![10, 1, -1, -1, -2], ![31, 4, -1, -5, -6], ![32, 4, -1, -2, -10], ![92, 4, -6, -11, -14], ![73, 11, -5, -9, -17]]]
  hmulB := by decide  
  f := ![![![-782, -197, -33, 57, 134]], ![![-139, -35, -6, 10, 24]], ![![-550, -138, -23, 40, 94]], ![![-618, -156, -26, 45, 106]], ![![-659, -166, -28, 48, 113]]]
  g := ![![![3, 1, -1, -1, -2], ![9, 4, -1, -5, -6], ![10, 4, -1, -2, -10], ![24, 4, -6, -11, -14], ![23, 11, -5, -9, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1290, -541, -250, 157, 20]] ![![229, 24, -12, -28, -48]]
  ![![3298, -89, -2166, -547, 1196]] where
 M := ![![![3298, -89, -2166, -547, 1196]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![3298, -89, -2166, -547, 1196]] ![![10, 1, -1, -1, -2]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-2107, 5246, -3741, -3268, 2924]]]
 hmul := by decide  
 g := ![![![![-49, 122, -87, -76, 68]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-380, 9, 20, 21, 70]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-380, 9, 20, 21, 70]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![8, 29, 7, 5, 1]] where
  M :=![![![-380, 9, 20, 21, 70], ![-1071, -140, 138, 159, 154], ![-699, -225, -124, 133, 318], ![-2801, -31, 93, 194, 584], ![-2766, -192, 247, 304, 465]]]
  hmulB := by decide  
  f := ![![![-255, -58, -11, 20, 40]], ![![-620, -173, -25, 38, 120]], ![![-609, -111, -28, 57, 76]], ![![-903, -273, -35, 48, 190]], ![![-631, -166, -26, 42, 115]]]
  g := ![![![-20, -43, -10, -7, 70], ![-49, -98, -20, -13, 154], ![-69, -201, -50, -31, 318], ![-159, -361, -85, -58, 584], ![-138, -291, -64, -43, 465]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [42, 0, 28, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 14, 32], [45, 11, 9, 8], [33, 21, 6, 39], [0, 1]]
 g := ![![[19, 43, 29, 34], [17, 7, 2, 34], [41, 40, 0, 34], [32, 1], []], ![[30, 10, 8, 40, 21], [32, 44, 29, 44, 9], [12, 46, 27, 38, 34], [17, 24, 34, 4, 2], [37]], ![[38, 21, 21, 25, 19, 9], [28, 25, 6, 31, 11, 24], [27, 0, 11, 39, 23, 2], [10, 34, 7, 22, 30, 42], [36, 30, 17]], ![[45, 32, 45, 32, 23, 29], [41, 19, 2, 13, 41, 23], [45, 15, 20, 3, 27, 20], [46, 41, 29, 40, 22, 43], [24, 25, 17]]]
 h' := ![![[1, 14, 32], [38, 42, 43, 9], [17, 44, 29, 38], [19, 5, 44, 9], [0, 0, 1], [0, 1]], ![[45, 11, 9, 8], [6, 37, 13, 33], [38, 34, 24, 32], [42, 17, 27, 45], [45, 28, 23, 12], [1, 14, 32]], ![[33, 21, 6, 39], [14, 40, 42, 30], [4, 31, 39, 12], [18, 21, 46, 24], [43, 12, 8, 8], [45, 11, 9, 8]], ![[0, 1], [10, 22, 43, 22], [20, 32, 2, 12], [26, 4, 24, 16], [34, 7, 15, 27], [33, 21, 6, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 32, 4], []]
 b := ![[], [], [25, 45, 39, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [42, 0, 28, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-545024863, -52709817, 35302894, 68287079, 124341316]
  a := ![0, 10, 7, 1, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32760753, -77842723, -17767794, -11774883, 124341316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-255, -58, -11, 20, 40]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-255, -58, -11, 20, 40]] 
 ![![47, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-255, -58, -11, 20, 40], ![-620, -173, -25, 38, 120], ![-609, -111, -28, 57, 76], ![-903, -273, -35, 48, 190], ![-859, -179, -38, 73, 123]]]
  hmulB := by decide  
  f := ![![![-380, 9, 20, 21, 70]], ![![-233, 2, 14, 15, 42]], ![![-217, 0, 8, 14, 44]], ![![-383, 7, 19, 22, 72]], ![![-358, 3, 21, 23, 65]]]
  g := ![![![-16, -58, -11, 20, 40], ![-31, -173, -25, 38, 120], ![-45, -111, -28, 57, 76], ![-40, -273, -35, 48, 190], ![-58, -179, -38, 73, 123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-380, 9, 20, 21, 70]] ![![-255, -58, -11, 20, 40]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 30, -14, -34, -60]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![283, 30, -14, -34, -60]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![21, 0, 1, 0, 0], ![37, 37, 0, 1, 0], ![18, 28, 0, 0, 1]] where
  M :=![![![283, 30, -14, -34, -60], ![934, 99, -46, -114, -196], ![1060, 116, -51, -128, -228], ![2304, 240, -112, -279, -484], ![2298, 246, -114, -278, -487]]]
  hmulB := by decide  
  f := ![![![219, 50, 6, -14, -36]], ![![554, 147, 22, -46, -92]], ![![95, 22, 3, -6, -16]], ![![557, 141, 20, -43, -92]], ![![380, 98, 14, -30, -63]]]
  g := ![![![55, 56, -14, -34, -60], ![182, 185, -46, -114, -196], ![207, 212, -51, -128, -228], ![447, 455, -112, -279, -484], ![448, 456, -114, -278, -487]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [24, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 52], [0, 1]]
 g := ![![[9, 42], [16], [30, 47], [11], [49, 1]], ![[0, 11], [16], [1, 6], [11], [45, 52]]]
 h' := ![![[49, 52], [47, 25], [22, 49], [48, 10], [43, 45], [0, 1]], ![[0, 1], [0, 28], [38, 4], [8, 43], [22, 8], [49, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [8, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [24, 4, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5497, 28, 495, 704, 1327]
  a := ![2, -5, -1, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1242, -1192, 495, 704, 1327]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, 34, -6, 24, -24]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-81, 34, -6, 24, -24]] 
 ![![53, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-81, 34, -6, 24, -24], ![336, -95, 26, -84, 72], ![-666, 234, -49, 182, -168], ![836, -260, 66, -217, 196], ![-576, 204, -40, 158, -143]]]
  hmulB := by decide  
  f := ![![![-761, 286, 186, -68, -40]], ![![-332, 117, 90, -24, -24]], ![![-224, 98, 39, -30, 0]], ![![-153, 62, 32, -17, -4]], ![![-282, 96, 80, -18, -23]]]
  g := ![![![-9, 34, -6, 24, -24], ![24, -95, 26, -84, 72], ![-62, 234, -49, 182, -168], ![65, -260, 66, -217, 196], ![-56, 204, -40, 158, -143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -3, 1, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-2, -3, 1, 1, 0]] 
 ![![53, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2, -3, 1, 1, 0], ![-1, -4, -7, 1, 4], ![-30, 6, 7, -4, 2], ![-28, -8, 8, 9, -6], ![13, -13, -5, 1, 5]]]
  hmulB := by decide  
  f := ![![![-3610, -387, 175, 437, 764]], ![![-2949, -316, 143, 357, 624]], ![![-2164, -232, 105, 262, 458]], ![![-3072, -329, 149, 372, 650]], ![![-553, -59, 27, 67, 117]]]
  g := ![![![1, -3, 1, 1, 0], ![6, -4, -7, 1, 4], ![-6, 6, 7, -4, 2], ![-5, -8, 8, 9, -6], ![12, -13, -5, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2

def I53N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 3, -7, -3, 4]] i)))

def SI53N3: IdealEqSpanCertificate' Table ![![10, 3, -7, -3, 4]] 
 ![![53, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![10, 3, -7, -3, 4], ![-57, 22, 21, -3, -8], ![90, -42, -7, 16, -6], ![82, 2, -48, -13, 26], ![-57, 33, 7, -11, 3]]]
  hmulB := by decide  
  f := ![![![-2802, 935, -209, 749, -680]], ![![-2095, 699, -156, 560, -508]], ![![-816, 272, -61, 218, -198]], ![![-1860, 620, -138, 497, -450]], ![![-551, 183, -41, 147, -133]]]
  g := ![![![1, 3, -7, -3, 4], ![-19, 22, 21, -3, -8], ![24, -42, -7, 16, -6], ![16, 2, -48, -13, 26], ![-20, 33, 7, -11, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N3 : Nat.card (O ⧸ I53N3) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N3)

lemma isPrimeI53N3 : Ideal.IsPrime I53N3 := prime_ideal_of_norm_prime hp53.out _ NI53N3
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![283, 30, -14, -34, -60]] ![![-81, 34, -6, 24, -24]]
  ![![2617, 96, -76, -378, -364]] where
 M := ![![![2617, 96, -76, -378, -364]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![2617, 96, -76, -378, -364]] ![![-2, -3, 1, 1, 0]]
  ![![2802, -935, 209, -749, 680]] where
 M := ![![![2802, -935, 209, -749, 680]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N2 : IdealMulLeCertificate' Table 
  ![![2802, -935, 209, -749, 680]] ![![10, 3, -7, -3, 4]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2, I53N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
    exact isPrimeI53N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1 ⊙ MulI53N2)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152, -23, 33, 27, 10]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-152, -23, 33, 27, 10]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![32, 39, 21, 44, 1]] where
  M :=![![![-152, -23, 33, 27, 10], ![-177, -118, -59, 59, 118], ![-826, 118, 59, 0, 118], ![-1298, -118, 236, 177, 118], ![-805, -227, 23, 169, 209]]]
  hmulB := by decide  
  f := ![![![216, 55, 9, -15, -38]], ![![585, 142, 25, -43, -98]], ![![464, 124, 19, -30, -86]], ![![892, 212, 38, -67, -146]], ![![1346, 329, 57, -98, -227]]]
  g := ![![![-8, -7, -3, -7, 10], ![-67, -80, -43, -87, 118], ![-78, -76, -41, -88, 118], ![-86, -80, -38, -85, 118], ![-127, -142, -74, -153, 209]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [27, 43, 52, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 17, 41, 37], [46, 4, 49, 52], [20, 37, 28, 29], [0, 1]]
 g := ![![[49, 22, 11, 57], [11, 4, 31, 3], [30, 34, 3], [9, 36, 41, 1], []], ![[44, 46, 2, 47, 40, 47], [42, 49, 4, 20, 21, 30], [4, 10, 35], [16, 23, 15, 35, 44, 32], [25, 20, 4, 32, 33, 31]], ![[24, 10, 8, 18, 31, 44], [14, 47, 12, 55, 40, 31], [29, 19, 4], [40, 8, 53, 31, 26, 40], [56, 53, 9, 33, 43, 11]], ![[22, 16, 1, 9], [14, 1, 46, 24, 35, 28], [34, 36, 20], [40, 48, 40, 13, 56, 45], [26, 17, 37, 18, 38, 22]]]
 h' := ![![[34, 17, 41, 37], [57, 45, 48, 36], [6, 3, 31, 48], [52, 57, 4, 11], [0, 0, 0, 1], [0, 1]], ![[46, 4, 49, 52], [37, 12, 6, 9], [36, 22, 32, 57], [12, 39, 58, 34], [43, 52, 9, 16], [34, 17, 41, 37]], ![[20, 37, 28, 29], [17, 12, 15, 14], [29, 54, 32, 2], [35, 4, 51, 57], [8, 18, 23, 21], [46, 4, 49, 52]], ![[0, 1], [22, 49, 49], [43, 39, 23, 11], [31, 18, 5, 16], [41, 48, 27, 21], [20, 37, 28, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [52, 15, 35], []]
 b := ![[], [], [58, 35, 26, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [27, 43, 52, 18, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-588624980, -11180218357, 3066289623, -4241676471, 12930623972]
  a := ![-16, 22, 13, -24, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7023196476, -8736856835, -4550454471, -9715070021, 12930623972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-216, -55, -9, 15, 38]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-216, -55, -9, 15, 38]] 
 ![![59, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-216, -55, -9, 15, 38], ![-585, -142, -25, 43, 98], ![-464, -124, -19, 30, 86], ![-892, -212, -38, 67, 146], ![-695, -181, -29, 47, 125]]]
  hmulB := by decide  
  f := ![![![152, 23, -33, -27, -10]], ![![3, 2, 1, -1, -2]], ![![14, -2, -1, 0, -2]], ![![22, 2, -4, -3, -2]], ![![127, 21, -25, -23, -11]]]
  g := ![![![-32, -55, -9, 15, 38], ![-83, -142, -25, 43, 98], ![-72, -124, -19, 30, 86], ![-124, -212, -38, 67, 146], ![-105, -181, -29, 47, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-152, -23, 33, 27, 10]] ![![-216, -55, -9, 15, 38]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 1, -1, 3, -2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-8, 1, -1, 3, -2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![60, 38, 1, 0, 0], ![7, 27, 0, 1, 0], ![15, 21, 0, 0, 1]] where
  M :=![![![-8, 1, -1, 3, -2], ![27, -10, -1, -9, 10], ![-84, 24, 1, 18, -18], ![84, -36, 6, -17, 18], ![-51, 15, -9, 15, -11]]]
  hmulB := by decide  
  f := ![![![64, 1, -7, -9, -14]], ![![219, 14, -19, -33, -50]], ![![204, 10, -19, -30, -46]], ![![115, 7, -10, -17, -26]], ![![102, 6, -9, -15, -23]]]
  g := ![![![1, 0, -1, 3, -2], ![0, 1, -1, -9, 10], ![0, -2, 1, 18, -18], ![-7, -3, 6, -17, 18], ![9, 3, -9, 15, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [20, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 60], [0, 1]]
 g := ![![[48, 58], [1], [14, 42], [44, 3], [16, 1]], ![[0, 3], [1], [15, 19], [31, 58], [32, 60]]]
 h' := ![![[16, 60], [56, 27], [25, 60], [35, 15], [46, 53], [0, 1]], ![[0, 1], [0, 34], [9, 1], [31, 46], [40, 8], [16, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [50, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [20, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32627, -4643, 9068, 501, 13592]
  a := ![-10, 13, 5, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12854, -10626, 9068, 501, 13592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, -27, 4, -15, 20]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![38, -27, 4, -15, 20]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![45, 5, 1, 0, 0], ![11, 33, 0, 1, 0], ![53, 59, 0, 0, 1]] where
  M :=![![![38, -27, 4, -15, 20], ![-285, 56, -18, 63, -40], ![411, -171, 34, -121, 126], ![-679, 163, -45, 160, -116], ![306, -156, 29, -100, 117]]]
  hmulB := by decide  
  f := ![![![-63, 2, 31, 8, -14]], ![![202, -95, -55, 26, 18]], ![![-34, -4, 18, 7, -8]], ![![90, -50, -21, 16, 6]], ![![142, -92, -26, 33, 5]]]
  g := ![![![-17, -12, 4, -15, 20], ![32, 7, -18, 63, -40], ![-106, -62, 34, -121, 126], ![94, 32, -45, 160, -116], ![-100, -64, 29, -100, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [13, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 60], [0, 1]]
 g := ![![[44, 47], [34], [19, 20], [54, 52], [38, 1]], ![[0, 14], [34], [47, 41], [17, 9], [15, 60]]]
 h' := ![![[38, 60], [55, 13], [58, 20], [30, 9], [55, 28], [0, 1]], ![[0, 1], [0, 48], [25, 41], [6, 52], [21, 33], [38, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [52, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [13, 23, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9502, -229, 1529, 891, 2992]
  a := ![-3, 7, 3, -1, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4044, -3505, 1529, 891, 2992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, -3, 1, -3, 2]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![14, -3, 1, -3, 2]] 
 ![![61, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![14, -3, 1, -3, 2], ![-27, 14, -3, 9, -10], ![84, -24, 7, -22, 18], ![-82, 34, -6, 25, -26], ![81, -21, 5, -19, 15]]]
  hmulB := by decide  
  f := ![![![270, 29, -17, -31, -50]], ![![181, 20, -11, -21, -34]], ![![246, 26, -15, -28, -46]], ![![96, 10, -6, -11, -18]], ![![293, 32, -18, -34, -55]]]
  g := ![![![0, -3, 1, -3, 2], ![1, 14, -3, 9, -10], ![-2, -24, 7, -22, 18], ![2, 34, -6, 25, -26], ![0, -21, 5, -19, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-8, 1, -1, 3, -2]] ![![38, -27, 4, -15, 20]]
  ![![-3649, 1244, -277, 984, -908]] where
 M := ![![![-3649, 1244, -277, 984, -908]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-3649, 1244, -277, 984, -908]] ![![14, -3, 1, -3, 2]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-262178, 87535, -19764, 70089, -63928]]]
 hmul := by decide  
 g := ![![![![-4298, 1435, -324, 1149, -1048]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB318I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB318I1 : PrimesBelowBoundCertificateInterval O 23 61 318 where
  m := 9
  g := ![2, 1, 1, 2, 3, 2, 4, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB318I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2, I53N3]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![707281, 29]
    · exact ![28629151]
    · exact ![69343957]
    · exact ![2825761, 41]
    · exact ![1849, 1849, 43]
    · exact ![4879681, 47]
    · exact ![2809, 53, 53, 53]
    · exact ![12117361, 59]
    · exact ![3721, 3721, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
      exact NI53N3
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I41N1, I43N2, I47N1, I53N1, I53N2, I53N3, I59N1, I61N2]
  Il := ![[I29N1], [], [], [I41N1], [I43N2], [I47N1], [I53N1, I53N2, I53N3], [I59N1], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
