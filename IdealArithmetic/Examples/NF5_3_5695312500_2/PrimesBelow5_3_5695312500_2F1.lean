
import IdealArithmetic.Examples.NF5_3_5695312500_2.RI5_3_5695312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [4, 11, 16, 21, 19, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 27, 10, 25, 19], [0, 27, 24, 10, 8], [9, 24, 18, 5, 24], [10, 8, 6, 18, 7], [0, 1]]
 g := ![![[24, 6, 28, 9, 16], [1, 10, 17, 24], [21, 10, 1], []], ![[0, 15, 23, 3, 28, 5, 4, 18], [13, 20, 6, 23], [0, 26, 9, 14, 9, 25, 11, 2], [6, 10, 6, 19, 17, 28, 23, 15]], ![[5, 21, 9, 17, 14, 14, 23, 15], [21, 16, 28, 25], [14, 1, 13, 22, 17, 8, 18, 18], [0, 9, 19, 10, 26, 14, 22, 19]], ![[8, 21, 22, 8, 1, 3, 18, 9], [21, 19, 28, 13], [5, 17, 21, 0, 18, 2, 20, 28], [18, 13, 17, 17, 0, 12, 24, 20]], ![[3, 22, 5, 8, 21, 1, 21, 6], [22, 28, 27, 20], [8, 5, 16, 9, 15, 5, 10, 22], [15, 21, 22, 2, 7, 24, 15, 24]]]
 h' := ![![[20, 27, 10, 25, 19], [5, 5, 19, 21, 4], [3, 19, 14, 26, 13], [0, 0, 0, 1], [0, 1]], ![[0, 27, 24, 10, 8], [0, 1, 18, 4, 2], [20, 23, 21, 23, 9], [1, 17, 4, 20, 9], [20, 27, 10, 25, 19]], ![[9, 24, 18, 5, 24], [7, 1, 21, 2, 7], [2, 16, 3, 28, 24], [0, 22, 28, 5, 16], [0, 27, 24, 10, 8]], ![[10, 8, 6, 18, 7], [16, 24, 9, 7, 27], [10, 18, 20, 8, 19], [19, 14, 26, 0, 21], [9, 24, 18, 5, 24]], ![[0, 1], [23, 27, 20, 24, 18], [16, 11, 0, 2, 22], [12, 5, 0, 3, 12], [10, 8, 6, 18, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 18, 1, 6], [], [], []]
 b := ![[], [7, 22, 3, 13, 18], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [4, 11, 16, 21, 19, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52485799797618356402, 32138885388913525343, -8779014300263179419, 26039428294791390666, -124754076904959692218]
  a := ![228, 83, 50, 161, -498]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1809855165435115738, 1108237427203914667, -302724631043557911, 897911320510047954, -4301864720860679042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-73, -55, -25, -17, 51]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-73, -55, -25, -17, 51]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![4, 12, 7, 1, 0], ![23, 9, 14, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-73, -55, -25, -17, 51], ![34, -90, 22, 18, -34], ![-276, -48, -196, -188, 576], ![254, -238, 534, 226, -314], ![-30, -142, 134, 18, 98]]]
  hmulB := by decide  
  f := ![![![3061, -8100, 1980, 1620, -3060], ![0, -2790, 0, 0, 0]], ![![-539, 1676, -371, -307, 561], ![31, 558, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![224, -368, 125, 99, -204], ![28, -144, 0, 0, 0]], ![![2051, -5571, 1340, 1098, -2063], ![-18, -1908, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-4, -12, -7, 31, 0], ![-23, -9, -14, 0, 31]], ![![-38, -10, -20, -17, 51], ![24, 0, 12, 18, -34], ![-412, -96, -224, -188, 576], ![212, -4, 108, 226, -314], ![-76, -40, -44, 18, 98]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [26, 16, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 0, 8], [23, 30, 23], [0, 1]]
 g := ![![[23, 4, 1], [2, 15, 28], [16, 2, 10], [1]], ![[27, 24, 29, 25], [12, 22, 12, 25], [7, 20, 26, 19], [7, 5, 7, 16]], ![[4, 1, 29, 3], [20, 4, 0, 23], [15, 28, 1, 27], [19, 2, 18, 15]]]
 h' := ![![[22, 0, 8], [10, 26, 1], [18, 27, 20], [5, 15, 14], [0, 1]], ![[23, 30, 23], [28, 27, 21], [10, 13, 10], [19, 6, 13], [22, 0, 8]], ![[0, 1], [24, 9, 9], [26, 22, 1], [17, 10, 4], [23, 30, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 29], []]
 b := ![[], [8, 28, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [26, 16, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-118731393656, -66045220808, 10028461798, -62154510604, 277216044676]
  a := ![-271, -161, -59, -193, 592]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-201486528348, -58552757924, -110835954498, -62154510604, 277216044676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![0, 5, -3, -2, 6]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![0, 5, -3, -2, 6]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![8, 18, 1, 0, 0], ![17, 19, 0, 1, 0], ![20, 11, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![0, 5, -3, -2, 6], ![4, -2, 14, 2, -4], ![-28, -4, -2, 4, 58], ![-410, -185, -49, -292, 920], ![-140, -72, 2, -90, 326]]]
  hmulB := by decide  
  f := ![![![-486111, 205531, -1726589, -234094, 412186], ![295151, 3888888, 17360, 0, 0]], ![![-312480, 132121, -1109880, -150480, 264960], ![189720, 2499840, 11160, 0, 0]], ![![-306328, 129521, -1088030, -147518, 259746], ![185975, 2450624, 10940, 0, 0]], ![![-458097, 193691, -1627090, -220605, 388436], ![278118, 3664776, 16360, 0, 0]], ![![-424500, 179481, -1507756, -204424, 359943], ![257748, 3396000, 15160, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, -18, 31, 0, 0], ![-17, -19, 0, 31, 0], ![-20, -11, 0, 0, 31]], ![![-2, 1, -3, -2, 6], ![-2, -8, 14, 2, -4], ![-40, -22, -2, 4, 58], ![-434, -125, -49, -292, 920], ![-166, -64, 2, -90, 326]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 30], [0, 1]]
 g := ![![[23, 20], [28, 1], [3, 5], [19, 1]], ![[0, 11], [16, 30], [5, 26], [7, 30]]]
 h' := ![![[19, 30], [11, 19], [20, 1], [13, 6], [0, 1]], ![[0, 1], [0, 12], [8, 30], [3, 25], [19, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [21, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-170517, -82417, -4086, -95630, 388779]
  a := ![49, 16, 11, 34, -107]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-202829, -79628, -4086, -95630, 388779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![-73, -55, -25, -17, 51]] ![![31, 0, 0, 0, 0], ![0, 5, -3, -2, 6]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![961, 0, 0, 0, 0], ![0, 155, -93, -62, 186]], ![![-2263, -1705, -775, -527, 1581], ![310, -682, 434, 310, -682]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0]], ![![0, 5, -3, -2, 6]]], ![![![-73, -55, -25, -17, 51]], ![![10, -22, 14, 10, -22]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32381, 881, 22499, 25120, -62760]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![32381, 881, 22499, 25120, -62760]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![27, 24, 32, 5, 1]] where
  M :=![![![32381, 881, 22499, 25120, -62760], ![-201440, -5499, -139940, -156282, 390440], ![1253436, 34308, 870659, 972496, -2429526], ![-4526986, -124093, -3144315, -3512429, 8774746], ![-1070952, -29350, -743860, -830934, 2075843]]]
  hmulB := by decide  
  f := ![![![97, -267, -107, -62, 190]], ![![76, 15, -6, 2, -16]], ![![116, 128, 7, 60, -266]], ![![398, 239, -73, 201, -968]], ![![281, -42, -88, 37, -243]]]
  g := ![![![46673, 40733, 54887, 9160, -62760], ![-290360, -253407, -341460, -56986, 390440], ![1806774, 1576836, 2124743, 354598, -2429526], ![-6525544, -5695081, -7673951, -1280707, 8774746], ![-1543749, -1347286, -1815428, -302977, 2075843]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [27, 18, 29, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 24, 11, 14], [32, 19, 0, 30], [36, 30, 26, 30], [0, 1]]
 g := ![![[21, 19, 7, 12], [7, 32, 36], [34, 22, 22, 28], [1], []], ![[6, 14, 20, 14, 26, 17], [24, 27, 28], [36, 18, 12, 7, 25, 6], [34, 28, 26], [11, 36, 11]], ![[13, 0, 23, 4, 0, 10], [27, 2, 12], [7, 34, 29, 33, 23, 16], [17, 13, 3], [18, 6, 12]], ![[4, 17, 31, 9, 34, 27], [31, 26, 36], [22, 15, 29, 20, 30, 4], [10, 5, 25], [25, 12, 12]]]
 h' := ![![[25, 24, 11, 14], [8, 28, 8, 7], [7, 4, 32, 6], [10, 19, 8, 19], [0, 0, 1], [0, 1]], ![[32, 19, 0, 30], [29, 6, 16, 5], [23, 31, 24, 18], [32, 34, 14, 14], [32, 30, 10, 10], [25, 24, 11, 14]], ![[36, 30, 26, 30], [2, 35, 29, 32], [18, 17, 5, 7], [15, 16, 29, 15], [20, 27, 36, 22], [32, 19, 0, 30]], ![[0, 1], [15, 5, 21, 30], [1, 22, 13, 6], [16, 5, 23, 26], [29, 17, 27, 5], [36, 30, 26, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 34, 20], []]
 b := ![[], [], [3, 14, 14, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [27, 18, 29, 18, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4914322665073087, -2974923146087164, 771457692901198, -2454552436403210, 11655194078517916]
  a := ![-293, -88, -65, -209, 640]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8637961156352887, -7640529217041004, -10059317643774922, -1641365481864670, 11655194078517916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, -267, -107, -62, 190]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![97, -267, -107, -62, 190]] 
 ![![37, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![97, -267, -107, -62, 190], ![76, 15, -6, 2, -16], ![116, 128, 7, 60, -266], ![398, 239, -73, 201, -968], ![252, 4, -82, 70, -385]]]
  hmulB := by decide  
  f := ![![![32381, 881, 22499, 25120, -62760]], ![![-3694, -101, -2566, -2866, 7160]], ![![62757, 1713, 43598, 48688, -121638]], ![![-117100, -3211, -81333, -90857, 226978]], ![![-25444, -698, -17672, -19742, 49319]]]
  g := ![![![102, -267, -107, -62, 190], ![8, 15, -6, 2, -16], ![9, 128, 7, 60, -266], ![135, 239, -73, 201, -968], ![110, 4, -82, 70, -385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![32381, 881, 22499, 25120, -62760]] ![![97, -267, -107, -62, 190]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [4, 9, 12, 6, 38, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 40, 40, 39, 32], [31, 13, 8, 20, 9], [26, 22, 27, 9, 15], [39, 6, 7, 14, 26], [0, 1]]
 g := ![![[13, 21, 29, 0, 20], [18, 5, 25, 21], [13, 6, 32, 9], [1], []], ![[26, 6, 35, 36, 7, 31, 36, 37], [18, 9, 2, 5], [35, 15, 32, 10], [11, 4, 25, 0, 0, 27, 31, 39], [12, 4, 33, 40]], ![[39, 34, 19, 20, 31, 11, 19, 33], [30, 30, 38, 10], [20, 35, 25, 2], [25, 21, 11, 22, 34, 6, 40, 20], [7, 22, 29, 40]], ![[7, 24, 16, 5, 10, 14, 13, 30], [33, 2], [27, 15, 11, 2], [25, 3, 16, 13, 9, 34, 19, 24], [27, 39, 2, 20]], ![[31, 25, 9, 28, 38, 10, 3, 22], [24, 8, 28, 2], [10, 27, 21, 36], [9, 8, 0, 14, 17, 32, 6, 19], [16, 16, 9, 20]]]
 h' := ![![[30, 40, 40, 39, 32], [35, 30, 2, 2, 26], [5, 13, 3, 36, 12], [37, 32, 29, 35, 3], [0, 0, 1], [0, 1]], ![[31, 13, 8, 20, 9], [5, 7, 0, 39, 13], [6, 0, 22, 21, 28], [8, 26, 30, 23, 25], [32, 21, 39, 2, 33], [30, 40, 40, 39, 32]], ![[26, 22, 27, 9, 15], [21, 14, 34, 27, 21], [10, 12, 9, 10, 25], [7, 12, 2, 32, 24], [31, 40, 21, 24, 36], [31, 13, 8, 20, 9]], ![[39, 6, 7, 14, 26], [1, 13, 1, 3, 24], [25, 8, 39, 24], [16, 11, 17, 30, 24], [35, 7, 16, 26, 31], [26, 22, 27, 9, 15]], ![[0, 1], [26, 18, 4, 11, 39], [32, 8, 9, 32, 17], [21, 1, 4, 3, 6], [22, 14, 5, 30, 23], [39, 6, 7, 14, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 12, 2, 33], [], [], []]
 b := ![[], [21, 7, 11, 37, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [4, 9, 12, 6, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![276499659516632168346, 169124113658615729046, -45974115196861720178, 137267097442853916084, -657075415956482937764]
  a := ![331, 121, 75, 237, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6743894134552004106, 4124978381917456806, -1121319882850285858, 3347977986411071124, -16026229657475193604]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-79, -88, -34, -23, 69]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-79, -88, -34, -23, 69]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![29, 41, 29, 1, 0], ![16, 18, 26, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-79, -88, -34, -23, 69], ![46, -102, 16, 24, -46], ![-360, -60, -256, -272, 750], ![848, -121, 819, 688, -1538], ![126, -118, 188, 132, -226]]]
  hmulB := by decide  
  f := ![![![11358, -22288, 4022, 5725, -11247], ![473, -9804, 0, 0, 0]], ![![-874, 1939, -304, -456, 874], ![0, 817, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![6812, -13199, 2417, 3422, -6739], ![311, -5833, 0, 0, 0]], ![![3842, -7502, 1362, 1934, -3803], ![166, -3306, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-29, -41, -29, 43, 0], ![-16, -18, -26, 0, 43]], ![![-12, -9, -27, -23, 69], ![2, -6, 12, 24, -46], ![-104, -56, -276, -272, 750], ![128, -15, 485, 688, -1538], ![-2, -34, 52, 132, -226]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [2, 2, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 31, 11], [25, 11, 32], [0, 1]]
 g := ![![[26, 42, 6], [17, 16, 36], [42, 15], [39, 16, 1], []], ![[4, 18, 14, 25], [0, 0, 6, 13], [9, 38], [42, 30, 19, 41], [38, 35]], ![[22, 29, 19, 3], [42, 5, 39, 30], [30, 11], [1, 40, 29, 7], [17, 35]]]
 h' := ![![[34, 31, 11], [9, 33, 7], [23, 18, 37], [8, 19, 31], [0, 0, 1], [0, 1]], ![[25, 11, 32], [5, 8, 10], [3, 9, 3], [35, 7, 34], [5, 27, 11], [34, 31, 11]], ![[0, 1], [26, 2, 26], [23, 16, 3], [13, 17, 21], [32, 16, 31], [25, 11, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 15], []]
 b := ![[], [13, 12, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [2, 2, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39584955354, 24095646736, -6409496104, 19707946328, -93982220032]
  a := ![152, 56, 30, 98, -332]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22599303078, 21110460648, 43385994912, 19707946328, -93982220032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 43, 19, 12, -36]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![19, 43, 19, 12, -36]] 
 ![![43, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![19, 43, 19, 12, -36], ![-24, 31, -10, -10, 24], ![92, -4, 87, 68, -182], ![-246, 27, -217, -171, 456], ![-56, 32, -46, -38, 99]]]
  hmulB := by decide  
  f := ![![![33, 1, 15, 22, -62]], ![![4, 1, 0, 2, -8]], ![![54, 10, 21, 36, -110]], ![![4, 37, -57, -17, -34]], ![![41, 19, -5, 20, -91]]]
  g := ![![![7, 43, 19, 12, -36], ![-16, 31, -10, -10, 24], ![76, -4, 87, 68, -182], ![-194, 27, -217, -171, 456], ![-47, 32, -46, -38, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![21, 1, 0, 0, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![21, 1, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![21, 1, 0, 0, 0], ![0, 21, 1, 0, 0], ![0, 0, 22, 2, 0], ![-38, -14, -9, -7, 83], ![-12, -5, -1, -8, 48]]]
  hmulB := by decide  
  f := ![![![4151754, -58394, 44667425, 4064876, -41168], ![-8462615, 536769, -87320186, 21328, 0]], ![![2075866, -29208, 22333734, 2032440, -20584], ![-4231285, 268406, -43660136, 10664, 0]], ![![3113810, -43791, 33500558, 3048656, -30876], ![-6346950, 402567, -65490118, 15996, 0]], ![![3373270, -47453, 36292285, 3302712, -33449], ![-6875813, 436138, -70947656, 17329, 0]], ![![3668988, -51591, 39473539, 3592216, -36381], ![-7478582, 474327, -77166676, 18848, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-21, 43, 0, 0, 0], ![-32, 0, 43, 0, 0], ![-35, 0, 0, 43, 0], ![-38, 0, 0, 0, 43]], ![![0, 1, 0, 0, 0], ![-11, 21, 1, 0, 0], ![-18, 0, 22, 2, 0], ![-55, -14, -9, -7, 83], ![-33, -5, -1, -8, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-79, -88, -34, -23, 69]] ![![19, 43, 19, 12, -36]]
  ![![43, 0, 0, 0, 0], ![-49, 184, 96, 60, -179]] where
 M := ![![![817, 1849, 817, 516, -1548]], ![![-723, -4402, -1762, -1069, 3263]]]
 hmul := by decide  
 g := ![![![![68, -141, -77, -48, 143], ![43, 0, 0, 0, 0]]], ![![![-2, -158, -70, -43, 130], ![13, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-49, 184, 96, 60, -179]] ![![43, 0, 0, 0, 0], ![21, 1, 0, 0, 0]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![1849, 0, 0, 0, 0], ![903, 43, 0, 0, 0]], ![![-2107, 7912, 4128, 2580, -7697], ![-1161, 3870, 1935, 1204, -3612]]]
 hmul := by decide  
 g := ![![![![43, 0, 0, 0, 0]], ![![21, 1, 0, 0, 0]]], ![![![-49, 184, 96, 60, -179]], ![![-27, 90, 45, 28, -84]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-5, 11, -3, -2, 6]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-5, 11, -3, -2, 6]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![9, 11, 1, 0, 0], ![40, 9, 0, 1, 0], ![17, 26, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-5, 11, -3, -2, 6], ![4, -7, 20, 2, -4], ![-28, -4, -1, 16, 58], ![-638, -269, -103, -465, 1418], ![-212, -102, -4, -138, 483]]]
  hmulB := by decide  
  f := ![![![9914701, -16857950, 54165660, 5052484, -9714112], ![-9912676, -128775394, 16168, 0, 0]], ![![3458216, -5879998, 18892808, 1762290, -3388252], ![-3457508, -44916443, 5640, 0, 0]], ![![2703024, -4595947, 14767070, 1377448, -2648338], ![-2702473, -35107765, 4408, 0, 0]], ![![9100252, -15473142, 49716204, 4637445, -8916140], ![-9098424, -118197101, 14840, 0, 0]], ![![5499224, -9350321, 30043175, 2802378, -5387967], ![-5498101, -71425728, 8968, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-9, -11, 47, 0, 0], ![-40, -9, 0, 47, 0], ![-17, -26, 0, 0, 47]], ![![0, -2, -3, -2, 6], ![-4, -3, 20, 2, -4], ![-35, -35, -1, 16, 58], ![-111, -677, -103, -465, 1418], ![-61, -242, -4, -138, 483]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [16, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 46], [0, 1]]
 g := ![![[29, 3], [19, 36], [14, 3], [24, 36], [1]], ![[0, 44], [0, 11], [32, 44], [5, 11], [1]]]
 h' := ![![[6, 46], [25, 35], [11, 6], [39, 12], [31, 6], [0, 1]], ![[0, 1], [0, 12], [0, 41], [17, 35], [20, 41], [6, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [30, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [16, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27571282, -12527206, -1850258, -15902454, 62256850]
  a := ![-617, -216, -130, -435, 1348]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9216750, -31228306, -1850258, -15902454, 62256850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![5, -20, -3, -2, 6]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![5, -20, -3, -2, 6]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![19, 38, 1, 0, 0], ![29, 44, 0, 1, 0], ![20, 46, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![5, -20, -3, -2, 6], ![4, 3, -11, 2, -4], ![-28, -4, -22, -46, 58], ![540, 165, 176, 413, -1155], ![160, 53, 27, 110, -344]]]
  hmulB := by decide  
  f := ![![![5568675, 3747837, -15099007, 2711146, -5378768], ![-840642, -64306105, 10716, 0, 0]], ![![3711846, 2498154, -10064367, 1807138, -3585264], ![-560334, -42863765, 7144, 0, 0]], ![![5232487, 3521589, -14187466, 2547474, -5054052], ![-789866, -60423895, 10070, 0, 0]], ![![6910912, 4651187, -18738370, 3364623, -6675230], ![-1043275, -79806015, 13300, 0, 0]], ![![6002518, 4039832, -16275340, 2922368, -5797821], ![-906118, -69316070, 11552, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-19, -38, 47, 0, 0], ![-29, -44, 0, 47, 0], ![-20, -46, 0, 0, 47]], ![![0, -2, -3, -2, 6], ![5, 11, -11, 2, -4], ![12, 4, -22, -46, 58], ![177, 605, 176, 413, -1155], ![71, 213, 27, 110, -344]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [18, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 46], [0, 1]]
 g := ![![[33, 34], [15, 24], [45, 25], [24, 7], [1]], ![[0, 13], [0, 23], [0, 22], [2, 40], [1]]]
 h' := ![![[17, 46], [12, 38], [36, 20], [38, 42], [29, 17], [0, 1]], ![[0, 1], [0, 9], [0, 27], [0, 5], [36, 30], [17, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [33, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [18, 30, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9461, -1780, -4613, -7011, 19398]
  a := ![-11, -8, -3, -9, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2265, -8730, -4613, -7011, 19398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 0, -1, 2, 0], ![-38, -14, -9, -30, 83], ![-12, -5, -1, -8, 25]]]
  hmulB := by decide  
  f := ![![![801749, -387286, 684000, -1348054, -34362], ![18471376, -1739, 31971139, 19458, 0]], ![![801747, -387285, 683999, -1348052, -34362], ![18471330, -1739, 31971092, 19458, 0]], ![![766889, -370446, 654259, -1289440, -32868], ![17668242, -1644, 30581020, 18612, 0]], ![![766891, -370448, 654261, -1289443, -32868], ![17668288, -1668, 30581091, 18612, 0]], ![![324113, -156562, 276510, -544958, -13891], ![7467192, -673, 12924503, 7866, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-45, 47, 0, 0, 0], ![-43, 0, 47, 0, 0], ![-45, 0, 0, 47, 0], ![-19, 0, 0, 0, 47]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-1, 0, -1, 2, 0], ![16, -14, -9, -30, 83], ![3, -5, -1, -8, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![-5, 11, -3, -2, 6]] ![![47, 0, 0, 0, 0], ![5, -20, -3, -2, 6]]
  ![![47, 0, 0, 0, 0], ![-44, -405, -164, -103, 310]] where
 M := ![![![2209, 0, 0, 0, 0], ![235, -940, -141, -94, 282]], ![![-235, 517, -141, -94, 282], ![-17, 133, -230, 4, -2]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![49, 385, 161, 101, -304], ![47, 0, 0, 0, 0]]], ![![![-5, 11, -3, -2, 6], ![0, 0, 0, 0, 0]], ![![9, 89, 30, 22, -66], ![10, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![-44, -405, -164, -103, 310]] ![![47, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![-94, 47, 0, 0, 0]], ![![-2068, -19035, -7708, -4841, 14570], ![282, 658, 376, 282, -799]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![-44, -405, -164, -103, 310]], ![![6, 14, 8, 6, -17]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-15, 2, 8, 5, -15]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-15, 2, 8, 5, -15]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![30, 13, 22, 1, 0], ![11, 36, 28, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-15, 2, 8, 5, -15], ![-10, -10, -20, -4, 10], ![32, -4, -4, -8, -62], ![508, 229, 65, 360, -1138], ![166, 90, 0, 112, -406]]]
  hmulB := by decide  
  f := ![![![1691, 1520, 3000, 566, -1390], ![530, 8162, 0, 0, 0]], ![![-110, -109, -220, -44, 110], ![0, -583, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![935, 833, 1642, 308, -755], ![317, 4477, 0, 0, 0]], ![![272, 242, 476, 89, -218], ![95, 1298, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-30, -13, -22, 53, 0], ![-11, -36, -28, 0, 53]], ![![0, 9, 6, 5, -15], ![0, -6, -4, -4, 10], ![18, 44, 36, -8, -62], ![42, 689, 453, 360, -1138], ![24, 250, 168, 112, -406]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [44, 34, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 15, 50], [52, 37, 3], [0, 1]]
 g := ![![[44, 43, 7], [51, 7], [28, 40, 43], [2, 46], [1]], ![[32, 6, 22, 31], [42, 29], [0, 46, 31, 34], [11, 24], [5, 43, 22, 26]], ![[25, 46, 52, 19], [12, 4], [26, 11, 36, 19], [41, 49], [2, 24, 4, 27]]]
 h' := ![![[25, 15, 50], [45, 45, 31], [40, 40, 31], [46, 52, 19], [9, 19, 24], [0, 1]], ![[52, 37, 3], [49, 3, 5], [25, 34, 20], [52, 45, 17], [35, 40, 36], [25, 15, 50]], ![[0, 1], [15, 5, 17], [15, 32, 2], [22, 9, 17], [17, 47, 46], [52, 37, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 32], []]
 b := ![[], [14, 3, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [44, 34, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-171221407560, -94801140314, 13817605818, -89822351968, 399440926718]
  a := ![-309, -111, -66, -223, 675]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35290585706, -251075168426, -173479935830, -89822351968, 399440926718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-3, -23, -3, -2, 6]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-3, -23, -3, -2, 6]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![52, 10, 1, 0, 0], ![32, 24, 0, 1, 0], ![45, 18, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-3, -23, -3, -2, 6], ![4, -5, -14, 2, -4], ![-28, -4, -33, -52, 58], ![654, 207, 203, 489, -1404], ![196, 68, 30, 134, -433]]]
  hmulB := by decide  
  f := ![![![92098385, -94427862, -311858446, 46449956, -94428916], ![40974512, -1189433950, 19822, 0, 0]], ![![8371574, -8583311, -28347356, 4222216, -8583416], ![3724522, -108117350, 1802, 0, 0]], ![![91782264, -94103742, -310788013, 46290520, -94104796], ![40833876, -1185351300, 19754, 0, 0]], ![![59397473, -60899835, -201128431, 29957203, -60900514], ![26425895, -767107600, 12784, 0, 0]], ![![81039918, -83089687, -274412877, 40872602, -83090617], ![36054611, -1046615850, 17442, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-52, -10, 53, 0, 0], ![-32, -24, 0, 53, 0], ![-45, -18, 0, 0, 53]], ![![-1, -1, -3, -2, 6], ![16, 3, -14, 2, -4], ![14, 10, -33, -52, 58], ![710, 221, 203, 489, -1404], ![261, 82, 30, 134, -433]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [42, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 52], [0, 1]]
 g := ![![[2, 24], [29], [9, 49], [6], [22, 1]], ![[0, 29], [29], [27, 4], [6], [44, 52]]]
 h' := ![![[22, 52], [50, 17], [46, 33], [12, 46], [30, 18], [0, 1]], ![[0, 1], [0, 36], [30, 20], [17, 7], [2, 35], [22, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [42, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [42, 31, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3275202, -1422750, -317106, -1923234, 7346340]
  a := ![-217, -78, -49, -155, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4826934, -1591098, -317106, -1923234, 7346340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0, 0], ![-15, 2, 8, 5, -15]] ![![53, 0, 0, 0, 0], ![-3, -23, -3, -2, 6]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![2809, 0, 0, 0, 0], ![-159, -1219, -159, -106, 318]], ![![-795, 106, 424, 265, -795], ![159, 318, 318, 53, -159]]]
 hmul := by decide  
 g := ![![![![53, 0, 0, 0, 0]], ![![-3, -23, -3, -2, 6]]], ![![![-15, 2, 8, 5, -15]], ![![3, 6, 6, 1, -3]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![185, 5932, 1670, 892, -2926]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![185, 5932, 1670, 892, -2926]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![20, 21, 45, 47, 1]] where
  M :=![![![185, 5932, 1670, 892, -2926], ![1216, 2327, 2500, 1772, -4966], ![-7744, 1238, -6155, -4888, 12994], ![18780, -2760, 16118, 12745, -33930], ![4856, 2432, 5144, 3836, -10507]]]
  hmulB := by decide  
  f := ![![![851, 24, 590, 660, -1650]], ![![-5280, -139, -3676, -4100, 10230]], ![![33040, 970, 22855, 25608, -64090]], ![![-118532, -2996, -82706, -92101, 229562]], ![![-71288, -1699, -49893, -55441, 137987]]]
  g := ![![![995, 1142, 2260, 2346, -2926], ![1704, 1807, 3830, 3986, -4966], ![-4536, -4604, -10015, -10434, 12994], ![11820, 12030, 26152, 27245, -33930], ![3644, 3781, 8101, 8435, -10507]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [30, 39, 53, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 11, 54, 32], [39, 14, 36, 38], [10, 33, 28, 48], [0, 1]]
 g := ![![[24, 37, 33, 45], [33, 0, 18, 48], [11, 33, 53], [23, 18, 37, 1], []], ![[34, 57, 17, 26, 34, 34], [47, 26, 14, 30, 29, 14], [57, 18, 57], [34, 35, 29, 4, 9, 10], [56, 42, 37, 53, 5, 23]], ![[51, 9, 26, 33, 3, 55], [7, 19, 15, 41, 38, 50], [9, 43, 51], [20, 5, 7, 46, 44, 42], [29, 18, 49, 5, 30, 2]], ![[29, 37, 11, 27, 47, 17], [6, 33, 51, 11, 44, 9], [47, 54, 36], [45, 31, 37, 13, 34, 45], [2, 8, 25, 29, 34, 26]]]
 h' := ![![[47, 11, 54, 32], [13, 47, 34, 35], [53, 8, 24, 15], [18, 38, 37, 17], [0, 0, 0, 1], [0, 1]], ![[39, 14, 36, 38], [30, 30, 58, 7], [23, 22, 25, 10], [50, 19, 2, 23], [14, 10, 40, 57], [47, 11, 54, 32]], ![[10, 33, 28, 48], [10, 55, 22, 11], [44, 58, 40, 46], [14, 8, 38, 13], [39, 25, 1, 23], [39, 14, 36, 38]], ![[0, 1], [21, 45, 4, 6], [47, 30, 29, 47], [49, 53, 41, 6], [55, 24, 18, 37], [10, 33, 28, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 51, 34], []]
 b := ![[], [], [46, 58, 34, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [30, 39, 53, 22, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3480204448173738, -2113772583346728, 556649569621648, -1734898150541673, 8259178866673412]
  a := ![-260, -92, -56, -183, 568]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2858708165790542, -2975534386160820, -6289938973401388, -6608750930240543, 8259178866673412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![851, 24, 590, 660, -1650]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![851, 24, 590, 660, -1650]] 
 ![![59, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![851, 24, 590, 660, -1650], ![-5280, -139, -3676, -4100, 10230], ![33040, 970, 22855, 25608, -64090], ![-118532, -2996, -82706, -92101, 229562], ![-27928, -640, -19584, -21732, 54039]]]
  hmulB := by decide  
  f := ![![![185, 5932, 1670, 892, -2926]], ![![99, 2553, 750, 408, -1324]], ![![-56, 2434, 575, 280, -970]], ![![450, 4176, 1462, 851, -2658]], ![![214, 4264, 1276, 700, -2261]]]
  g := ![![![469, 24, 590, 660, -1650], ![-2899, -139, -3676, -4100, 10230], ![18246, 970, 22855, 25608, -64090], ![-64950, -2996, -82706, -92101, 229562], ![-15234, -640, -19584, -21732, 54039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![185, 5932, 1670, 892, -2926]] ![![851, 24, 590, 660, -1650]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [6, 21, 36, 57, 47, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 36, 7, 53, 29], [5, 18, 13, 1, 26], [21, 9, 28, 22, 27], [22, 58, 13, 46, 40], [0, 1]]
 g := ![![[26, 53, 21, 24, 46], [42, 11, 13, 19], [39, 21, 59, 13, 13], [17, 14, 1], []], ![[10, 44, 5, 54, 22, 13, 15, 50], [6, 14, 23, 16], [37, 57, 5, 8, 29, 17, 4, 43], [50, 28, 25, 19, 11, 47, 42, 10], [38, 45, 52, 25, 32, 21, 36, 50]], ![[9, 34, 38, 43, 1, 7, 30, 31], [41, 5, 11, 5], [49, 56, 21, 0, 30, 51, 55, 59], [26, 31, 52, 2, 59, 53, 10, 2], [30, 35, 7, 57, 22, 9, 5, 8]], ![[49, 49, 6, 44, 41, 16, 0, 16], [16, 7, 37, 41], [19, 1, 60, 44, 56, 8, 21, 19], [28, 27, 19, 58, 30, 4, 2, 46], [37, 10, 3, 11, 12, 33, 10, 41]], ![[26, 47, 19, 0, 56, 48, 16, 33], [26, 51, 35, 39], [43, 19, 54, 45, 10, 44, 51, 51], [6, 35, 24, 1, 24, 47, 53, 11], [59, 3, 28, 7, 23, 3, 12, 11]]]
 h' := ![![[27, 36, 7, 53, 29], [31, 47, 50, 10, 30], [10, 4, 47, 46, 43], [20, 47, 3, 31, 14], [0, 0, 0, 1], [0, 1]], ![[5, 18, 13, 1, 26], [5, 50, 17, 33, 32], [38, 58, 60, 48, 57], [10, 32, 44, 13, 16], [57, 11, 52, 52, 20], [27, 36, 7, 53, 29]], ![[21, 9, 28, 22, 27], [25, 22, 28, 26, 24], [24, 33, 30, 7, 35], [24, 16, 55, 42, 40], [6, 22, 13, 13, 48], [5, 18, 13, 1, 26]], ![[22, 58, 13, 46, 40], [13, 6, 8, 56, 51], [32, 6, 21, 13, 38], [55, 12, 8, 4, 16], [11, 29, 22, 2, 14], [21, 9, 28, 22, 27]], ![[0, 1], [22, 58, 19, 58, 46], [42, 21, 25, 8, 10], [34, 15, 12, 32, 36], [46, 60, 35, 54, 40], [22, 58, 13, 46, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 7, 28, 23], [], [], []]
 b := ![[], [25, 15, 6, 34, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [6, 21, 36, 57, 47, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1018648218438431958232, 622967295444487123932, -169224704247049615604, 505751797293661627574, -2420646392202577305792]
  a := ![419, 163, 85, 299, -915]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16699151121941507512, 10212578613844051212, -2774175479459829764, 8291013070387895534, -39682727741025857472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB3690I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB3690I1 : PrimesBelowBoundCertificateInterval O 23 61 3690 where
  m := 9
  g := ![1, 2, 2, 1, 3, 3, 2, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB3690I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![20511149]
    · exact ![29791, 961]
    · exact ![1874161, 37]
    · exact ![115856201]
    · exact ![79507, 43, 43]
    · exact ![2209, 2209, 47]
    · exact ![148877, 2809]
    · exact ![12117361, 59]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I31N1, I37N1, I43N1, I43N2, I47N0, I47N1, I47N2, I53N1, I59N1]
  Il := ![[], [I31N1], [I37N1], [], [I43N1, I43N2], [I47N0, I47N1, I47N2], [I53N1], [I59N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
