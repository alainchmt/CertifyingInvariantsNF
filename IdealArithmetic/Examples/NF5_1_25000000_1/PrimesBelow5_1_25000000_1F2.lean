
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0, 0, 0]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]] where
  M :=![![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![0, 0, 0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [31, 51, 7, 58, 38, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 41, 54, 8, 56], [50, 13, 2, 4, 28], [23, 3, 9, 15, 18], [3, 9, 2, 40, 32], [0, 1]]
 g := ![![[8, 45, 30, 43, 39], [32, 66, 49, 44, 54], [24, 2, 21, 56], [47, 46, 29, 1], [], []], ![[24, 27, 49, 28, 28, 8, 53, 15], [22, 11, 5, 21, 13, 51, 61, 60], [12, 27, 13, 47], [17, 15, 51, 39], [41, 1, 47, 22], [65, 8, 50, 54]], ![[28, 15, 33, 9, 1, 29, 7, 38], [4, 49, 21, 25, 64, 53, 58, 34], [5, 27, 60, 14], [6, 60, 53, 4], [0, 24, 15, 10], [18, 9, 46, 47]], ![[4, 1, 34, 34, 44, 1, 22, 12], [51, 33, 58, 42, 62, 59, 45, 34], [10, 56, 25, 23], [18, 11, 8, 14], [50, 26, 6, 62], [20, 25, 20, 56]], ![[0, 54, 41, 44, 2, 42, 14, 31], [35, 66, 20, 10, 34, 60, 50, 42], [26, 59, 12, 29], [13, 27, 4, 35], [23, 59, 45, 60], [58, 60, 29, 19]]]
 h' := ![![[20, 41, 54, 8, 56], [13, 2, 32, 6, 21], [14, 52, 55, 57, 56], [17, 63, 44, 65, 49], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[50, 13, 2, 4, 28], [57, 59, 5, 31, 36], [39, 21, 50, 25, 5], [64, 23, 26, 7, 28], [51, 10, 53, 64, 46], [60, 20, 21, 48, 42], [20, 41, 54, 8, 56]], ![[23, 3, 9, 15, 18], [56, 10, 45, 39, 56], [34, 49, 54, 29, 41], [16, 21, 42, 49, 58], [1, 55, 10, 66, 65], [66, 36, 33, 31, 55], [50, 13, 2, 4, 28]], ![[3, 9, 2, 40, 32], [31, 48, 20, 32, 36], [26, 50, 66, 35, 11], [1, 9, 34, 19, 36], [31, 1, 61, 30, 9], [43, 18, 63, 3, 14], [23, 3, 9, 15, 18]], ![[0, 1], [0, 15, 32, 26, 52], [60, 29, 43, 55, 21], [14, 18, 55, 61, 30], [22, 1, 10, 41, 13], [20, 60, 16, 52, 23], [3, 9, 2, 40, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 38, 39, 65], [], [], []]
 b := ![[], [6, 65, 57, 48, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [31, 51, 7, 58, 38, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23529847573275, -3210423351547, -23237566929251, -39783755566304, 39028275152279]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-351191754825, -47916766441, -346829357153, -593787396512, 582511569437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 1350125107 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 1, 3, 0, 7]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-11, 1, 3, 0, 7]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![28, 48, 1, 0, 0], ![5, 64, 0, 1, 0], ![27, 10, 0, 0, 1]] where
  M :=![![![-11, 1, 3, 0, 7], ![-28, -8, 7, -2, 21], ![-80, -17, 14, -4, 49], ![0, -4, -2, -3, 0], ![-56, -14, 10, -4, 33]]]
  hmulB := by decide  
  f := ![![![-1, 9, 1, 2, -7]], ![![24, -4, 3, 8, -7]], ![![16, 1, 2, 6, -7]], ![![21, -3, 3, 7, -7]], ![![3, 3, 1, 2, -4]]]
  g := ![![![-4, -3, 3, 0, 7], ![-11, -6, 7, -2, 21], ![-25, -13, 14, -4, 49], ![1, 4, -2, -3, 0], ![-17, -8, 10, -4, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 70], [0, 1]]
 g := ![![[58, 32], [15, 45], [24, 1], [27], [8], [1]], ![[0, 39], [0, 26], [0, 70], [27], [8], [1]]]
 h' := ![![[47, 70], [55, 23], [17, 51], [47, 70], [27, 58], [51, 47], [0, 1]], ![[0, 1], [0, 48], [0, 20], [0, 1], [55, 13], [59, 24], [47, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [24, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [20, 24, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2307615, -825532, -2910561, -3898614, 5397332]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-662631, 4710132, -2910561, -3898614, 5397332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -32, 0, -8, 13]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![27, -32, 0, -8, 13]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![10, 45, 1, 0, 0], ![60, 42, 0, 1, 0], ![39, 7, 0, 0, 1]] where
  M :=![![![27, -32, 0, -8, 13], ![-36, 43, 0, 14, -17], ![40, -64, -13, -36, 47], ![-40, 46, 20, 23, -47], ![12, -10, 6, 6, -5]]]
  hmulB := by decide  
  f := ![![![209, 54, -38, 14, -129]], ![![488, 143, -78, 36, -289]], ![![354, 103, -57, 26, -210]], ![![464, 130, -78, 33, -279]], ![![173, 47, -30, 12, -105]]]
  g := ![![![0, 3, 0, -8, 13], ![-3, -6, 0, 14, -17], ![7, 24, -13, -36, 47], ![3, -21, 20, 23, -47], ![-3, -7, 6, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [47, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 70], [0, 1]]
 g := ![![[3, 19], [7, 57], [68, 1], [58], [1], [1]], ![[22, 52], [64, 14], [69, 70], [58], [1], [1]]]
 h' := ![![[1, 70], [26, 27], [70, 25], [2, 70], [32, 49], [24, 1], [0, 1]], ![[0, 1], [53, 44], [24, 46], [1, 1], [10, 22], [25, 70], [1, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [41, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [47, 70, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16214, -3048, -14678, -24912, 25344]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8970, 21498, -14678, -24912, 25344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, -1, 0, -2]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![1, -1, -1, 0, -2]] 
 ![![71, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![1, -1, -1, 0, -2], ![8, 0, -3, 0, -6], ![24, 5, -6, 0, -18], ![4, 2, 2, 3, -3], ![20, 4, -4, 2, -13]]]
  hmulB := by decide  
  f := ![![![-129, 133, 3, 36, -54]], ![![-87, 89, 2, 24, -36]], ![![-27, 28, 1, 8, -12]], ![![-61, 63, 1, 17, -25]], ![![-8, 8, 0, 2, -3]]]
  g := ![![![1, -1, -1, 0, -2], ![1, 0, -3, 0, -6], ![-1, 5, -6, 0, -18], ![-3, 2, 2, 3, -3], ![-2, 4, -4, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-11, 1, 3, 0, 7]] ![![27, -32, 0, -8, 13]]
  ![![-129, 133, 3, 36, -54]] where
 M := ![![![-129, 133, 3, 36, -54]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-129, 133, 3, 36, -54]] ![![1, -1, -1, 0, -2]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [58, 33, 12, 33, 51, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 55, 63, 53, 51], [44, 12, 41, 65, 14], [11, 11, 27, 28, 64], [72, 67, 15, 0, 17], [0, 1]]
 g := ![![[66, 15, 45, 7, 67], [22, 1, 46, 25], [38, 0, 38, 71], [61, 59, 13, 22, 1], [], []], ![[30, 48, 72, 58, 72, 10, 20, 29], [53, 63, 28, 64], [65, 44, 13, 69], [22, 37, 28, 71, 59, 50, 72, 56], [6, 4, 33, 1], [27, 66, 67, 46]], ![[10, 10, 0, 71, 54, 53, 49, 62], [28, 3, 7, 72], [10, 56, 60, 55], [22, 41, 66, 49, 44, 65, 52, 62], [40, 6, 17, 24], [29, 0, 0, 50]], ![[58, 19, 48, 51, 55, 62, 53, 23], [15, 59, 21, 1], [51, 53, 7, 54], [36, 48, 6, 69, 62, 32, 20, 41], [25, 67, 68, 8], [38, 45, 37, 8]], ![[40, 63, 15, 11, 29, 18, 62, 7], [66, 39, 68, 18], [65, 9, 50, 37], [26, 12, 60, 34, 22, 31, 12, 29], [58, 50, 47, 67], [35, 33, 7, 70]]]
 h' := ![![[41, 55, 63, 53, 51], [57, 4, 44, 1, 33], [47, 41, 25, 65, 68], [39, 40, 71, 27, 61], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[44, 12, 41, 65, 14], [27, 11, 51, 42, 41], [53, 7, 32, 5, 8], [63, 13, 51, 43, 19], [29, 45, 3, 16, 30], [42, 10, 51, 42, 1], [41, 55, 63, 53, 51]], ![[11, 11, 27, 28, 64], [53, 56, 10, 36, 40], [61, 31, 35, 63, 46], [38, 35, 8, 18, 37], [0, 6, 42, 69, 33], [35, 26, 46, 0, 30], [44, 12, 41, 65, 14]], ![[72, 67, 15, 0, 17], [63, 61, 28, 45, 29], [35, 61, 43, 36, 1], [0, 6, 2, 25, 45], [71, 40, 20, 19, 67], [34, 28, 59, 67, 9], [11, 11, 27, 28, 64]], ![[0, 1], [4, 14, 13, 22, 3], [67, 6, 11, 50, 23], [25, 52, 14, 33, 57], [0, 55, 8, 42, 15], [15, 9, 62, 37, 33], [72, 67, 15, 0, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 12, 4, 43], [], [], []]
 b := ![[], [13, 10, 43, 64, 65], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [58, 33, 12, 33, 51, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9122648016321646, 7688332366173974, 36588911816179304, 38875865863560146, -58109313024926079]
  a := ![-107, -61, -118, -103, 375]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![124967781045502, 105319621454438, 501217970084648, 532546107720002, -796017986642823]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 2073071593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![669, -795, -21, -218, 354]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![669, -795, -21, -218, 354]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![11, 31, 1, 0, 0], ![8, 4, 0, 1, 0], ![28, 15, 0, 0, 1]] where
  M :=![![![669, -795, -21, -218, 354], ![-980, 1084, 35, 298, -464], ![1260, -1541, -38, -422, 694], ![-868, 1016, 28, 279, -449], ![188, -272, -4, -74, 131]]]
  hmulB := by decide  
  f := ![![![35, 3, -9, 10, -2]], ![![-12, 6, -55, -82, 64]], ![![-1, 4, -20, -30, 20]], ![![8, 0, -4, 1, 3]], ![![12, 2, -15, -12, 13]]]
  g := ![![![-92, -58, -21, -218, 354], ![117, 73, 35, 298, -464], ![-182, -115, -38, -422, 694], ![116, 73, 28, 279, -449], ![-36, -23, -4, -74, 131]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [65, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 78], [0, 1]]
 g := ![![[35, 62], [49, 38], [2, 10], [0, 22], [19], [1]], ![[0, 17], [25, 41], [4, 69], [36, 57], [19], [1]]]
 h' := ![![[16, 78], [54, 46], [28, 14], [0, 57], [67, 41], [14, 16], [0, 1]], ![[0, 1], [0, 33], [15, 65], [43, 22], [12, 38], [33, 63], [16, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [75, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [65, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92285, 4314, -15614, -90310, 35641]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2481, 3987, -15614, -90310, 35641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 35, -15, 8, -59]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![107, 35, -15, 8, -59]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![31, 35, 1, 0, 0], ![49, 20, 0, 1, 0], ![9, 20, 0, 0, 1]] where
  M :=![![![107, 35, -15, 8, -59], ![220, 76, -27, 18, -121], ![448, 157, -50, 44, -237], ![-64, -20, 2, -13, 48], ![280, 102, -34, 20, -145]]]
  hmulB := by decide  
  f := ![![![889, -1029, -29, -282, 451]], ![![-1240, 1424, 41, 392, -621]], ![![-179, 202, 6, 56, -87]], ![![223, -261, -7, -71, 115]], ![![-209, 239, 7, 66, -104]]]
  g := ![![![9, 20, -15, 8, -59], ![16, 39, -27, 18, -121], ![25, 73, -50, 44, -237], ![1, -10, 2, -13, 48], ![21, 48, -34, 20, -145]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [14, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 78], [0, 1]]
 g := ![![[1, 8], [41, 40], [41, 49], [37, 8], [38], [1]], ![[47, 71], [34, 39], [66, 30], [4, 71], [38], [1]]]
 h' := ![![[65, 78], [58, 18], [58, 44], [35, 7], [59, 18], [65, 65], [0, 1]], ![[0, 1], [43, 61], [74, 35], [16, 72], [44, 61], [24, 14], [65, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [71, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [14, 14, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-82498, 16672, 40840, -36232, -53396]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11486, 4808, 40840, -36232, -53396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, -2, -2, 3]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-1, 0, -2, -2, 3]] 
 ![![79, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-1, 0, -2, -2, 3], ![-8, 1, 4, -4, -5], ![28, 4, 25, 46, -43], ![8, -12, -46, -33, 71], ![-12, -2, -14, -22, 23]]]
  hmulB := by decide  
  f := ![![![-347, -166, -8, -32, 93]], ![![-61, -31, -2, -6, 16]], ![![-300, -146, -9, -28, 77]], ![![-162, -78, -4, -15, 43]], ![![-192, -94, -6, -18, 49]]]
  g := ![![![1, 0, -2, -2, 3], ![1, 1, 4, -4, -5], ![-20, 4, 25, 46, -43], ![18, -12, -46, -33, 71], ![10, -2, -14, -22, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![669, -795, -21, -218, 354]] ![![107, 35, -15, 8, -59]]
  ![![347, 166, 8, 32, -93]] where
 M := ![![![347, 166, 8, 32, -93]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![347, 166, 8, 32, -93]] ![![-1, 0, -2, -2, 3]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 24, -6, 6, -32]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![63, 24, -6, 6, -32]] 
 ![![83, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![63, 24, -6, 6, -32], ![116, 45, -12, 10, -54], ![196, 84, -19, 10, -92], ![-40, -14, 14, 7, 8], ![128, 52, -8, 16, -61]]]
  hmulB := by decide  
  f := ![![![28469, -32836, -950, -9014, 14384]], ![![3297, -3803, -110, -1044, 1666]], ![![16095, -18564, -537, -5096, 8132]], ![![5391, -6218, -180, -1707, 2724]], ![![4914, -5668, -164, -1556, 2483]]]
  g := ![![![5, 24, -6, 6, -32], ![9, 45, -12, 10, -54], ![15, 84, -19, 10, -92], ![-9, -14, 14, 7, 8], ![6, 52, -8, 16, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 6, 20, 8, -30]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-11, 6, 20, 8, -30]] 
 ![![83, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-11, 6, 20, 8, -30], ![104, -7, 14, 100, -34], ![-64, -82, -379, -376, 598], ![-404, 120, 352, -45, -500], ![0, 44, 188, 160, -293]]]
  hmulB := by decide  
  f := ![![![4471, 1118, -872, 304, -2886]], ![![2879, 723, -558, 196, -1852]], ![![3259, 832, -623, 224, -2084]], ![![2511, 630, -488, 171, -1618]], ![![3269, 830, -628, 224, -2095]]]
  g := ![![![-1, 6, 20, 8, -30], ![-37, -7, 14, 100, -34], ![103, -82, -379, -376, 598], ![57, 120, 352, -45, -500], ![-41, 44, 188, 160, -293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 0, 0, 1]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-1, 0, 0, 0, 1]] 
 ![![83, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 0, 0, 1], ![-4, -1, 0, -2, 3], ![-8, 0, 7, 4, -5], ![8, -2, -4, 3, 5], ![-4, -2, -2, -2, 7]]]
  hmulB := by decide  
  f := ![![![57, 86, -6, 22, -65]], ![![39, 55, -4, 14, -42]], ![![11, 16, -1, 4, -12]], ![![39, 58, -4, 15, -44]], ![![58, 86, -6, 22, -65]]]
  g := ![![![-1, 0, 0, 0, 1], ![-1, -1, 0, -2, 3], ![1, 0, 7, 4, -5], ![-5, -2, -4, 3, 5], ![-4, -2, -2, -2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2

def I83N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![465, 149, -65, 36, -259]] i)))

def SI83N3: IdealEqSpanCertificate' Table ![![465, 149, -65, 36, -259]] 
 ![![83, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![465, 149, -65, 36, -259], ![964, 328, -125, 78, -525], ![1944, 683, -234, 160, -1029], ![-264, -76, 42, -19, 154], ![1248, 446, -146, 104, -655]]]
  hmulB := by decide  
  f := ![![![119, -55, -135, -26, 203]], ![![74, -38, -97, -28, 147]], ![![55, -18, -29, 16, 42]], ![![75, -25, -63, 7, 91]], ![![98, -48, -124, -32, 187]]]
  g := ![![![128, 149, -65, 36, -259], ![237, 328, -125, 78, -525], ![430, 683, -234, 160, -1029], ![-87, -76, 42, -19, 154], ![264, 446, -146, 104, -655]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N3 : Nat.card (O ⧸ I83N3) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N3)

lemma isPrimeI83N3 : Ideal.IsPrime I83N3 := prime_ideal_of_norm_prime hp83.out _ NI83N3

def I83N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19807, -22841, -661, -6270, 10004]] i)))

def SI83N4: IdealEqSpanCertificate' Table ![![19807, -22841, -661, -6270, 10004]] 
 ![![83, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![19807, -22841, -661, -6270, 10004], ![-27476, 31686, 917, 8698, -13878], ![38116, -43955, -1272, -12066, 19252], ![-25408, 29300, 848, 8043, -12833], ![6476, -7468, -216, -2050, 3271]]]
  hmulB := by decide  
  f := ![![![69, 77, 3, -26, -4]], ![![64, 72, 5, -22, -6]], ![![34, 31, 0, -6, 4]], ![![43, 59, -3, -33, 7]], ![![2, 10, 2, -6, 1]]]
  g := ![![![25129, -22841, -661, -6270, 10004], ![-34860, 31686, 917, 8698, -13878], ![48358, -43955, -1272, -12066, 19252], ![-32235, 29300, 848, 8043, -12833], ![8216, -7468, -216, -2050, 3271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N4 : Nat.card (O ⧸ I83N4) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N4)

lemma isPrimeI83N4 : Ideal.IsPrime I83N4 := prime_ideal_of_norm_prime hp83.out _ NI83N4
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![63, 24, -6, 6, -32]] ![![-11, 6, 20, 8, -30]]
  ![![-237, 14, -34, -230, 82]] where
 M := ![![![-237, 14, -34, -230, 82]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-237, 14, -34, -230, 82]] ![![-1, 0, 0, 0, 1]]
  ![![-1715, 282, 518, -1018, -601]] where
 M := ![![![-1715, 282, 518, -1018, -601]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N2 : IdealMulLeCertificate' Table 
  ![![-1715, 282, 518, -1018, -601]] ![![465, 149, -65, 36, -259]]
  ![![69, 77, 3, -26, -4]] where
 M := ![![![69, 77, 3, -26, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N3 : IdealMulLeCertificate' Table 
  ![![69, 77, 3, -26, -4]] ![![19807, -22841, -661, -6270, 10004]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2, I83N3, I83N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
    exact isPrimeI83N3
    exact isPrimeI83N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1 ⊙ MulI83N2 ⊙ MulI83N3)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [13, 75, 31, 13, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 23, 84, 17, 22], [45, 86, 56, 62, 32], [12, 24, 42, 66, 87], [27, 44, 85, 33, 37], [0, 1]]
 g := ![![[1, 20, 3, 23, 11], [49, 21, 33, 72], [56, 35, 28, 69], [0, 58, 86, 65, 57], [1], []], ![[18, 69, 59, 38, 59, 37, 37, 2], [74, 80, 15, 40], [49, 77, 28, 16], [51, 68, 9, 4, 3, 84, 57, 20], [41, 81, 74, 7, 15, 85, 61, 20], [18, 69, 46, 39]], ![[74, 70, 65, 64, 54, 58, 10, 87], [19, 44, 7, 25], [5, 58, 55, 18], [79, 43, 49, 33, 14, 86, 10, 78], [24, 53, 69, 46, 76, 44, 30, 36], [42, 17, 43, 45]], ![[59, 53, 28, 63, 50, 6, 60, 57], [63, 25, 62, 79], [3, 18, 26, 81], [1, 70, 58, 32, 0, 42], [78, 3, 69, 36, 59, 46, 61, 18], [19, 38, 20, 4]], ![[21, 86, 21, 85, 25, 25, 58, 23], [76, 83, 4, 68], [75, 0, 66, 5], [58, 17, 2, 49, 25, 38, 0, 24], [66, 84, 80, 81, 88, 85, 3, 74], [45, 74, 50, 34]]]
 h' := ![![[76, 23, 84, 17, 22], [64, 31, 26, 60, 10], [73, 62, 12, 73, 28], [0, 38, 42, 8, 46], [76, 14, 58, 76, 71], [0, 0, 1], [0, 1]], ![[45, 86, 56, 62, 32], [74, 63, 85, 3, 9], [18, 34, 33, 84, 60], [78, 61, 38, 5, 85], [78, 39, 82, 2, 3], [24, 3, 24, 29, 3], [76, 23, 84, 17, 22]], ![[12, 24, 42, 66, 87], [41, 25, 48, 79, 53], [33, 63, 40, 70, 84], [86, 9, 12, 85, 75], [88, 1, 14, 82, 50], [55, 8, 44, 5, 48], [45, 86, 56, 62, 32]], ![[27, 44, 85, 33, 37], [80, 70, 84, 76, 4], [86, 7, 8, 55, 41], [6, 24, 64, 56, 80], [3, 79, 42, 54], [75, 81, 21, 0, 13], [12, 24, 42, 66, 87]], ![[0, 1], [38, 78, 24, 49, 13], [15, 12, 85, 74, 54], [10, 46, 22, 24, 70], [5, 45, 71, 53, 54], [55, 86, 88, 55, 25], [27, 44, 85, 33, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 68, 60, 81], [], [], []]
 b := ![[], [45, 44, 74, 69, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [13, 75, 31, 13, 18, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54498675499437, -6604708858922, -6254347484004, 41067141866344, 3226395430183]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![612344668533, -74210211898, -70273567236, 461428560296, 36251634047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [7, 73, 73, 83, 94, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 45, 21, 36, 69], [53, 24, 86, 92, 76], [17, 81, 59, 33, 84], [69, 43, 28, 33, 62], [0, 1]]
 g := ![![[61, 18, 39, 3, 94], [27, 76, 25, 53], [33, 73, 84, 85], [85, 74, 64, 44], [3, 1], []], ![[26, 10, 57, 91, 14, 65, 34, 51], [36, 80, 83, 96], [38, 64, 73, 44], [44, 71, 20, 43], [83, 59, 38, 94], [88, 27, 81, 3, 52, 48, 95, 67]], ![[74, 95, 89, 1, 15, 90, 37, 71], [70, 48, 63, 6], [62, 68, 88, 50], [78, 56, 49, 86], [88, 20, 13, 6], [92, 49, 80, 57, 27, 23, 37, 51]], ![[13, 5, 93, 29, 90, 67, 20, 28], [73, 32, 71, 81], [0, 84, 11, 44], [44, 78, 27, 81], [74, 6, 93, 33], [25, 85, 38, 87, 29, 5, 52, 34]], ![[0, 83, 65, 71, 29, 70], [82, 11, 19, 12], [29, 10, 78, 33], [75, 58, 3, 1], [92, 16, 1, 1], [7, 88, 45, 62, 74, 53, 22, 96]]]
 h' := ![![[58, 45, 21, 36, 69], [29, 56, 24, 45, 26], [11, 59, 3, 43, 21], [40, 53, 69, 31, 52], [76, 65, 96, 66, 23], [0, 0, 0, 1], [0, 1]], ![[53, 24, 86, 92, 76], [38, 24, 11, 42, 8], [22, 73, 87, 24, 22], [26, 13, 19, 54, 74], [25, 24, 16, 89, 25], [11, 66, 92, 42, 71], [58, 45, 21, 36, 69]], ![[17, 81, 59, 33, 84], [68, 43, 95, 89, 34], [48, 40, 16, 40, 43], [71, 56, 41, 24, 27], [61, 9, 93, 27, 59], [17, 25, 62, 71, 43], [53, 24, 86, 92, 76]], ![[69, 43, 28, 33, 62], [17, 18, 26, 1, 29], [72, 69, 11, 85, 88], [84, 68, 58, 29, 23], [95, 62, 55, 12, 88], [82, 4, 41, 81, 79], [17, 81, 59, 33, 84]], ![[0, 1], [0, 53, 38, 17], [34, 50, 77, 2, 20], [25, 4, 7, 56, 18], [68, 34, 31, 0, 96], [18, 2, 96, 96, 1], [69, 43, 28, 33, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 54, 3, 44], [], [], []]
 b := ![[], [2, 75, 29, 86, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [7, 73, 73, 83, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28335407491, 3826547374, 27917547884, 47885413238, -46866600995]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![292117603, 39448942, 287809772, 493664054, -483160835]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-325, 371, 11, 102, -162]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-325, 371, 11, 102, -162]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![92, 59, 1, 0, 0], ![11, 83, 0, 1, 0], ![37, 44, 0, 0, 1]] where
  M :=![![![-325, 371, 11, 102, -162], ![444, -518, -15, -142, 228], ![-628, 713, 20, 194, -310], ![416, -476, -12, -129, 205], ![-108, 120, 4, 34, -53]]]
  hmulB := by decide  
  f := ![![![23, -1, -11, -2, -18]], ![![76, 16, -15, 2, -68]], ![![68, 9, -19, 0, -58]], ![![65, 13, -14, 1, -57]], ![![43, 7, -11, 0, -37]]]
  g := ![![![35, -16, 11, 102, -162], ![-50, 21, -15, -142, 228], ![68, -29, 20, 194, -310], ![-46, 19, -12, -129, 205], ![11, -6, 4, 34, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [31, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 100], [0, 1]]
 g := ![![[69, 88], [20], [61, 100], [14], [100], [83, 1]], ![[0, 13], [20], [79, 1], [14], [100], [65, 100]]]
 h' := ![![[83, 100], [63, 54], [28, 11], [13, 91], [12, 69], [53, 91], [0, 1]], ![[0, 1], [0, 47], [32, 90], [92, 10], [83, 32], [31, 10], [83, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [9, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [31, 18, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-133102, -8180, -58305, -152902, 118302]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![25106, 108093, -58305, -152902, 118302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 4, 24, 48, -43]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![35, 4, 24, 48, -43]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![35, 83, 1, 0, 0], ![39, 38, 0, 1, 0], ![74, 91, 0, 0, 1]] where
  M :=![![![35, 4, 24, 48, -43], ![76, -37, -140, -58, 207], ![-712, 52, -85, -684, 215], ![464, 126, 732, 1019, -1195], ![348, -10, 86, 366, -177]]]
  hmulB := by decide  
  f := ![![![8427, -9754, -274, -2678, 4293]], ![![-11816, 13509, 410, 3708, -5867]], ![![-6631, 7535, 237, 2068, -3251]], ![![-1299, 1440, 52, 395, -604]], ![![-4446, 4993, 168, 1370, -2126]]]
  g := ![![![5, 1, 24, 48, -43], ![-80, -50, -140, -58, 207], ![129, 134, -85, -684, 215], ![233, 93, 732, 1019, -1195], ![-38, -49, 86, 366, -177]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [5, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 100], [0, 1]]
 g := ![![[25, 81], [24], [75, 9], [70], [13], [77, 1]], ![[0, 20], [24], [61, 92], [70], [13], [53, 100]]]
 h' := ![![[77, 100], [14, 9], [29, 78], [2, 98], [94, 75], [19, 66], [0, 1]], ![[0, 1], [0, 92], [76, 23], [74, 3], [11, 26], [51, 35], [77, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [53, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [5, 24, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38176, -1109, -13794, -42271, 28506]
  a := ![-23, -17, -32, -35, 81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-161, 1545, -13794, -42271, 28506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 23, -7, 6, -31]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![37, 23, -7, 6, -31]] 
 ![![101, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![37, 23, -7, 6, -31], ![112, 18, -15, 4, -51], ![196, 89, -28, 22, -125], ![-12, -18, 4, -5, 20], ![136, 50, -18, 12, -77]]]
  hmulB := by decide  
  f := ![![![-59, 17, 57, 4, -79]], ![![-32, 10, 35, 6, -49]], ![![-20, 3, 8, -8, -9]], ![![-35, 9, 27, -5, -37]], ![![-7, 3, 11, 4, -16]]]
  g := ![![![-10, 23, -7, 6, -31], ![-1, 18, -15, 4, -51], ![-37, 89, -28, 22, -125], ![9, -18, 4, -5, 20], ![-19, 50, -18, 12, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-325, 371, 11, 102, -162]] ![![35, 4, 24, 48, -43]]
  ![![-59, 17, 57, 4, -79]] where
 M := ![![![-59, 17, 57, 4, -79]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-59, 17, 57, 4, -79]] ![![37, 23, -7, 6, -31]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-789, 910, 26, 250, -398]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-789, 910, 26, 250, -398]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![75, 42, 1, 0, 0], ![102, 72, 0, 1, 0], ![65, 55, 0, 0, 1]] where
  M :=![![![-789, 910, 26, 250, -398], ![1092, -1263, -38, -350, 556], ![-1524, 1754, 61, 486, -782], ![1028, -1170, -38, -311, 516], ![-256, 296, 4, 80, -123]]]
  hmulB := by decide  
  f := ![![![1405, 506, -162, 118, -734]], ![![2700, 1007, -290, 230, -1376]], ![![2173, 798, -241, 184, -1120]], ![![3270, 1202, -362, 277, -1684]], ![![2359, 869, -260, 200, -1213]]]
  g := ![![![-23, 36, 26, 250, -398], ![34, -49, -38, -350, 556], ![-47, 70, 61, 486, -782], ![20, -54, -38, -311, 516], ![-7, 11, 4, 80, -123]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [74, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 102], [0, 1]]
 g := ![![[28, 52], [31, 8], [60, 97], [41], [59], [91, 1]], ![[22, 51], [38, 95], [29, 6], [41], [59], [79, 102]]]
 h' := ![![[91, 102], [75, 84], [92, 27], [32, 32], [39, 12], [64, 70], [0, 1]], ![[0, 1], [97, 19], [77, 76], [60, 71], [101, 91], [48, 33], [91, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [57, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [74, 12, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236, 489, 2963, 2693, -3942]
  a := ![2, 5, 9, 15, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2339, -981, 2963, 2693, -3942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 4, 2, 2, -2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![5, 4, 2, 2, -2]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![77, 19, 1, 0, 0], ![85, 100, 0, 1, 0], ![5, 14, 0, 0, 1]] where
  M :=![![![5, 4, 2, 2, -2], ![4, 3, 0, 2, 8], ![-36, 0, -5, -26, 38], ![-8, 2, 26, 21, -38], ![-8, 0, 12, 12, 1]]]
  hmulB := by decide  
  f := ![![![419, -472, -14, -130, 206]], ![![-564, 665, 20, 182, -292]], ![![217, -239, -7, -66, 104]], ![![-207, 262, 8, 71, -116]], ![![-55, 66, 2, 18, -29]]]
  g := ![![![-3, -2, 2, 2, -2], ![-2, -3, 0, 2, 8], ![23, 21, -5, -26, 38], ![-35, -20, 26, 21, -38], ![-19, -14, 12, 12, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [81, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 102], [0, 1]]
 g := ![![[93, 14], [79, 13], [95, 91], [92], [41], [89, 1]], ![[0, 89], [0, 90], [57, 12], [92], [41], [75, 102]]]
 h' := ![![[89, 102], [90, 80], [30, 61], [25, 83], [79, 68], [1, 12], [0, 1]], ![[0, 1], [0, 23], [0, 42], [99, 20], [54, 35], [39, 91], [89, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [50, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [81, 14, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-974320, -74746, -490862, -1172170, 959392]
  a := ![127, 90, 156, 164, -441]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1278248, 1097448, -490862, -1172170, 959392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 34, -12, 8, -52]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![97, 34, -12, 8, -52]] 
 ![![103, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![97, 34, -12, 8, -52], ![192, 69, -22, 16, -100], ![368, 138, -39, 32, -188], ![-60, -20, 8, -5, 34], ![232, 88, -24, 20, -117]]]
  hmulB := by decide  
  f := ![![![-57, 74, 16, 40, -52]], ![![-22, 29, 6, 16, -20]], ![![-54, 66, 13, 32, -44]], ![![-43, 58, 16, 35, -46]], ![![-25, 34, 8, 20, -25]]]
  g := ![![![15, 34, -12, 8, -52], ![26, 69, -22, 16, -100], ![42, 138, -39, 32, -188], ![-11, -20, 8, -5, 34], ![25, 88, -24, 20, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-789, 910, 26, 250, -398]] ![![5, 4, 2, 2, -2]]
  ![![-57, 74, 16, 40, -52]] where
 M := ![![![-57, 74, 16, 40, -52]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-57, 74, 16, 40, -52]] ![![97, 34, -12, 8, -52]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB312I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB312I2 : PrimesBelowBoundCertificateInterval O 61 103 312 where
  m := 9
  g := ![1, 3, 1, 3, 5, 1, 1, 3, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB312I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1, I83N2, I83N3, I83N4]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1, I103N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1350125107]
    · exact ![5041, 5041, 71]
    · exact ![2073071593]
    · exact ![6241, 6241, 79]
    · exact ![83, 83, 83, 83, 83]
    · exact ![5584059449]
    · exact ![8587340257]
    · exact ![10201, 10201, 101]
    · exact ![10609, 10609, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
      exact NI83N3
      exact NI83N4
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I71N2, I79N2, I83N0, I83N1, I83N2, I83N3, I83N4, I101N2, I103N2]
  Il := ![[], [I71N2], [], [I79N2], [I83N0, I83N1, I83N2, I83N3, I83N4], [], [], [I101N2], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
