
import IdealArithmetic.Examples.NF5_1_3515625_1.RI5_1_3515625_1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [59, 36, 29, 44, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 41, 6, 11, 31], [25, 45, 58, 49], [53, 17, 43, 21, 15], [25, 30, 27, 53, 21], [0, 1]]
 g := ![![[1, 19, 62, 5, 19], [62, 23, 46, 53, 21], [48, 41, 61, 62], [12, 16, 44, 1], [], []], ![[10, 44, 19, 37, 43, 18, 18, 58], [1, 38, 4, 7, 0, 9, 37, 34], [63, 46, 19, 9], [39, 20, 14, 59], [41, 8, 8, 23], [44, 49, 19, 23]], ![[19, 7, 38, 50, 26, 1, 23], [7, 31, 61, 47, 24, 63, 62], [56, 64, 17, 59], [66, 17, 1, 59], [64, 5, 6, 10], [41, 56]], ![[9, 4, 35, 51, 41, 28, 35, 21], [21, 58, 22, 1, 47, 40, 55, 56], [40, 25, 23, 37], [47, 44, 21, 54], [37, 2, 30, 14], [6, 20, 11, 24]], ![[17, 11, 59, 31, 3, 31, 14, 14], [44, 33, 17, 53, 57, 62, 62, 35], [18, 4], [60, 26, 22, 33], [46, 27, 19, 33], [35, 1, 56, 39]]]
 h' := ![![[8, 41, 6, 11, 31], [27, 55, 2, 9, 32], [19, 63, 44, 0, 50], [29, 31, 31, 45, 53], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[25, 45, 58, 49], [13, 61, 44, 3, 34], [3, 55, 42, 16, 43], [54, 15, 49, 60, 3], [55, 62, 41, 23, 40], [14, 0, 28, 27, 36], [8, 41, 6, 11, 31]], ![[53, 17, 43, 21, 15], [51, 45, 51, 33, 53], [43, 32, 1, 30, 2], [59, 38, 50, 49, 40], [0, 25, 20, 45, 27], [15, 16, 45, 21, 12], [25, 45, 58, 49]], ![[25, 30, 27, 53, 21], [18, 18, 62, 64, 51], [7, 16, 37, 6, 54], [42, 66, 10, 45, 38], [1, 33, 46, 37, 56], [43, 4, 21, 27, 9], [53, 17, 43, 21, 15]], ![[0, 1], [4, 22, 42, 25, 31], [29, 35, 10, 15, 52], [32, 51, 61, 2], [50, 14, 27, 29, 10], [34, 47, 39, 59, 10], [25, 30, 27, 53, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 37, 39, 45], [], [], []]
 b := ![[], [21, 60, 60, 13, 18], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [59, 36, 29, 44, 23, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75145514883, -529362042, -72869780019, -44376274753, 282002499845]
  a := ![-20, 2, 9, 9, -55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1121574849, -7900926, -1087608657, -662332459, 4208992535]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-275, 30, -108, 40, -311]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-275, 30, -108, 40, -311]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![48, 31, 1, 0, 0], ![3, 10, 0, 1, 0], ![33, 58, 0, 0, 1]] where
  M :=![![![-275, 30, -108, 40, -311], ![-302, -4, -130, 43, -364], ![-384, 19, -176, 62, -510], ![-524, 64, -229, 86, -676], ![-109, 7, -53, 19, -156]]]
  hmulB := by decide  
  f := ![![![38, -13, -9, -27, 101]], ![![-14, -36, 95, -2, -190]], ![![14, -22, 35, -15, -26]], ![![10, -4, -1, -7, 23]], ![![9, -36, 72, -16, -100]]]
  g := ![![![212, 296, -108, 40, -311], ![251, 348, -130, 43, -364], ![348, 485, -176, 62, -510], ![458, 641, -229, 86, -676], ![106, 148, -53, 19, -156]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [56, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 70], [0, 1]]
 g := ![![[49, 49], [34, 4], [6, 9], [37], [57], [1]], ![[67, 22], [63, 67], [18, 62], [37], [57], [1]]]
 h' := ![![[25, 70], [13, 64], [19, 2], [70, 3], [15, 45], [15, 25], [0, 1]], ![[0, 1], [51, 7], [69, 69], [3, 68], [4, 26], [1, 46], [25, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [70, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [56, 46, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![827403, -345532, 3221, -601092, 1764116]
  a := ![-239, -1, 122, 120, -658]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-785067, -1362721, 3221, -601092, 1764116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, -6, -4, 1, -17]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![24, -6, -4, 1, -17]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![55, 30, 1, 0, 0], ![54, 7, 0, 1, 0], ![64, 48, 0, 0, 1]] where
  M :=![![![24, -6, -4, 1, -17], ![-26, 40, -10, 9, -46], ![-20, 11, 4, 0, 14], ![28, -34, 11, -10, 56], ![-7, -1, 4, -2, 17]]]
  hmulB := by decide  
  f := ![![![5, 1, 5, 2, -3]], ![![10, 6, -7, 0, 32]], ![![9, 3, 1, 1, 13]], ![![4, 1, 5, 2, -4]], ![![11, 5, 0, 2, 18]]]
  g := ![![![18, 13, -4, 1, -17], ![42, 35, -10, 9, -46], ![-16, -11, 4, 0, 14], ![-51, -42, 11, -10, 56], ![-17, -13, 4, -2, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [43, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 70], [0, 1]]
 g := ![![[31, 38], [33, 29], [26, 25], [58], [43], [1]], ![[0, 33], [0, 42], [0, 46], [58], [43], [1]]]
 h' := ![![[16, 70], [1, 31], [18, 61], [62, 5], [0, 22], [28, 16], [0, 1]], ![[0, 1], [0, 40], [0, 10], [0, 66], [68, 49], [0, 55], [16, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [34, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [43, 55, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3408, -1471, -113, -2587, 7606]
  a := ![-17, 1, 9, 8, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4753, -4860, -113, -2587, 7606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -21, 6, -5, 26]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![15, -21, 6, -5, 26]] 
 ![![71, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![15, -21, 6, -5, 26], ![12, -6, -1, 0, -6], ![-12, 18, -6, 5, -24], ![-8, 7, -2, -2, 14], ![-8, 11, -3, 2, -11]]]
  hmulB := by decide  
  f := ![![![693, -50, 303, -107, 868]], ![![110, -8, 48, -17, 138]], ![![426, -31, 186, -66, 534]], ![![78, -6, 35, -12, 96]], ![![512, -37, 224, -79, 641]]]
  g := ![![![-19, -21, 6, -5, 26], ![6, -6, -1, 0, -6], ![18, 18, -6, 5, -24], ![-10, 7, -2, -2, 14], ![8, 11, -3, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-275, 30, -108, 40, -311]] ![![24, -6, -4, 1, -17]]
  ![![-1923, 613, -436, 217, -1264]] where
 M := ![![![-1923, 613, -436, 217, -1264]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-1923, 613, -436, 217, -1264]] ![![15, -21, 6, -5, 26]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-7881, 16472, -6177, 4473, -26270]]]
 hmul := by decide  
 g := ![![![![-111, 232, -87, 63, -370]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [45, 34, 62, 29, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 6, 54, 50, 22], [45, 32, 2, 35, 9], [15, 24, 30, 1, 15], [52, 10, 60, 60, 27], [0, 1]]
 g := ![![[65, 22, 48, 9, 54], [16, 22, 50, 12], [52, 27, 5, 9], [42, 40, 32, 34, 1], [], []], ![[2, 69, 34, 11, 4, 16, 43, 7], [8, 24, 60, 57], [66, 17, 11, 71], [62, 54, 7, 11, 72, 40, 7, 33], [15, 26, 56, 67], [14, 45, 41, 46]], ![[21, 51, 69, 38, 65, 43, 55, 46], [12, 63, 48, 3], [72, 44, 22, 16], [31, 61, 5, 6, 24, 61, 55, 36], [54, 8, 21, 64], [49, 15, 26, 8]], ![[46, 1, 12, 17, 44, 1, 2, 26], [52, 37, 27, 54], [60, 45, 45, 27], [49, 71, 23, 51, 11, 25, 32, 20], [9, 4, 52, 3], [56, 69, 15, 6]], ![[72, 51, 52, 10, 65, 3, 71, 61], [66, 68, 49, 12], [55, 63, 6, 38], [14, 71, 54, 44, 38, 20, 53, 36], [65, 8, 8, 35], [37, 22, 67, 72]]]
 h' := ![![[68, 6, 54, 50, 22], [33, 44, 67, 60, 45], [60, 46, 18, 6, 31], [8, 57, 71, 35, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[45, 32, 2, 35, 9], [51, 9, 65, 34, 17], [22, 16, 52, 42, 35], [27, 6, 27, 55, 12], [58, 32, 20, 39, 29], [52, 67, 71, 58, 40], [68, 6, 54, 50, 22]], ![[15, 24, 30, 1, 15], [17, 52, 6, 4, 17], [22, 50, 58, 30, 21], [14, 40, 68, 26, 4], [40, 61, 38, 10, 71], [39, 28, 63, 48, 65], [45, 32, 2, 35, 9]], ![[52, 10, 60, 60, 27], [66, 33, 6, 44, 49], [56, 14, 42, 42, 28], [37, 64, 9, 33, 10], [35, 41, 25, 18, 59], [41, 18, 20, 44, 21], [15, 24, 30, 1, 15]], ![[0, 1], [60, 8, 2, 4, 18], [16, 20, 49, 26, 31], [70, 52, 44, 70, 44], [65, 12, 63, 6, 59], [17, 33, 64, 69, 20], [52, 10, 60, 60, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 35, 37, 21], [], [], []]
 b := ![[], [11, 35, 43, 7, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [45, 34, 62, 29, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563082450989071, 152795559778175, 195107322756799, 382388718778884, -1528387588568188]
  a := ![103, -3, -50, -52, 283]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7713458232727, 2093089859975, 2672703051463, 5238201627108, -20936816281756]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [53, 74, 1, 5, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 68, 28, 32, 23], [20, 35, 26, 66, 73], [26, 24, 44, 41, 59], [71, 30, 60, 19, 3], [0, 1]]
 g := ![![[65, 41, 29, 44, 18], [41, 31, 43, 21, 51], [65, 16, 33, 65, 45], [18, 47, 16, 69, 1], [], []], ![[1, 65, 50, 48, 46, 31, 76, 65], [9, 72, 35, 13, 17, 44, 49, 13], [75, 56, 25, 74, 23, 46, 54, 19], [8, 27, 26, 72, 14, 17, 65, 31], [33, 0, 70, 67], [37, 6, 53, 55]], ![[61, 61, 55, 32, 71, 54, 74, 50], [59, 64, 6, 11, 46, 34, 76, 31], [12, 26, 11, 75, 19, 75, 23, 76], [56, 38, 58, 9, 66, 43, 38, 20], [72, 13, 73, 52], [19, 58, 33, 36]], ![[23, 2, 32, 73, 42, 66, 76, 48], [66, 70, 73, 38, 20, 59, 23, 47], [46, 48, 31, 26, 47, 37, 37, 28], [7, 52, 52, 56, 59, 52, 36, 48], [32, 42, 44, 20], [27, 48, 48, 5]], ![[72, 8, 54, 45, 59, 40, 6, 71], [21, 0, 55, 55, 73, 21, 26, 57], [2, 16, 73, 34, 19, 3, 69, 70], [33, 36, 77, 74, 42, 12, 51, 57], [45, 23, 22, 64], [25, 41, 24, 9]]]
 h' := ![![[31, 68, 28, 32, 23], [39, 76, 31, 69, 52], [31, 66, 60, 14, 50], [73, 48, 1, 78, 19], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[20, 35, 26, 66, 73], [22, 24, 31, 10, 39], [13, 67, 72, 10, 2], [68, 45, 2, 51, 27], [7, 0, 1, 39, 58], [27, 54, 68, 28, 64], [31, 68, 28, 32, 23]], ![[26, 24, 44, 41, 59], [78, 12, 45, 22, 52], [38, 15, 50, 76, 18], [57, 4, 42, 30, 44], [48, 37, 4, 57, 55], [25, 1, 76, 36, 62], [20, 35, 26, 66, 73]], ![[71, 30, 60, 19, 3], [1, 44, 47, 14, 60], [22, 63, 25, 7, 72], [21, 5, 62, 14, 21], [3, 9, 24, 68, 60], [35, 24, 59, 7, 40], [26, 24, 44, 41, 59]], ![[0, 1], [47, 2, 4, 43, 34], [31, 26, 30, 51, 16], [17, 56, 51, 64, 47], [73, 33, 50, 73, 63], [3, 0, 33, 8, 71], [71, 30, 60, 19, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 62, 19, 46], [], [], []]
 b := ![[], [65, 43, 59, 6, 77], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [53, 74, 1, 5, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7993142997120, -2826558411758, -1219116581972, -5648462036550, 19112469392964]
  a := ![-43, 5, 22, 23, -118]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![101179025280, -35779220402, -15431855468, -71499519450, 241929992316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 2, 5, 4, -23]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-8, 2, 5, 4, -23]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![64, 12, 1, 0, 0], ![62, 3, 0, 1, 0], ![7, 68, 0, 0, 1]] where
  M :=![![![-8, 2, 5, 4, -23], ![-14, 11, -14, 12, -4], ![88, -22, -37, -58, 248], ![32, -102, 210, -53, -284], ![-21, -6, 34, 11, -103]]]
  hmulB := by decide  
  f := ![![![-293, -24, -121, 37, -327]], ![![-358, -3, -172, 58, -494]], ![![-284, -18, -121, 38, -332]], ![![-240, -17, -100, 31, -272]], ![![-320, -4, -152, 51, -435]]]
  g := ![![![-5, 18, 5, 4, -23], ![2, 5, -14, 12, -4], ![52, -196, -37, -58, 248], ![-98, 203, 210, -53, -284], ![-26, 79, 34, 11, -103]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [3, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 82], [0, 1]]
 g := ![![[62, 28], [8, 17], [26], [41], [5, 68], [1]], ![[0, 55], [0, 66], [26], [41], [56, 15], [1]]]
 h' := ![![[63, 82], [59, 32], [34, 10], [19, 62], [68, 37], [80, 63], [0, 1]], ![[0, 1], [0, 51], [0, 73], [24, 21], [75, 46], [65, 20], [63, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [53, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [3, 20, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5165, -2108, 10284, 2172, -28072]
  a := ![16, -2, -6, -18, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7247, 21408, 10284, 2172, -28072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 12, 2, 1, 1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![0, 12, 2, 1, 1]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![32, 6, 1, 0, 0], ![57, 79, 0, 1, 0], ![45, 4, 0, 0, 1]] where
  M :=![![![0, 12, 2, 1, 1], ![10, -2, 8, -3, 26], ![28, -13, 10, -6, 38], ![28, -4, 11, -4, 20], ![11, -7, 4, -2, 11]]]
  hmulB := by decide  
  f := ![![![11, -11, 5, -4, 15]], ![![-2, 0, 5, 6, -28]], ![![4, -4, 2, -1, 4]], ![![7, -8, 8, 2, -13]], ![![6, -6, 3, -2, 7]]]
  g := ![![![-2, -1, 2, 1, 1], ![-15, 1, 8, -3, 26], ![-20, 3, 10, -6, 38], ![-12, 2, 11, -4, 20], ![-6, 1, 4, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [2, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 82], [0, 1]]
 g := ![![[8, 38], [14, 38], [17], [38], [35, 7], [1]], ![[64, 45], [70, 45], [17], [38], [6, 76], [1]]]
 h' := ![![[67, 82], [55, 72], [66, 11], [10, 10], [13, 11], [81, 67], [0, 1]], ![[0, 1], [65, 11], [56, 72], [16, 73], [3, 72], [5, 16], [67, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [16, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [2, 16, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1950, 361, 2067, 1629, -7627]
  a := ![3, 4, 6, 6, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2196, -1328, 2067, 1629, -7627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, -5, 7, -3, 21]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![20, -5, 7, -3, 21]] 
 ![![83, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![20, -5, 7, -3, 21], ![18, 2, 7, -2, 18], ![20, 2, 10, -3, 28], ![32, -5, 14, -6, 46], ![5, 1, 3, -1, 9]]]
  hmulB := by decide  
  f := ![![![-19, 20, -2, 14, -61]], ![![-15, 16, -2, 11, -47]], ![![0, 1, 0, 0, -2]], ![![-17, 14, 3, 12, -59]], ![![-15, 15, -1, 11, -48]]]
  g := ![![![-10, -5, 7, -3, 21], ![-14, 2, 7, -2, 18], ![-21, 2, 10, -3, 28], ![-27, -5, 14, -6, 46], ![-7, 1, 3, -1, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-8, 2, 5, 4, -23]] ![![0, 12, 2, 1, 1]]
  ![![19, -20, 2, -14, 61]] where
 M := ![![![19, -20, 2, -14, 61]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![19, -20, 2, -14, 61]] ![![20, -5, 7, -3, 21]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38, -7, -7, 1, -11]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-38, -7, -7, 1, -11]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![67, 78, 1, 0, 0], ![25, 35, 0, 1, 0], ![44, 27, 0, 0, 1]] where
  M :=![![![-38, -7, -7, 1, -11], ![-14, -28, -11, 0, -22], ![-44, 8, -28, 11, -88], ![-88, 33, -36, 16, -110], ![-15, 9, -11, 5, -37]]]
  hmulB := by decide  
  f := ![![![-17, 6, 2, 10, -33]], ![![14, 6, -34, -5, 88]], ![![1, 9, -28, 2, 55]], ![![-3, 4, -9, 3, 11]], ![![-5, 5, -9, 4, 8]]]
  g := ![![![10, 9, -7, 1, -11], ![19, 16, -11, 0, -22], ![61, 47, -28, 11, -88], ![76, 59, -36, 16, -110], ![25, 19, -11, 5, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [77, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 88], [0, 1]]
 g := ![![[56, 10], [80], [9], [88, 80], [10, 87], [1]], ![[12, 79], [80], [9], [3, 9], [1, 2], [1]]]
 h' := ![![[49, 88], [28, 59], [74, 13], [77, 3], [31, 76], [12, 49], [0, 1]], ![[0, 1], [71, 30], [88, 76], [46, 86], [17, 13], [10, 40], [49, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [3, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [77, 40, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![441, -91, -324, -305, 1417]
  a := ![-7, -1, 4, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-366, -27, -324, -305, 1417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-136, 11, -59, 21, -171]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-136, 11, -59, 21, -171]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![56, 50, 1, 0, 0], ![48, 48, 0, 1, 0], ![67, 12, 0, 0, 1]] where
  M :=![![![-136, 11, -59, 21, -171], ![-174, 14, -73, 28, -222], ![-220, 20, -98, 37, -272], ![-248, 15, -128, 26, -274], ![-59, 3, -27, 7, -71]]]
  hmulB := by decide  
  f := ![![![191, -192, 34, -36, 149]], ![![10, 78, -48, 29, -196]], ![![124, -75, -6, -6, -18]], ![![108, -62, -7, -4, -24]], ![![144, -133, 19, -23, 85]]]
  g := ![![![153, 45, -59, 21, -171], ![196, 56, -73, 28, -222], ![244, 72, -98, 37, -272], ![270, 95, -128, 26, -274], ![66, 21, -27, 7, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [15, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 88], [0, 1]]
 g := ![![[12, 25], [9], [69], [15, 72], [52, 4], [1]], ![[51, 64], [9], [69], [49, 17], [44, 85], [1]]]
 h' := ![![[87, 88], [65, 84], [17, 3], [42, 43], [21, 61], [74, 87], [0, 1]], ![[0, 1], [75, 5], [11, 86], [45, 46], [77, 28], [78, 2], [87, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [35, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [15, 2, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-894, -10, 982, 603, -3612]
  a := ![9, 0, 4, -7, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1766, -390, 982, 603, -3612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![297, -32, 127, -47, 371]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![297, -32, 127, -47, 371]] 
 ![![89, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![297, -32, 127, -47, 371], ![366, -27, 156, -56, 450], ![452, -28, 197, -70, 568], ![576, -46, 252, -91, 732], ![129, -6, 57, -20, 164]]]
  hmulB := by decide  
  f := ![![![-32, 54, -77, 30, 57]], ![![-14, 29, -44, 14, 42]], ![![-32, 46, -60, 28, 29]], ![![-56, 46, -44, 45, -48]], ![![-29, 46, -65, 27, 44]]]
  g := ![![![-367, -32, 127, -47, 371], ![-454, -27, 156, -56, 450], ![-577, -28, 197, -70, 568], ![-736, -46, 252, -91, 732], ![-168, -6, 57, -20, 164]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-38, -7, -7, 1, -11]] ![![-136, 11, -59, 21, -171]]
  ![![8327, -674, 3608, -1304, 10463]] where
 M := ![![![8327, -674, 3608, -1304, 10463]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![8327, -674, 3608, -1304, 10463]] ![![297, -32, 127, -47, 371]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![4455874, -352084, 1930944, -696781, 5596765]]]
 hmul := by decide  
 g := ![![![![50066, -3956, 21696, -7829, 62885]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
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


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [72, 49, 9, 35, 74, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 84, 59, 13, 44], [54, 22, 71, 70, 92], [22, 33, 60, 70, 15], [25, 54, 4, 41, 43], [0, 1]]
 g := ![![[90, 40, 30, 50, 96], [50, 73, 2, 9], [77, 70, 8, 66], [50, 69, 15, 81], [23, 1], []], ![[12, 87, 91, 46, 44, 58, 50, 9], [8, 68, 85, 33], [68, 66], [5, 6, 0, 31], [87, 42, 9, 1], [96, 9, 31, 31, 29, 35, 64, 18]], ![[5, 18, 27, 15, 14, 1, 25, 87], [80, 15, 59, 33], [85, 75, 14, 54], [47, 10, 9, 79], [59, 68, 40, 18], [39, 83, 27, 43, 10, 40, 47, 69]], ![[71, 43, 13, 51, 74, 12, 65, 30], [62, 67, 29, 50], [23, 54, 29, 62], [8, 35, 47, 18], [88, 30, 2, 89], [12, 90, 3, 67, 39, 46, 36, 77]], ![[36, 46, 67, 85, 18, 67, 6, 73], [18, 94, 66, 91], [9, 70, 67, 44], [41, 47, 33, 31], [3, 21, 94, 81], [60, 23, 87, 32, 59, 22, 76, 64]]]
 h' := ![![[19, 84, 59, 13, 44], [83, 47, 63, 70, 22], [71, 2, 94, 18, 94], [38, 56, 92, 8, 39], [90, 62, 35, 59, 9], [0, 0, 0, 1], [0, 1]], ![[54, 22, 71, 70, 92], [18, 25, 9, 86, 80], [20, 14, 37, 19, 18], [39, 69, 36, 58], [37, 73, 72, 27, 82], [44, 66, 56, 90, 1], [19, 84, 59, 13, 44]], ![[22, 33, 60, 70, 15], [25, 82, 51, 65, 14], [16, 80, 95, 41, 79], [92, 54, 38, 1, 65], [9, 47, 20, 90, 46], [38, 75, 89, 81, 42], [54, 22, 71, 70, 92]], ![[25, 54, 4, 41, 43], [31, 55, 87, 64, 14], [79, 63, 59, 96, 27], [38, 3, 21, 20, 16], [41, 32, 39, 73, 42], [84, 11, 30, 80, 63], [22, 33, 60, 70, 15]], ![[0, 1], [35, 82, 81, 6, 64], [19, 35, 6, 20, 73], [52, 12, 7, 10, 74], [71, 77, 28, 42, 15], [53, 42, 19, 39, 88], [25, 54, 4, 41, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 61, 49, 42], [], [], []]
 b := ![[], [88, 15, 65, 10, 74], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [72, 49, 9, 35, 74, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1617249516128, 407804244008, 633576359947, 1087870226381, -4511708777043]
  a := ![31, -3, -16, -16, 85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16672675424, 4204167464, 6531715051, 11215156973, -46512461619]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 26, -7, 5, -23]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-21, 26, -7, 5, -23]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![57, 32, 1, 0, 0], ![95, 43, 0, 1, 0], ![13, 38, 0, 0, 1]] where
  M :=![![![-21, 26, -7, 5, -23], ![-6, -3, 6, -4, 18], ![4, -20, 13, 4, -16], ![0, 16, -36, 13, 24], ![15, -12, -3, -4, 28]]]
  hmulB := by decide  
  f := ![![![1148, -96, 497, -180, 1443]], ![![1446, -115, 624, -226, 1812]], ![![1124, -92, 486, -176, 1411]], ![![1718, -141, 743, -269, 2157]], ![![697, -56, 301, -109, 874]]]
  g := ![![![2, 9, -7, 5, -23], ![-2, -7, 6, -4, 18], ![-9, 0, 13, 4, -16], ![5, -3, -36, 13, 24], ![2, -8, -3, -4, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [38, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 100], [0, 1]]
 g := ![![[8, 16], [65], [56, 36], [85], [56], [100, 1]], ![[93, 85], [65], [20, 65], [85], [56], [99, 100]]]
 h' := ![![[100, 100], [3, 4], [94, 60], [26, 95], [23, 61], [38, 64], [0, 1]], ![[0, 1], [100, 97], [34, 41], [32, 6], [63, 40], [75, 37], [100, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [99, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [38, 1, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1314, 65, -1297, -684, 4874]
  a := ![12, 0, -5, -3, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![761, -1131, -1297, -684, 4874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 3, 1, 1, 1]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-8, 3, 1, 1, 1]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![27, 19, 1, 0, 0], ![93, 70, 0, 1, 0], ![74, 15, 0, 0, 1]] where
  M :=![![![-8, 3, 1, 1, 1], ![10, -10, -1, -4, 26], ![20, -12, 6, -11, 16], ![-56, 15, 32, 34, -178], ![-7, 3, 1, 7, -27]]]
  hmulB := by decide  
  f := ![![![-345, 24, -146, 52, -419]], ![![-422, 22, -184, 65, -532]], ![![-177, 11, -76, 27, -219]], ![![-617, 38, -265, 94, -763]], ![![-317, 21, -135, 48, -388]]]
  g := ![![![-2, -1, 1, 1, 1], ![-15, -1, -1, -4, 26], ![-3, 4, 6, -11, 16], ![90, -3, 32, 34, -178], ![13, -1, 1, 7, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [62, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 100], [0, 1]]
 g := ![![[52, 33], [64], [91, 6], [79], [4], [8, 1]], ![[13, 68], [64], [38, 95], [79], [4], [16, 100]]]
 h' := ![![[8, 100], [66, 29], [14, 8], [64, 39], [35, 68], [9, 2], [0, 1]], ![[0, 1], [96, 72], [78, 93], [73, 62], [74, 33], [25, 99], [8, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [79, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [62, 93, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39912, -8647, -19449, -25370, 112260]
  a := ![37, -1, -40, -15, 100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53295, 4484, -19449, -25370, 112260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 3, -1, -3]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![1, -2, 3, -1, -3]] 
 ![![101, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![1, -2, 3, -1, -3], ![-14, 5, 2, 10, -34], ![12, 10, -35, -4, 84], ![136, -68, 26, -103, 248], ![11, -10, 13, -10, 2]]]
  hmulB := by decide  
  f := ![![![-622, 340, -243, 128, -819]], ![![-314, 169, -122, 64, -410]], ![![-158, 82, -62, 32, -207]], ![![-394, 212, -155, 81, -521]], ![![-25, 12, -10, 5, -33]]]
  g := ![![![1, -2, 3, -1, -3], ![-8, 5, 2, 10, -34], ![3, 10, -35, -4, 84], ![83, -68, 26, -103, 248], ![8, -10, 13, -10, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-21, 26, -7, 5, -23]] ![![-8, 3, 1, 1, 1]]
  ![![169, -233, 48, -39, 274]] where
 M := ![![![169, -233, 48, -39, 274]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![169, -233, 48, -39, 274]] ![![1, -2, 3, -1, -3]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![1717, -1111, 909, -1414, 2323]]]
 hmul := by decide  
 g := ![![![![17, -11, 9, -14, 23]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [58, 11, 17, 95, 84, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 18, 80, 87, 10], [51, 29, 21, 44, 33], [60, 13, 4, 59, 49], [39, 42, 101, 16, 11], [0, 1]]
 g := ![![[36, 6, 24, 2, 15], [14, 9, 38, 97, 46], [7, 29, 85, 57, 34], [92, 26, 37, 98], [19, 1], []], ![[82, 39, 25, 70, 41, 10, 81, 53], [48, 16, 62, 71, 70, 8, 99, 47], [78, 16, 66, 92, 60, 92, 59, 39], [86, 51, 85, 8], [56, 37, 98, 76], [50, 18, 101, 37, 45, 68, 89, 73]], ![[54, 52, 101, 32, 96, 16, 42, 60], [58, 38, 51, 78, 96, 55], [24, 98, 30, 48, 19, 56, 36, 81], [8, 27, 39, 2], [86, 32, 53, 52], [28, 93, 57, 33, 17, 72, 79, 93]], ![[46, 18, 55, 36, 71, 34, 45, 16], [1, 66, 77, 1, 43, 44, 82, 9], [43, 40, 18, 66, 15, 85, 87, 33], [4, 54, 53, 38], [57, 97, 48, 23], [76, 39, 68, 40, 24, 100, 24, 23]], ![[62, 88, 64, 95, 80, 96, 46, 65], [17, 70, 28, 32, 84, 60, 54, 67], [27, 9, 79, 66, 75, 11, 21, 102], [25, 73, 19, 58], [34, 15, 21, 91], [8, 55, 99, 28, 0, 71, 94, 95]]]
 h' := ![![[75, 18, 80, 87, 10], [12, 81, 13, 5, 85], [6, 24, 99, 51, 56], [54, 84, 29, 61, 72], [31, 42, 78, 32, 60], [0, 0, 0, 1], [0, 1]], ![[51, 29, 21, 44, 33], [48, 89, 76, 35, 43], [56, 18, 6, 25, 85], [61, 47, 96, 64, 73], [65, 9, 33, 35, 27], [74, 57, 53, 84, 30], [75, 18, 80, 87, 10]], ![[60, 13, 4, 59, 49], [38, 39, 75, 87, 77], [32, 88, 67, 97], [6, 95, 52, 87, 58], [77, 4, 100, 61, 38], [11, 62, 52, 54, 19], [51, 29, 21, 44, 33]], ![[39, 42, 101, 16, 11], [95, 55, 19, 24, 73], [11, 73, 70, 77, 74], [4, 30, 0, 100, 53], [66, 4, 75, 81, 55], [30, 3, 78, 17, 34], [60, 13, 4, 59, 49]], ![[0, 1], [64, 45, 23, 55, 31], [88, 3, 67, 59, 94], [99, 53, 29, 100, 53], [101, 44, 23, 100, 26], [42, 84, 23, 50, 20], [39, 42, 101, 16, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 89, 0, 6], [], [], []]
 b := ![[], [35, 19, 31, 64, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [58, 11, 17, 95, 84, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8794799406, 808797097, 6767689057, 5443880424, -30071001101]
  a := ![7, 1, -9, -4, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85386402, 7852399, 65705719, 52853208, -291951467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB117I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB117I2 : PrimesBelowBoundCertificateInterval O 61 103 117 where
  m := 9
  g := ![1, 3, 1, 1, 3, 3, 1, 3, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB117I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
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
    · exact ![3077056399]
    · exact ![6889, 6889, 83]
    · exact ![7921, 7921, 89]
    · exact ![8587340257]
    · exact ![10201, 10201, 101]
    · exact ![11592740743]
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
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
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
  β := ![I71N2, I83N2, I89N2, I101N2]
  Il := ![[], [I71N2], [], [], [I83N2], [I89N2], [], [I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
