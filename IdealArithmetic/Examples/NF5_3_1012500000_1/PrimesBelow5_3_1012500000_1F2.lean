
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 5 2 6 [37, 48, 6, 64, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 57, 28, 12, 20], [56, 17, 55, 40, 5], [16, 33, 50, 12, 58], [0, 26, 1, 3, 51], [0, 1]]
 g := ![![[51, 39, 20, 46, 17], [4, 58, 10, 55, 37], [34, 59, 53, 15], [10, 39, 61, 1], [], []], ![[39, 31, 21, 4, 23, 0, 41, 20], [53, 5, 63, 62, 19, 27, 49, 52], [5, 0, 1, 17], [35, 3, 60, 16], [25, 56, 6, 21], [65, 48, 23, 65]], ![[40, 46, 10, 9, 3, 3, 47, 52], [48, 24, 33, 15, 56, 19, 23, 11], [3, 21, 16, 59], [39, 50, 37, 14], [54, 25, 15, 23], [16, 55, 49, 25]], ![[47, 2, 63, 55, 32, 5, 24, 48], [4, 23, 8, 21, 26, 25, 20, 18], [64, 46, 60, 35], [49, 6, 16, 64], [3, 2, 10, 15], [7, 14, 35, 14]], ![[0, 57, 50, 34, 21, 15, 43, 27], [20, 50, 48, 63, 23, 25, 6, 31], [10, 35, 31, 47], [22, 45, 57, 15], [58, 48, 51, 23], [4, 18, 43, 55]]]
 h' := ![![[56, 57, 28, 12, 20], [53, 24, 49, 14, 34], [34, 11, 64, 66, 29], [32, 20, 32, 47, 45], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[56, 17, 55, 40, 5], [63, 15, 27, 59, 1], [33, 3, 21, 27, 63], [34, 42, 66, 36, 34], [49, 44, 40, 53, 4], [61, 14, 26, 63, 17], [56, 57, 28, 12, 20]], ![[16, 33, 50, 12, 58], [20, 14, 59, 25, 59], [49, 4, 47, 44, 30], [19, 12, 3, 13, 40], [16, 12, 16, 3, 9], [65, 39, 24, 44, 36], [56, 17, 55, 40, 5]], ![[0, 26, 1, 3, 51], [2, 18, 53, 55, 34], [1, 7, 58, 57, 47], [15, 41, 46, 36, 54], [32, 44, 60, 25, 8], [64, 1, 10, 16, 45], [16, 33, 50, 12, 58]], ![[0, 1], [64, 63, 13, 48, 6], [12, 42, 11, 7, 32], [39, 19, 54, 2, 28], [60, 34, 18, 53, 45], [53, 13, 6, 11, 36], [0, 26, 1, 3, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 22, 64, 66], [], [], []]
 b := ![[], [41, 44, 54, 50, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 5
  hpos := by decide
  P := [37, 48, 6, 64, 6, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-177653211959, -446967785593, 155034205656, 559529380327, 43243681762]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2651540477, -6671160979, 2313943368, 8351184781, 645428086]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1765, 3009, -772, 485, -321]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1765, 3009, -772, 485, -321]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![54, 53, 65, 8, 1]] where
  M :=![![![1765, 3009, -772, 485, -321], ![-1926, -3050, 1492, -309, 485], ![2910, 5349, -205, 1149, -309], ![-1764, -2962, 906, -427, 346], ![-306, -111, 1312, 357, 302]]]
  hmulB := by decide  
  f := ![![![3647, 1945, -862, 157, -309]], ![![-1854, -988, 438, -81, 157]], ![![942, 501, -221, 45, -81]], ![![-552, -296, 130, -23, 48]], ![![2184, 1164, -515, 97, -186]]]
  g := ![![![269, 282, 283, 43, -321], ![-396, -405, -423, -59, 485], ![276, 306, 280, 51, -309], ![-288, -300, -304, -45, 346], ![-234, -227, -258, -29, 302]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [47, 7, 55, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 3, 44, 46], [19, 61, 28, 44], [32, 6, 70, 52], [0, 1]]
 g := ![![[49, 58], [61, 23, 68, 10], [55, 21, 5, 36], [43, 49, 45], [1], []], ![[28, 65, 46, 17, 43, 53], [10, 8, 31, 1, 49, 66], [33, 12, 63, 70, 51, 42], [11, 58, 8], [52, 40, 43], [29, 5, 57]], ![[21, 67, 24, 63, 23, 59], [22, 55, 22, 30, 64, 17], [41, 13, 62, 69, 42, 68], [12, 63, 12], [32, 13, 27], [4, 4, 19]], ![[35, 63, 5, 6, 61, 11], [12, 7, 21, 59, 18, 34], [43, 28, 35, 46, 6, 69], [68, 20, 6], [49, 46, 9], [47, 16, 6]]]
 h' := ![![[40, 3, 44, 46], [44, 43, 49], [42, 34, 31, 62], [46, 42, 41, 6], [24, 64, 16, 20], [0, 0, 1], [0, 1]], ![[19, 61, 28, 44], [29, 12, 24, 64], [48, 13, 31, 46], [38, 69, 70, 2], [49, 38, 11, 47], [24, 15, 1, 16], [40, 3, 44, 46]], ![[32, 6, 70, 52], [37, 44, 59, 48], [44, 38, 29, 12], [61, 39, 62, 24], [25, 56, 13, 56], [31, 43, 23, 58], [19, 61, 28, 44]], ![[0, 1], [13, 43, 10, 30], [40, 57, 51, 22], [18, 63, 40, 39], [27, 55, 31, 19], [22, 13, 46, 68], [32, 6, 70, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 5, 16], []]
 b := ![[], [], [10, 5, 58, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [47, 7, 55, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47744009, 147060316, 1145397, -192193365, -14396047]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11621557, 12817617, 13195612, -1084859, -14396047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3647, 1945, -862, 157, -309]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![3647, 1945, -862, 157, -309]] 
 ![![71, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![3647, 1945, -862, 157, -309], ![-1854, -988, 438, -81, 157], ![942, 501, -221, 45, -81], ![-552, -296, 130, -23, 48], ![-426, -219, 94, -39, 40]]]
  hmulB := by decide  
  f := ![![![1765, 3009, -772, 485, -321]], ![![1539, 2627, -664, 426, -278]], ![![215, 372, -79, 64, -36]], ![![1591, 2713, -694, 438, -289]], ![![294, 507, -112, 87, -50]]]
  g := ![![![-1681, 1945, -862, 157, -309], ![855, -988, 438, -81, 157], ![-437, 501, -221, 45, -81], ![255, -296, 130, -23, 48], ![208, -219, 94, -39, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1765, 3009, -772, 485, -321]] ![![3647, 1945, -862, 157, -309]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [63, 33, 10, 13, 50, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 46, 1, 34, 42], [58, 49, 2, 66, 43], [47, 10, 66, 22, 50], [9, 40, 4, 24, 11], [0, 1]]
 g := ![![[42, 51, 59, 14, 19], [17, 52, 58, 16], [72, 20, 37, 12], [28, 25, 5, 23, 1], [], []], ![[65, 57, 20, 20, 20, 41, 60, 47], [13, 13, 8, 24], [63, 57, 33, 55], [2, 51, 39, 49, 70, 66, 64, 45], [5, 35, 10, 54], [20, 47, 66, 12]], ![[48, 62, 53, 39, 15, 60, 67, 26], [53, 42, 66, 9], [10, 61, 56, 48], [8, 44, 8, 49, 40, 61, 3, 39], [0, 38, 55, 9], [70, 0, 23, 24]], ![[16, 67, 71, 44, 22, 36, 10, 35], [31, 62, 56, 2], [44, 56, 11, 2], [7, 61, 70, 5, 69, 28, 44, 25], [34, 6, 24, 19], [20, 31, 59, 18]], ![[44, 46, 35, 48, 14, 48, 64, 11], [14, 65, 23, 25], [32, 60, 42, 57], [19, 61, 1, 10, 20, 50, 68, 17], [45, 9, 46, 46], [36, 54, 26, 48]]]
 h' := ![![[55, 46, 1, 34, 42], [22, 51, 20, 32, 47], [61, 57, 71, 16, 4], [61, 56, 40, 35, 31], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[58, 49, 2, 66, 43], [48, 56, 64, 8, 36], [8, 45, 26, 25, 30], [20, 6, 5, 9, 37], [0, 4, 11, 1, 62], [13, 52, 40, 22, 45], [55, 46, 1, 34, 42]], ![[47, 10, 66, 22, 50], [43, 22, 58, 39, 71], [43, 59, 13, 13, 3], [69, 55, 9, 32, 11], [65, 50, 45, 72, 15], [49, 16, 46, 72, 3], [58, 49, 2, 66, 43]], ![[9, 40, 4, 24, 11], [21, 29, 19, 7, 64], [21, 52, 64, 66, 41], [26, 35, 35, 12, 32], [48, 33, 30, 7, 57], [0, 6, 50, 29, 47], [47, 10, 66, 22, 50]], ![[0, 1], [69, 61, 58, 60, 1], [32, 6, 45, 26, 68], [71, 67, 57, 58, 35], [21, 59, 60, 66, 11], [3, 72, 9, 23, 51], [9, 40, 4, 24, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 44, 33, 13], [], [], []]
 b := ![[], [18, 36, 42, 31, 64], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [63, 33, 10, 13, 50, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5073755938, -12985539811, 3845091916, 15130430191, 1994935897]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-69503506, -177884107, 52672492, 207266167, 27327889]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37997, -20260, 8985, -1635, 3221]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-37997, -20260, 8985, -1635, 3221]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![35, 2, 67, 25, 1]] where
  M :=![![![-37997, -20260, 8985, -1635, 3221], ![19326, 10318, -4554, 837, -1635], ![-9810, -5199, 2359, -405, 837], ![5742, 3057, -1357, 253, -486], ![4500, 2424, -1035, 201, -368]]]
  hmulB := by decide  
  f := ![![![85, 142, -45, 21, -17]], ![![-102, -170, 54, -27, 21]], ![![126, 213, -65, 27, -27]], ![![-90, -153, 49, -11, 18]], ![![113, 190, -58, 28, -24]]]
  g := ![![![-1908, -338, -2618, -1040, 3221], ![969, 172, 1329, 528, -1635], ![-495, -87, -680, -270, 837], ![288, 51, 395, 157, -486], ![220, 40, 299, 119, -368]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [45, 36, 72, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 48, 76, 52], [42, 16, 12, 42], [24, 14, 70, 64], [0, 1]]
 g := ![![[46, 7, 10, 20], [55, 36, 78, 4], [48, 50, 0, 38], [77, 42, 11, 51], [1], []], ![[5, 14, 77, 7, 6, 62], [76, 50, 10, 77, 65, 2], [73, 24, 1, 42, 62, 20], [46, 72, 15, 40, 74, 49], [76, 74, 10], [4, 35, 18]], ![[26, 47, 34, 63, 62, 5], [21, 63, 33, 51, 48, 46], [65, 11, 45, 19, 7, 51], [11, 54, 68, 20, 59, 49], [28, 38, 2], [71, 17, 26]], ![[27, 63, 2, 28, 17, 36], [7, 23], [58, 64, 64, 37, 33, 76], [50, 28, 62, 76, 49, 18], [8, 57, 11], [62, 65, 67]]]
 h' := ![![[63, 48, 76, 52], [53, 52, 37, 40], [52, 14, 9, 2], [11, 49, 34, 65], [34, 43, 7, 50], [0, 0, 1], [0, 1]], ![[42, 16, 12, 42], [18, 22, 41, 67], [36, 31, 43, 32], [8, 73, 14, 72], [65, 34, 29, 60], [76, 63, 42, 57], [63, 48, 76, 52]], ![[24, 14, 70, 64], [29, 64, 17, 70], [11, 37, 27, 45], [69, 3, 12, 17], [6, 4, 68, 15], [70, 77, 58, 9], [42, 16, 12, 42]], ![[0, 1], [69, 20, 63, 60], [4, 76], [47, 33, 19, 4], [39, 77, 54, 33], [77, 18, 57, 13], [24, 14, 70, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [44, 3, 75], []]
 b := ![[], [], [30, 33, 47, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [45, 36, 72, 29, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![586085637, 1540477835, -314095830, -1564571981, -354394773]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![164429148, 28471739, 296586759, 92345536, -354394773]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -142, 45, -21, 17]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-85, -142, 45, -21, 17]] 
 ![![79, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-85, -142, 45, -21, 17], ![102, 170, -54, 27, -21], ![-126, -213, 65, -27, 27], ![90, 153, -49, 11, -18], ![36, 66, -15, 3, -16]]]
  hmulB := by decide  
  f := ![![![37997, 20260, -8985, 1635, -3221]], ![![25728, 13718, -6084, 1107, -2181]], ![![3491, 1861, -826, 150, -296]], ![![24938, 13297, -5897, 1073, -2114]], ![![19663, 10484, -4650, 846, -1667]]]
  g := ![![![97, -142, 45, -21, 17], ![-117, 170, -54, 27, -21], ![142, -213, 65, -27, 27], ![-97, 153, -49, 11, -18], ![-37, 66, -15, 3, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-37997, -20260, 8985, -1635, 3221]] ![![-85, -142, 45, -21, 17]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [73, 12, 29, 51, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 34, 15, 82, 63], [27, 66, 48, 70, 35], [51, 1, 63, 32, 44], [79, 64, 40, 65, 24], [0, 1]]
 g := ![![[7, 35, 61, 28, 68], [82, 71, 15, 33, 33], [3, 61, 17, 31], [37, 73, 62, 69], [1], []], ![[56, 19, 71, 38, 8, 46, 26, 81], [67, 60, 36, 17, 52, 27, 52, 51], [17, 44, 81, 44], [69, 6, 14, 26], [49, 59, 58, 6, 31, 78, 25, 59], [61, 77, 38, 68]], ![[64, 32, 22, 18, 70, 0, 13, 22], [71, 8, 51, 70, 49, 24, 80, 5], [24, 9, 27, 29], [47, 27, 40, 11], [55, 50, 61, 68, 25, 79, 34, 13], [77, 32, 28, 63]], ![[81, 47, 73, 41, 71, 36, 13, 7], [35, 56, 72, 50, 69, 59, 80, 28], [37, 74, 39, 41], [39, 20, 17, 4], [55, 53, 68, 34, 82, 41, 73, 41], [13, 48, 64, 27]], ![[69, 80, 19, 63, 50, 62, 3, 67], [54, 48, 29, 59, 64, 25, 70, 52], [50, 49, 9, 11], [6, 19, 41, 37], [80, 22, 80, 79, 40, 75, 79, 14], [42, 80, 76, 78]]]
 h' := ![![[70, 34, 15, 82, 63], [73, 65, 62, 20, 63], [67, 73, 43, 22, 38], [55, 46, 61, 17, 23], [10, 71, 54, 32, 61], [0, 0, 1], [0, 1]], ![[27, 66, 48, 70, 35], [37, 63, 46, 71, 78], [81, 52, 34, 25, 63], [49, 32, 20, 67, 58], [43, 73, 9, 10, 21], [32, 67, 30, 76, 47], [70, 34, 15, 82, 63]], ![[51, 1, 63, 32, 44], [26, 49, 12, 68, 70], [14, 28, 66, 30, 57], [40, 63, 44, 59, 19], [63, 72, 32, 81, 54], [5, 55, 46, 77, 74], [27, 66, 48, 70, 35]], ![[79, 64, 40, 65, 24], [46, 44, 10, 19, 77], [36, 30, 25, 51, 12], [74, 24, 54, 43, 37], [79, 5, 33, 47, 2], [75, 11, 55, 7, 38], [51, 1, 63, 32, 44]], ![[0, 1], [31, 28, 36, 71, 44], [27, 66, 81, 38, 79], [5, 1, 70, 63, 29], [32, 28, 38, 79, 28], [21, 33, 34, 6, 7], [79, 64, 40, 65, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 60, 12, 2], [], [], []]
 b := ![[], [46, 0, 2, 14, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [73, 12, 29, 51, 22, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-417920514858, -1094619683846, 249496035224, 1148549856806, 249939322869]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5035186926, -13188188962, 3005976328, 13837950082, 3011317143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 3939040643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4625, -2331, 1242, -129, 419]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-4625, -2331, 1242, -129, 419]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![34, 38, 1, 0, 0], ![5, 13, 0, 1, 0], ![52, 33, 0, 0, 1]] where
  M :=![![![-4625, -2331, 1242, -129, 419], ![2514, 1660, -152, 297, -129], ![-774, 579, 1423, 519, 297], ![684, 324, -188, 13, -62], ![906, 1305, 854, 507, 124]]]
  hmulB := by decide  
  f := ![![![-85, -249, -16, 141, 137]], ![![822, 1970, -986, -2985, 141]], ![![328, 779, -411, -1215, 79]], ![![77, 175, -118, -317, 46]], ![![256, 549, -478, -1176, 263]]]
  g := ![![![-764, -693, 1242, -129, 419], ![145, 88, -152, 297, -129], ![-755, -787, 1423, 519, 297], ![115, 105, -188, 13, -62], ![-417, -470, 854, 507, 124]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [19, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 88], [0, 1]]
 g := ![![[32, 81], [67], [80], [20, 44], [46, 47], [1]], ![[1, 8], [67], [80], [57, 45], [39, 42], [1]]]
 h' := ![![[15, 88], [41, 80], [35, 44], [65, 76], [16, 69], [70, 15], [0, 1]], ![[0, 1], [84, 9], [72, 45], [48, 13], [72, 20], [28, 74], [15, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [67, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [19, 74, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-821, -2288, 252, 1716, 820]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-681, -688, 252, 1716, 820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18115, -51660, -49845, -24579, -8623]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-18115, -51660, -49845, -24579, -8623]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![16, 19, 1, 0, 0], ![60, 22, 0, 1, 0], ![22, 83, 0, 0, 1]] where
  M :=![![![-18115, -51660, -49845, -24579, -8623], ![-51738, -147460, -142124, -70119, -24579], ![-147474, -420423, -405397, -199965, -70119], ![3618, 10335, 10003, 4925, 1732], ![-126228, -359820, -346897, -171123, -59998]]]
  hmulB := by decide  
  f := ![![![-71579, -38166, 16915, -3093, 6065]], ![![36390, 19396, -8588, 1599, -3093]], ![![-5308, -2833, 1257, -222, 448]], ![![-39138, -20869, 9251, -1687, 3314]], ![![16340, 8710, -3851, 726, -1395]]]
  g := ![![![27459, 24178, -49845, -24579, -8623], ![78316, 68939, -142124, -70119, -24579], ![223364, 196643, -405397, -199965, -70119], ![-5506, -4852, 10003, 4925, 1732], ![191140, 168267, -346897, -171123, -59998]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [55, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 88], [0, 1]]
 g := ![![[16, 34], [9], [64], [37, 16], [78, 11], [1]], ![[0, 55], [9], [64], [19, 73], [10, 78], [1]]]
 h' := ![![[10, 88], [75, 37], [6, 3], [12, 81], [71, 85], [34, 10], [0, 1]], ![[0, 1], [0, 52], [36, 86], [21, 8], [31, 4], [45, 79], [10, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [37, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [55, 79, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2589, 2665, -2680, -6085, 1287]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4295, 906, -2680, -6085, 1287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -6, 5, 7, 1]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-7, -6, 5, 7, 1]] 
 ![![89, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-7, -6, 5, 7, 1], ![6, 8, -2, -9, 7], ![42, 111, -17, -111, -9], ![-30, -71, 43, 121, -14], ![-132, -342, 105, 399, 70]]]
  hmulB := by decide  
  f := ![![![-691583, -1155832, 367113, -167851, 139093]], ![![-239282, -399908, 127018, -58075, 48125]], ![![-353222, -590335, 187501, -85729, 71041]], ![![-302890, -506215, 160783, -73513, 60918]], ![![-315683, -527596, 167574, -76618, 63491]]]
  g := ![![![-4, -6, 5, 7, 1], ![-1, 8, -2, -9, 7], ![23, 111, -17, -111, -9], ![-44, -71, 43, 121, -14], ![-142, -342, 105, 399, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-4625, -2331, 1242, -129, 419]] ![![-18115, -51660, -49845, -24579, -8623]]
  ![![-32135809, -91606401, -88319135, -43567128, -15275364]] where
 M := ![![![-32135809, -91606401, -88319135, -43567128, -15275364]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-32135809, -91606401, -88319135, -43567128, -15275364]] ![![-7, -6, 5, 7, 1]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-710729525, -2026019763, -1953340672, -963561793, -337844089]]]
 hmul := by decide  
 g := ![![![![-7985725, -22764267, -21947648, -10826537, -3796001]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89257, -47601, 21095, -3846, 7564]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-89257, -47601, 21095, -3846, 7564]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![17, 75, 1, 0, 0], ![70, 14, 0, 1, 0], ![86, 10, 0, 0, 1]] where
  M :=![![![-89257, -47601, 21095, -3846, 7564], ![45384, 24203, -10726, 1956, -3846], ![-23076, -12306, 5453, -996, 1956], ![13494, 7197, -3189, 581, -1144], ![10542, 5619, -2489, 462, -895]]]
  hmulB := by decide  
  f := ![![![299, 483, -207, 54, -70]], ![![-420, -751, 88, -144, 54]], ![![-269, -492, 26, -102, 28]], ![![152, 235, -135, 17, -42]], ![![220, 347, -177, 30, -57]]]
  g := ![![![-8548, -17026, 21095, -3846, 7564], ![4346, 8657, -10726, 1956, -3846], ![-2209, -4401, 5453, -996, 1956], ![1293, 2574, -3189, 581, -1144], ![1005, 2008, -2489, 462, -895]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [25, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 96], [0, 1]]
 g := ![![[68, 66], [53], [35], [18], [6], [46, 1]], ![[0, 31], [53], [35], [18], [6], [92, 96]]]
 h' := ![![[46, 96], [49, 39], [93, 21], [17, 36], [46, 42], [14, 54], [0, 1]], ![[0, 1], [0, 58], [89, 76], [24, 61], [38, 55], [73, 43], [46, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [44, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [25, 51, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77, 61, -168, -593, 263]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![225, 189, -168, -593, 263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56155, -29940, 13283, -2415, 4761]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-56155, -29940, 13283, -2415, 4761]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![27, 43, 1, 0, 0], ![84, 79, 0, 1, 0], ![86, 71, 0, 0, 1]] where
  M :=![![![-56155, -29940, 13283, -2415, 4761], ![28566, 15260, -6720, 1245, -2415], ![-14490, -7659, 3515, -585, 1245], ![8490, 4527, -2009, 365, -720], ![6660, 3612, -1497, 321, -550]]]
  hmulB := by decide  
  f := ![![![5, 42, -5, -105, -15]], ![![-90, -220, 192, 555, -105]], ![![-45, -103, 86, 231, -45]], ![![-60, -121, 143, 332, -99]], ![![-44, -74, 137, 282, -115]]]
  g := ![![![-6406, -7715, 13283, -2415, 4761], ![3228, 3890, -6720, 1245, -2415], ![-1725, -2072, 3515, -585, 1245], ![969, 1167, -2009, 365, -720], ![695, 842, -1497, 321, -550]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [16, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 96], [0, 1]]
 g := ![![[15, 91], [75], [85], [62], [89], [51, 1]], ![[0, 6], [75], [85], [62], [89], [5, 96]]]
 h' := ![![[51, 96], [60, 73], [22, 47], [11, 52], [79, 81], [57, 63], [0, 1]], ![[0, 1], [0, 24], [91, 50], [44, 45], [39, 16], [69, 34], [51, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [81, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [16, 46, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![625, 1162, -143, -1634, 227]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1260, 1240, -143, -1634, 227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7495, -4328, 1857, -381, 669]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-7495, -4328, 1857, -381, 669]] 
 ![![97, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-7495, -4328, 1857, -381, 669], ![4014, 2540, -1052, 243, -381], ![-2286, -1701, 665, -183, 243], ![1386, 1077, -415, 119, -152], ![960, 636, -259, 63, -94]]]
  hmulB := by decide  
  f := ![![![89, 266, 377, 285, 69]], ![![74, 220, 304, 225, 57]], ![![58, 169, 195, 123, 33]], ![![25, 79, 144, 128, 23]], ![![-5, -8, 80, 108, 29]]]
  g := ![![![2533, -4328, 1857, -381, 669], ![-1516, 2540, -1052, 243, -381], ![1046, -1701, 665, -183, 243], ![-667, 1077, -415, 119, -152], ![-383, 636, -259, 63, -94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-89257, -47601, 21095, -3846, 7564]] ![![-56155, -29940, 13283, -2415, 4761]]
  ![![3364513819, 1794307041, -795169780, 144976089, -285123967]] where
 M := ![![![3364513819, 1794307041, -795169780, 144976089, -285123967]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![3364513819, 1794307041, -795169780, 144976089, -285123967]] ![![-7495, -4328, 1857, -381, 669]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-16269706642717, -8676691723871, 3845185281569, -701057739666, 1378767793120]]]
 hmul := by decide  
 g := ![![![![-167728934461, -89450430143, 39641085377, -7227399378, 14214100960]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101203, 169144, -53725, 24563, -20355]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101203, 169144, -53725, 24563, -20355]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![49, 67, 42, 1, 0], ![20, 31, 36, 0, 1]] where
  M :=![![![101203, 169144, -53725, 24563, -20355], ![-122130, -204122, 64826, -29649, 24563], ![147378, 246315, -78247, 35769, -29649], ![-103338, -172717, 54857, -25069, 20786], ![-37920, -63384, 20103, -9237, 7640]]]
  hmulB := by decide  
  f := ![![![166559, 88826, -39365, 7177, -14115]], ![![-84690, -45166, 20014, -3651, 7177]], ![![43062, 22965, -10181, 1851, -3651]], ![![42283, 22549, -9996, 1819, -3584]], ![![22142, 11808, -5235, 952, -1877]]]
  g := ![![![-6884, -8372, -3491, 24563, -20355], ![8311, 10108, 4216, -29649, 24563], ![-10023, -12189, -5081, 35769, -29649], ![7023, 8540, 3559, -25069, 20786], ![2593, 3155, 1317, -9237, 7640]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [85, 7, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 37, 58], [50, 63, 43], [0, 1]]
 g := ![![[80, 36, 19], [48, 54], [93, 70, 1], [92, 77], [29, 87], [1]], ![[77, 82, 2, 95], [12, 70], [91, 68, 84, 1], [95, 52], [93, 47], [66, 43, 71, 81]], ![[66, 88, 86, 47], [29, 100], [10, 77, 21, 80], [20, 47], [70, 19], [1, 37, 38, 20]]]
 h' := ![![[68, 37, 58], [83, 32, 76], [74, 84, 85], [25, 24, 100], [13, 56, 73], [16, 94, 17], [0, 1]], ![[50, 63, 43], [67, 16, 79], [28, 90, 26], [22, 5, 16], [57, 73, 70], [65, 6, 59], [68, 37, 58]], ![[0, 1], [30, 53, 47], [77, 28, 91], [60, 72, 86], [89, 73, 59], [79, 1, 25], [50, 63, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 25], []]
 b := ![[], [11, 5, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [85, 7, 84, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![399297, 921872, -554148, -1560962, 196126]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![722415, 984420, 573720, -1560962, 196126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-166559, -88826, 39365, -7177, 14115]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-166559, -88826, 39365, -7177, 14115]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![4, 54, 1, 0, 0], ![63, 60, 0, 1, 0], ![54, 87, 0, 0, 1]] where
  M :=![![![-166559, -88826, 39365, -7177, 14115], ![84690, 45166, -20014, 3651, -7177], ![-43062, -22965, 10181, -1851, 3651], ![25182, 13433, -5953, 1079, -2134], ![19680, 10506, -4647, 843, -1672]]]
  hmulB := by decide  
  f := ![![![-101203, -169144, 53725, -24563, 20355]], ![![122130, 204122, -64826, 29649, -24563]], ![![59830, 99997, -31757, 14525, -12033]], ![![10449, 17465, -5542, 2540, -2101]], ![![51468, 86022, -27315, 12498, -10351]]]
  g := ![![![-6278, -29821, 39365, -7177, 14115], ![3191, 15161, -20014, 3651, -7177], ![-1627, -7716, 10181, -1851, 3651], ![953, 4513, -5953, 1079, -2134], ![747, 3528, -4647, 843, -1672]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [37, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 100], [0, 1]]
 g := ![![[33, 71], [36], [39, 65], [30], [17], [92, 1]], ![[0, 30], [36], [60, 36], [30], [17], [83, 100]]]
 h' := ![![[92, 100], [14, 24], [72, 95], [15, 41], [69, 63], [30, 44], [0, 1]], ![[0, 1], [0, 77], [25, 6], [50, 60], [7, 38], [38, 57], [92, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [74, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [37, 9, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![83, -14, 7, 37, -1]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22, -25, 7, 37, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101203, 169144, -53725, 24563, -20355]] ![![-166559, -88826, 39365, -7177, 14115]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-539783, -287868, 127572, -23260, 45744]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-539783, -287868, 127572, -23260, 45744]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![79, 23, 27, 1, 0], ![5, 27, 33, 0, 1]] where
  M :=![![![-539783, -287868, 127572, -23260, 45744], ![274464, 146377, -64868, 11820, -23260], ![-139560, -74436, 32993, -5988, 11820], ![81600, 43508, -19288, 3521, -6908], ![63792, 34068, -15116, 2628, -5383]]]
  hmulB := by decide  
  f := ![![![1279, 2084, -828, 260, -288]], ![![-1728, -3041, 492, -564, 260]], ![![1560, 2172, -2041, -36, -564]], ![![991, 1467, -1053, 61, -308]], ![![101, -17, -571, -152, -127]]]
  g := ![![![10379, -9592, -7320, -23260, 45744], ![-5272, 4879, 3724, 11820, -23260], ![2664, -2484, -1897, -5988, 11820], ![-1573, 1447, 1103, 3521, -6908], ![-1135, 1155, 889, 2628, -5383]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [1, 37, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 5, 83], [50, 97, 20], [0, 1]]
 g := ![![[94, 35, 82], [4, 21, 52], [97, 81, 64], [5, 36], [60, 82], [1]], ![[85, 17, 46, 46], [78, 21, 40, 76], [1, 26, 49, 19], [87, 63], [26, 58], [83, 4, 75, 34]], ![[17, 3, 100, 86], [18, 36, 77, 21], [11, 99, 44, 65], [4, 23], [25, 59], [51, 38, 64, 69]]]
 h' := ![![[9, 5, 83], [99, 73, 44], [6, 96, 19], [77, 33, 8], [44, 38, 6], [102, 66, 59], [0, 1]], ![[50, 97, 20], [85, 83, 27], [91, 82, 26], [46, 95, 13], [37, 86, 28], [28, 97, 77], [9, 5, 83]], ![[0, 1], [34, 50, 32], [72, 28, 58], [59, 78, 82], [75, 82, 69], [10, 43, 70], [50, 97, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 49], []]
 b := ![[], [92, 69, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [1, 37, 44, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32903401, -77316536, 40620824, 121703418, -12595036]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93053381, -24625526, -27473158, 121703418, -12595036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1279, 2084, -828, 260, -288]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1279, 2084, -828, 260, -288]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![26, 47, 1, 0, 0], ![58, 59, 0, 1, 0], ![5, 84, 0, 0, 1]] where
  M :=![![![1279, 2084, -828, 260, -288], ![-1728, -3041, 492, -564, 260], ![1560, 2172, -2041, -36, -564], ![-1344, -2236, 744, -313, 276], ![-816, -1740, -604, -540, -49]]]
  hmulB := by decide  
  f := ![![![-539783, -287868, 127572, -23260, 45744]], ![![274464, 146377, -64868, 11820, -23260]], ![![-12370, -6595, 2923, -536, 1048]], ![![-145946, -77831, 34492, -6293, 12368]], ![![198251, 105732, -46856, 8536, -16801]]]
  g := ![![![89, 484, -828, 260, -288], ![164, -143, 492, -564, 260], ![578, 1433, -2041, -36, -564], ![-38, -407, 744, -313, 276], ![451, 608, -604, -540, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [89, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 102], [0, 1]]
 g := ![![[9, 25], [71, 58], [55, 32], [93], [63], [23, 1]], ![[69, 78], [66, 45], [70, 71], [93], [63], [46, 102]]]
 h' := ![![[23, 102], [67, 5], [49, 26], [95, 49], [21, 14], [13, 28], [0, 1]], ![[0, 1], [79, 98], [29, 77], [89, 54], [34, 89], [39, 75], [23, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [43, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [89, 80, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2042, 4036, -3746, -8564, 2840]
  a := ![1, 3, -8, -1, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5650, 4338, -3746, -8564, 2840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-539783, -287868, 127572, -23260, 45744]] ![![1279, 2084, -828, 260, -288]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB1556I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1556I2 : PrimesBelowBoundCertificateInterval O 61 103 1556 where
  m := 9
  g := ![1, 2, 1, 2, 1, 3, 3, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1556I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
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
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![38950081, 79]
    · exact ![3939040643]
    · exact ![7921, 7921, 89]
    · exact ![9409, 9409, 97]
    · exact ![1030301, 10201]
    · exact ![1092727, 10609]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I71N1, I79N1, I89N2, I97N2]
  Il := ![[], [I71N1], [], [I79N1], [], [I89N2], [I97N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
