
import IdealArithmetic.Examples.NF5_1_3515625_1.RI5_1_3515625_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -2, 5, 1, -10]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-3, -2, 5, 1, -10]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![59, 52, 1, 0, 0], ![35, 30, 0, 1, 0], ![44, 72, 0, 0, 1]] where
  M :=![![![-3, -2, 5, 1, -10], ![-12, 6, -6, 11, -18], ![52, -5, -38, -32, 170], ![84, -86, 123, -80, -24], ![-6, -7, 24, 1, -55]]]
  hmulB := by decide  
  f := ![![![-337, 43, -130, 49, -376]], ![![-360, -10, -153, 50, -426]], ![![-365, 19, -148, 52, -420]], ![![-217, 12, -88, 31, -250]], ![![-382, 11, -157, 54, -443]]]
  g := ![![![1, 4, 5, 1, -10], ![7, 12, -6, 11, -18], ![-38, -87, -38, -32, 170], ![-31, -22, 123, -80, -24], ![9, 25, 24, 1, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [40, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 106], [0, 1]]
 g := ![![[101, 99], [56, 39], [85], [68, 76], [36], [26, 1]], ![[0, 8], [0, 68], [85], [11, 31], [36], [52, 106]]]
 h' := ![![[26, 106], [7, 45], [16, 57], [62, 37], [102, 41], [30, 101], [0, 1]], ![[0, 1], [0, 62], [0, 50], [61, 70], [98, 66], [88, 6], [26, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [100, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [40, 81, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3635, -1578, -240, -2893, 8294]
  a := ![-20, 2, 9, 9, -55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2298, -4668, -240, -2893, 8294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78, -88, 19, -18, 83]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![78, -88, 19, -18, 83]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![25, 101, 1, 0, 0], ![43, 96, 0, 1, 0], ![69, 25, 0, 0, 1]] where
  M :=![![![78, -88, 19, -18, 83], ![22, 13, -16, 8, -64], ![-64, 78, -19, 16, -80], ![-32, 0, 14, -3, 32], ![-43, 44, -8, 9, -39]]]
  hmulB := by decide  
  f := ![![![-119, 10, -53, 17, -147]], ![![-158, 11, -58, 26, -214]], ![![-179, 13, -68, 29, -239]], ![![-191, 14, -75, 30, -251]], ![![-114, 9, -48, 17, -145]]]
  g := ![![![-50, -22, 19, -18, 83], ![42, 23, -16, 8, -64], ![49, 23, -19, 16, -80], ![-23, -18, 14, -3, 32], ![23, 9, -8, 9, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [59, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 106], [0, 1]]
 g := ![![[36, 14], [63, 61], [25], [74, 40], [75], [16, 1]], ![[46, 93], [76, 46], [25], [72, 67], [75], [32, 106]]]
 h' := ![![[16, 106], [28, 96], [36, 75], [21, 5], [2, 19], [19, 90], [0, 1]], ![[0, 1], [66, 11], [59, 32], [101, 102], [92, 88], [68, 17], [16, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [65, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [59, 91, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![816651, -345577, 8711, -595692, 1734506]
  a := ![-239, -1, 122, 120, -658]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-873526, 117742, 8711, -595692, 1734506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -2, 10, 3, -29]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-6, -2, 10, 3, -29]] 
 ![![107, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-6, -2, 10, 3, -29], ![-34, 20, -14, 27, -50], ![116, -11, -88, -72, 394], ![212, -206, 277, -194, -8], ![-11, -19, 56, 0, -117]]]
  hmulB := by decide  
  f := ![![![-4775, 583, -1985, 744, -5801]], ![![-2775, 335, -1154, 432, -3371]], ![![-1136, 134, -474, 177, -1384]], ![![-1602, 193, -668, 250, -1952]], ![![-1848, 224, -769, 288, -2247]]]
  g := ![![![9, -2, 10, 3, -29], ![2, 20, -14, 27, -50], ![-101, -11, -88, -72, 394], ![122, -206, 277, -194, -8], ![43, -19, 56, 0, -117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-3, -2, 5, 1, -10]] ![![78, -88, 19, -18, 83]]
  ![![-200, 188, -26, 25, -99]] where
 M := ![![![-200, 188, -26, 25, -99]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-200, 188, -26, 25, -99]] ![![-6, -2, 10, 3, -29]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-1819, 1177, -963, 1498, -2461]]]
 hmul := by decide  
 g := ![![![![-17, 11, -9, 14, -23]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [11, 103, 92, 3, 48, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 7, 77, 108, 27], [107, 9, 38, 57, 4], [108, 71, 10, 105, 93], [106, 21, 93, 57, 94], [0, 1]]
 g := ![![[93, 7, 3, 83, 82], [48, 1], [57, 2, 16, 100, 12], [49, 48, 80, 4, 35], [61, 1], []], ![[81, 70, 96, 100, 24, 55, 66, 82], [39, 24, 89, 106], [13, 99, 35, 17, 16, 12, 32, 89], [9, 28, 77, 97, 39, 30, 30, 87], [11, 32, 99, 9], [9, 50, 84, 33, 37, 77, 21, 63]], ![[46, 52, 0, 38, 31, 72, 33, 100], [66, 82, 70, 27], [4, 35, 29, 27, 45, 32, 4, 1], [98, 105, 58, 89, 40, 11, 91, 82], [69, 75, 11, 63], [96, 92, 39, 57, 20, 68, 100, 64]], ![[87, 79, 96, 11, 97, 65, 86, 26], [93, 92, 82, 12], [51, 38, 92, 58, 48, 107, 71, 46], [11, 44, 77, 91, 33, 54, 93, 89], [74, 62, 80, 9], [56, 103, 6, 106, 81, 31, 61, 46]], ![[52, 92, 106, 45, 27, 25, 104, 84], [38, 95, 42, 20], [38, 84, 5, 29, 77, 47, 88, 46], [86, 72, 56, 30, 75, 75, 0, 49], [31, 39, 72, 63], [98, 35, 14, 93, 50, 99, 24, 4]]]
 h' := ![![[67, 7, 77, 108, 27], [92, 99, 4, 95, 55], [27, 29, 48, 1], [6, 55, 52, 108, 98], [92, 28, 62, 52, 12], [0, 0, 0, 1], [0, 1]], ![[107, 9, 38, 57, 4], [91, 71, 45, 41, 76], [56, 70, 74, 53, 91], [47, 27, 22, 15, 84], [8, 88, 101, 31, 57], [42, 33, 46, 34, 3], [67, 7, 77, 108, 27]], ![[108, 71, 10, 105, 93], [42, 19, 26, 107, 5], [88, 42, 103, 48, 71], [77, 41, 22, 98, 55], [26, 82, 79, 94, 82], [26, 108, 90, 45, 64], [107, 9, 38, 57, 4]], ![[106, 21, 93, 57, 94], [38, 105, 77, 64, 98], [84, 100, 101, 89, 98], [106, 56, 54, 1, 16], [10, 37, 30, 11, 65], [37, 70, 36, 60, 106], [108, 71, 10, 105, 93]], ![[0, 1], [99, 33, 66, 20, 93], [100, 86, 1, 27, 67], [106, 39, 68, 105, 74], [102, 92, 55, 30, 2], [94, 7, 46, 78, 45], [106, 21, 93, 57, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 101, 2, 24], [], [], []]
 b := ![[], [15, 90, 91, 90, 96], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [11, 103, 92, 3, 48, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54708223027, -7851294307, -35447567033, -34808810683, 175974146608]
  a := ![-17, 1, 9, 8, -47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![501910303, -72030223, -325207037, -319346887, 1614441712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 15386239549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, 32, -4, 5, -17]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-36, 32, -4, 5, -17]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![65, 44, 1, 0, 0], ![78, 50, 0, 1, 0], ![43, 49, 0, 0, 1]] where
  M :=![![![-36, 32, -4, 5, -17], ![6, -24, 12, -7, 42], ![28, -29, 4, -2, 14], ![12, 16, -21, -2, 12], ![21, -15, 0, -4, 13]]]
  hmulB := by decide  
  f := ![![![383, -33, 167, -60, 483]], ![![486, -40, 207, -76, 612]], ![![415, -35, 179, -65, 523]], ![![486, -41, 210, -76, 612]], ![![358, -30, 154, -56, 451]]]
  g := ![![![5, 7, -4, 5, -17], ![-18, -20, 12, -7, 42], ![-6, -7, 4, -2, 14], ![9, 4, -21, -2, 12], ![-2, -4, 0, -4, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [101, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 112], [0, 1]]
 g := ![![[70, 53], [95], [51], [64], [10, 18], [49, 1]], ![[68, 60], [95], [51], [64], [101, 95], [98, 112]]]
 h' := ![![[49, 112], [1, 36], [45, 78], [26, 86], [7, 105], [23, 40], [0, 1]], ![[0, 1], [70, 77], [25, 35], [59, 27], [67, 8], [62, 73], [49, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [17, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [101, 64, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![155577, -62639, -1176, -111369, 332681]
  a := ![103, -3, -50, -52, 283]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-47668, -95078, -1176, -111369, 332681]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![226, -16, 95, -34, 273]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![226, -16, 95, -34, 273]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![94, 14, 1, 0, 0], ![40, 11, 0, 1, 0], ![101, 25, 0, 0, 1]] where
  M :=![![![226, -16, 95, -34, 273], ![274, -13, 120, -42, 344], ![352, -28, 155, -56, 452], ![456, -44, 196, -73, 576], ![103, -10, 46, -17, 135]]]
  hmulB := by decide  
  f := ![![![1, -2, 5, 5, -35]], ![![-30, 31, -22, 20, -30]], ![![-2, 2, 1, 6, -30]], ![![-2, 1, 2, 3, -18]], ![![-6, 5, 0, 9, -39]]]
  g := ![![![-309, -69, 95, -34, 273], ![-390, -87, 120, -42, 344], ![-510, -114, 155, -56, 452], ![-648, -145, 196, -73, 576], ![-152, -34, 46, -17, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [9, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 112], [0, 1]]
 g := ![![[29, 88], [13], [57], [85], [76, 51], [78, 1]], ![[0, 25], [13], [57], [85], [99, 62], [43, 112]]]
 h' := ![![[78, 112], [87, 38], [54, 37], [62, 82], [107, 56], [89, 86], [0, 1]], ![[0, 1], [0, 75], [2, 76], [17, 31], [68, 57], [17, 27], [78, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [99, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [9, 35, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24741, -11723, 3025, -18582, 48126]
  a := ![-43, 5, 22, 23, -118]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38735, -9317, 3025, -18582, 48126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 1, -1, 3]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![2, -1, 1, -1, 3]] 
 ![![113, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![2, -1, 1, -1, 3], ![-2, 0, 3, 2, -10], ![-4, 6, -8, 5, 4], ![48, -13, -14, -32, 126], ![7, -3, 1, -5, 13]]]
  hmulB := by decide  
  f := ![![![-247, 222, -2, 28, -43]], ![![-119, 106, 0, 13, -17]], ![![-54, 49, 0, 6, -8]], ![![-85, 78, -1, 10, -17]], ![![-132, 119, -1, 15, -23]]]
  g := ![![![-1, -1, 1, -1, 3], ![4, 0, 3, 2, -10], ![-5, 6, -8, 5, 4], ![-47, -13, -14, -32, 126], ![-4, -3, 1, -5, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-36, 32, -4, 5, -17]] ![![226, -16, 95, -34, 273]]
  ![![-247, 222, -2, 28, -43]] where
 M := ![![![-247, 222, -2, 28, -43]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-247, 222, -2, 28, -43]] ![![2, -1, 1, -1, 3]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)


lemma PB117I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 116 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 116 (by omega)

def PB117I3 : PrimesBelowBoundCertificateInterval O 103 116 117 where
  m := 3
  g := ![3, 1, 3]
  P := ![107, 109, 113]
  hP := PB117I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![11449, 11449, 107]
    · exact ![15386239549]
    · exact ![12769, 12769, 113]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
  β := ![I107N2, I113N2]
  Il := ![[I107N2], [], [I113N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
