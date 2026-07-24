
import IdealArithmetic.Examples.NF3_3_600925_1.RI3_3_600925_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-20, -28, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-20, -28, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![63, 55, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-20, -28, 1], ![146, 55, -82], ![-3942, -1236, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -55, 83]], ![![-1, -1, 1], ![64, 55, -82], ![-27, 3, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [30, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 82], [0, 1]]
 g := ![![[33, 36], [51, 33], [36], [63], [22, 36], [1]], ![[0, 47], [0, 50], [36], [63], [72, 47], [1]]]
 h' := ![![[6, 82], [47, 6], [62, 45], [35, 77], [4, 35], [53, 6], [0, 1]], ![[0, 1], [0, 77], [0, 38], [82, 6], [48, 48], [6, 77], [6, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [77, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [30, 77, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1198, 980, 463]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-337, -295, 463]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-1, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-1, 1, 0]] 
 ![![83, 0, 0], ![82, 1, 0], ![27, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-1, 1, 0], ![0, -2, 3], ![146, 47, 1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![249, 0, 0]], ![![4, -3, 0], ![250, 0, 0]], ![![2, -1, -1], ![139, 28, 0]]]
  g := ![![![1, 0, 0], ![-82, 83, 0], ![-27, 0, 83]], ![![-1, 1, 0], ![1, -2, 3], ![-45, 47, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-20, -28, 1]] ![![83, 0, 0], ![-1, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-83, 83, 0]], ![![-1660, -2324, 83], ![166, 83, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-1, 1, 0]]], ![![![-20, -28, 1]], ![![2, 1, -1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 3, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 3, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![78, 3, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 3, 1], ![146, 33, 11], ![584, 221, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -3, 89]], ![![-1, 0, 1], ![-8, 0, 11], ![-32, 1, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [24, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 88], [0, 1]]
 g := ![![[43, 53], [10], [42], [12, 11], [72, 50], [1]], ![[82, 36], [10], [42], [52, 78], [3, 39], [1]]]
 h' := ![![[36, 88], [48, 26], [56, 59], [68, 24], [52, 10], [65, 36], [0, 1]], ![[0, 1], [5, 63], [44, 30], [42, 65], [56, 79], [26, 53], [36, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [65, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [24, 53, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![994, 1784, 2701]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2356, -71, 2701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 1, 0]] 
 ![![89, 0, 0], ![78, 1, 0], ![45, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 1, 0], ![0, -12, 3], ![146, 47, -9]]]
  hmulB := by decide  
  f := ![![![914, -83, 0], ![7387, 0, 0]], ![![804, -73, 0], ![6498, 0, 0]], ![![474, -39, -1], ![3831, 30, 0]]]
  g := ![![![1, 0, 0], ![-78, 89, 0], ![-45, 0, 89]], ![![-1, 1, 0], ![9, -12, 3], ![-35, 47, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-11, 3, 1]] ![![89, 0, 0], ![-11, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-979, 89, 0]], ![![-979, 267, 89], ![267, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-11, 1, 0]]], ![![![-11, 3, 1]], ![![3, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 137, -36]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![547, 137, -36]] 
 ![![97, 0, 0], ![0, 97, 0], ![36, 42, 1]] where
  M :=![![![547, 137, -36], ![-5256, -1282, 339], ![14746, 3559, -943]]]
  hmulB := by decide  
  f := ![![![25, 11, 3]], ![![438, 155, 39]], ![![220, 79, 20]]]
  g := ![![![19, 17, -36], ![-180, -160, 339], ![502, 445, -943]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [66, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 96], [0, 1]]
 g := ![![[9, 25], [70], [64], [49], [70], [85, 1]], ![[0, 72], [70], [64], [49], [70], [73, 96]]]
 h' := ![![[85, 96], [37, 92], [1, 78], [65, 8], [1, 7], [16, 78], [0, 1]], ![[0, 1], [0, 5], [35, 19], [66, 89], [14, 90], [50, 19], [85, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [68, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [66, 12, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3394, 15, 423]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-122, -183, 423]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 11, 3]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![25, 11, 3]] 
 ![![97, 0, 0], ![66, 1, 0], ![25, 0, 1]] where
  M :=![![![25, 11, 3], ![438, 155, 39], ![2044, 757, 194]]]
  hmulB := by decide  
  f := ![![![547, 137, -36]], ![![318, 80, -21]], ![![293, 72, -19]]]
  g := ![![![-8, 11, 3], ![-111, 155, 39], ![-544, 757, 194]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![547, 137, -36]] ![![25, 11, 3]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [2, 63, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 23, 68], [40, 77, 33], [0, 1]]
 g := ![![[98, 91, 30], [31, 19], [60, 44, 9], [33, 64], [34, 96], [1]], ![[7, 6, 65, 23], [94, 58], [35, 27, 50, 45], [9, 84], [63, 13], [48, 40, 63, 19]], ![[19, 84, 77, 31], [19, 17], [13, 52, 68, 76], [41, 17], [34, 20], [63, 68, 3, 82]]]
 h' := ![![[6, 23, 68], [97, 96, 38], [82, 70, 25], [91, 73, 3], [37, 39, 8], [99, 38, 46], [0, 1]], ![[40, 77, 33], [98, 78, 61], [36, 12, 19], [61, 49, 44], [33, 18, 36], [19, 87, 66], [6, 23, 68]], ![[0, 1], [39, 28, 2], [73, 19, 57], [56, 80, 54], [80, 44, 57], [42, 77, 90], [40, 77, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 54], []]
 b := ![[], [9, 0, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [2, 63, 55, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5437941, -2439352, -1046057]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53841, -24152, -10357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [41, 40, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 46], [52, 56], [0, 1]]
 g := ![![[91, 93, 83], [18, 34, 68], [99, 92, 33], [26, 56], [27, 17], [1]], ![[41, 42, 13], [85, 22, 100], [93, 15, 97], [77, 1], [48, 61], [1]], ![[81, 71, 7], [52, 47, 38], [76, 99, 76], [54, 46], [87, 25], [1]]]
 h' := ![![[80, 46], [86, 62, 86], [61, 49, 58], [46, 51, 41], [59, 61, 46], [62, 63, 29], [0, 1]], ![[52, 56], [70, 96, 78], [55, 36, 55], [65, 50, 30], [21, 24, 1], [49, 38, 79], [80, 46]], ![[0, 1], [87, 48, 42], [100, 18, 93], [56, 2, 32], [101, 18, 56], [75, 2, 98], [52, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96], []]
 b := ![[], [86, 71, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [41, 40, 74, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-778577, -313120, -101867]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7559, -3040, -989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [58, 82, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 90, 35], [40, 16, 72], [0, 1]]
 g := ![![[86, 14, 33], [37, 14, 101], [56, 105], [43, 67, 12], [63, 34], [1]], ![[94, 48, 80, 41], [0, 64, 41, 102], [40, 27], [74, 3, 90, 57], [100, 105], [69, 104, 96, 75]], ![[26, 16, 4, 24], [11, 15, 31, 55], [83, 101], [86, 100, 98, 98], [53, 25], [10, 44, 81, 32]]]
 h' := ![![[41, 90, 35], [101, 46, 56], [88, 31, 84], [74, 76, 31], [31, 20, 71], [49, 25, 81], [0, 1]], ![[40, 16, 72], [19, 1, 45], [12, 59, 75], [37, 7, 53], [22, 5, 17], [77, 56, 31], [41, 90, 35]], ![[0, 1], [53, 60, 6], [101, 17, 55], [97, 24, 23], [27, 82, 19], [76, 26, 102], [40, 16, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 36], []]
 b := ![[], [101, 64, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [58, 82, 26, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![192038785, 79412190, 29031240]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1794755, 742170, 271320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-71, 14, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-71, 14, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![38, 14, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-71, 14, 1], ![146, -38, 44], ![2190, 738, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -14, 109]], ![![-1, 0, 1], ![-14, -6, 44], ![18, 6, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [49, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 108], [0, 1]]
 g := ![![[81, 89], [1], [3, 60], [84, 82], [87], [64, 1]], ![[0, 20], [1], [28, 49], [100, 27], [87], [19, 108]]]
 h' := ![![[64, 108], [87, 31], [71, 108], [26, 96], [68, 55], [25, 14], [0, 1]], ![[0, 1], [0, 78], [7, 1], [66, 13], [100, 54], [49, 95], [64, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [70, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [49, 45, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5, 42, 3]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 0, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-44, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-44, 1, 0]] 
 ![![109, 0, 0], ![65, 1, 0], ![103, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-44, 1, 0], ![0, -45, 3], ![146, 47, -42]]]
  hmulB := by decide  
  f := ![![![3477, -79, 0], ![8611, 0, 0]], ![![2113, -48, 0], ![5233, 0, 0]], ![![3263, -44, -2], ![8081, 73, 0]]]
  g := ![![![1, 0, 0], ![-65, 109, 0], ![-103, 0, 109]], ![![-1, 1, 0], ![24, -45, 3], ![13, 47, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-71, 14, 1]] ![![109, 0, 0], ![-44, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4796, 109, 0]], ![![-7739, 1526, 109], ![3270, -654, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-44, 1, 0]]], ![![![-71, 14, 1]], ![![30, -6, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [29, 99, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 109, 24], [101, 3, 89], [0, 1]]
 g := ![![[70, 1, 60], [59, 62], [25, 32], [93, 32], [99, 55, 64], [1]], ![[50, 102, 75, 73], [5, 1], [90, 63], [36, 102], [89, 91, 12, 94], [87, 106, 16, 38]], ![[26, 41, 61, 37], [85, 82], [20, 25], [37, 1], [83, 9, 106, 93], [70, 59, 64, 75]]]
 h' := ![![[4, 109, 24], [47, 39, 25], [96, 60, 47], [97, 86, 22], [67, 67, 22], [84, 14, 105], [0, 1]], ![[101, 3, 89], [90, 80, 107], [110, 50, 112], [102, 49, 96], [109, 12, 92], [27, 99, 86], [4, 109, 24]], ![[0, 1], [71, 107, 94], [84, 3, 67], [72, 91, 108], [44, 34, 112], [84, 0, 35], [101, 3, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 25], []]
 b := ![[], [14, 41, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [29, 99, 8, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4402367, 1973432, 860834]
  a := ![0, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38959, 17464, 7618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![127, 0, 0], ![5, 1, 0], ![78, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 4, 3], ![146, 47, 7]]]
  hmulB := by decide  
  f := ![![![113, 7, -3]], ![![1, 0, 0]], ![![74, 5, -2]]]
  g := ![![![0, 1, 0], ![-2, 4, 3], ![-5, 47, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5241, 139, -106]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![5241, 139, -106]] 
 ![![127, 0, 0], ![51, 1, 0], ![39, 0, 1]] where
  M :=![![![5241, 139, -106], ![-15476, 120, 205], ![4818, -1947, 325]]]
  hmulB := by decide  
  f := ![![![-438135, -161207, -41215]], ![![-223325, -82170, -21008]], ![![-367251, -135126, -34547]]]
  g := ![![![18, 139, -106], ![-233, 120, 205], ![720, -1947, 325]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23387, 8605, 2200]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![23387, 8605, 2200]] 
 ![![127, 0, 0], ![70, 1, 0], ![41, 0, 1]] where
  M :=![![![23387, 8605, 2200], ![321200, 118182, 30215], ![1577530, 580435, 148397]]]
  hmulB := by decide  
  f := ![![![-10729, -815, 325]], ![![-5540, -407, 165]], ![![-4027, -360, 133]]]
  g := ![![![-5269, 8605, 2200], ![-72365, 118182, 30215], ![-355411, 580435, 148397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![5, 1, 0]] ![![5241, 139, -106]]
  ![![10729, 815, -325]] where
 M := ![![![10729, 815, -325]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![10729, 815, -325]] ![![23387, 8605, 2200]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [126, 48, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 34, 127], [15, 96, 4], [0, 1]]
 g := ![![[52, 54, 112], [118, 121, 80], [77, 59], [84, 94], [56, 100], [13, 1], []], ![[93, 64, 123, 22], [54, 51, 62, 128], [35, 53], [57, 121], [50, 123], [126, 46], [67, 16]], ![[50, 60, 14, 13], [16, 57, 69, 94], [108, 52], [35, 21], [116, 33], [21, 108], [59, 16]]]
 h' := ![![[129, 34, 127], [66, 42, 80], [56, 47, 39], [8, 19, 37], [51, 3, 116], [65, 36, 121], [0, 0, 1], [0, 1]], ![[15, 96, 4], [116, 96, 45], [83, 12, 19], [68, 102, 70], [69, 57, 120], [9, 15, 75], [77, 3, 96], [129, 34, 127]], ![[0, 1], [114, 124, 6], [81, 72, 73], [14, 10, 24], [25, 71, 26], [121, 80, 66], [127, 128, 34], [15, 96, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 114], []]
 b := ![[], [1, 97, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [126, 48, 118, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1329650, -478936, -112136]
  a := ![2, -2, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10150, -3656, -856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![215, 52, -14]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![215, 52, -14]] 
 ![![137, 0, 0], ![0, 137, 0], ![14, 55, 1]] where
  M :=![![![215, 52, -14], ![-2044, -495, 128], ![5548, 1324, -367]]]
  hmulB := by decide  
  f := ![![![-89, -4, 2]], ![![292, 9, -8]], ![![106, 3, -3]]]
  g := ![![![3, 6, -14], ![-28, -55, 128], ![78, 157, -367]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [60, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 136], [0, 1]]
 g := ![![[77, 16], [9], [126], [108, 69], [130], [74], [1]], ![[0, 121], [9], [126], [127, 68], [130], [74], [1]]]
 h' := ![![[38, 136], [15, 133], [12, 134], [96, 20], [59, 53], [119, 33], [77, 38], [0, 1]], ![[0, 1], [0, 4], [35, 3], [34, 117], [18, 84], [3, 104], [14, 99], [38, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [79, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [60, 99, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1516, 6, 441]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -177, 441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 4, -2]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![89, 4, -2]] 
 ![![137, 0, 0], ![107, 1, 0], ![101, 0, 1]] where
  M :=![![![89, 4, -2], ![-292, -9, 8], ![292, 28, -1]]]
  hmulB := by decide  
  f := ![![![-215, -52, 14]], ![![-153, -37, 10]], ![![-199, -48, 13]]]
  g := ![![![-1, 4, -2], ![-1, -9, 8], ![-19, 28, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![215, 52, -14]] ![![89, 4, -2]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB173I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB173I2 : PrimesBelowBoundCertificateInterval O 79 137 173 where
  m := 11
  g := ![2, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB173I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I109N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [], [], [I109N1], [], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
