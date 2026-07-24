
import IdealArithmetic.Examples.NF3_1_420812_2.RI3_1_420812_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [7, 53, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 33, 70], [35, 49, 13], [0, 1]]
 g := ![![[55, 68, 49], [77, 37, 65], [66, 65], [52, 70], [22, 65, 1], []], ![[28, 33, 65, 3], [30, 66, 29, 31], [69, 38], [76, 59], [25, 22, 62, 78], [1, 3]], ![[46, 28, 22, 35], [5, 72, 12, 74], [68, 33], [33, 59], [41, 65, 60, 47], [58, 3]]]
 h' := ![![[30, 33, 70], [42, 27, 76], [47, 13, 56], [29, 14, 56], [12, 39, 53], [0, 0, 1], [0, 1]], ![[35, 49, 13], [79, 82, 53], [64, 12, 2], [76, 45, 72], [39, 49, 15], [63, 80, 49], [30, 33, 70]], ![[0, 1], [68, 57, 37], [52, 58, 25], [69, 24, 38], [47, 78, 15], [72, 3, 33], [35, 49, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 42], []]
 b := ![[], [43, 25, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [7, 53, 18, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6474, -31789, -12118]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -383, -146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [39, 32, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 35, 38], [34, 53, 51], [0, 1]]
 g := ![![[63, 7, 72], [24, 36], [27, 57], [78, 78, 25], [12, 69, 1], []], ![[44, 37, 16, 15], [8, 16], [39, 68], [1, 2, 40, 60], [12, 87, 74, 31], [35, 20]], ![[68, 14, 5, 28], [60, 11], [61, 50], [49, 41, 63, 27], [67, 76, 33, 86], [22, 20]]]
 h' := ![![[35, 35, 38], [59, 2, 28], [4, 27, 83], [73, 64, 71], [66, 40, 5], [0, 0, 1], [0, 1]], ![[34, 53, 51], [36, 73, 47], [9, 48, 85], [27, 83, 54], [54, 56, 5], [38, 16, 53], [35, 35, 38]], ![[0, 1], [16, 14, 14], [24, 14, 10], [0, 31, 53], [68, 82, 79], [31, 73, 35], [34, 53, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 65], []]
 b := ![[], [48, 8, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [39, 32, 20, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78765, -27768, 158242]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![885, -312, 1778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![47, 36, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![47, 36, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![47, 36, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![47, 36, 1], ![36, 9, 73], ![-19, -1387, 45]]]
  hmulB := by decide  
  f := ![![![-46, -36, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -36, 97]], ![![0, 0, 1], ![-35, -27, 73], ![-22, -31, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [13, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 96], [0, 1]]
 g := ![![[28, 35], [24], [73], [93], [70], [24, 1]], ![[92, 62], [24], [73], [93], [70], [48, 96]]]
 h' := ![![[24, 96], [49, 61], [19, 86], [17, 48], [16, 53], [76, 78], [0, 1]], ![[0, 1], [58, 36], [46, 11], [5, 49], [27, 44], [8, 19], [24, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [23, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [13, 73, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83270, -77805, -161896]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77586, 59283, -161896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![24, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![24, 1, 0]] 
 ![![97, 0, 0], ![24, 1, 0], ![52, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![24, 1, 0], ![1, 24, 2], ![0, -38, 25]]]
  hmulB := by decide  
  f := ![![![-3704, -100420, -8370], ![-1940, 405945, 0]], ![![-939, -24836, -2070], ![-387, 100395, 0]], ![![-2000, -53834, -4487], ![-982, 217620, 0]]]
  g := ![![![1, 0, 0], ![-24, 97, 0], ![-52, 0, 97]], ![![0, 1, 0], ![-7, 24, 2], ![-4, -38, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![47, 36, 1]] ![![97, 0, 0], ![24, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![2328, 97, 0]], ![![4559, 3492, 97], ![1164, 873, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![24, 1, 0]]], ![![![47, 36, 1]], ![![12, 9, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![11, -39, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![11, -39, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![11, 62, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![11, -39, 1], ![-39, -27, -77], ![-19, 1463, -66]]]
  hmulB := by decide  
  f := ![![![-10, 39, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -62, 101]], ![![0, -1, 1], ![8, 47, -77], ![7, 55, -66]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [57, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 100], [0, 1]]
 g := ![![[12, 37], [68], [4, 16], [14], [79], [23, 1]], ![[55, 64], [68], [69, 85], [14], [79], [46, 100]]]
 h' := ![![[23, 100], [32, 80], [75, 13], [5, 4], [46, 69], [2, 68], [0, 1]], ![[0, 1], [54, 21], [71, 88], [97, 97], [17, 32], [51, 33], [23, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [39, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [57, 78, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-569, -21, -1328]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139, 815, -1328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-24, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-24, 1, 0]] 
 ![![101, 0, 0], ![77, 1, 0], ![66, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-24, 1, 0], ![1, -24, 2], ![0, -38, -23]]]
  hmulB := by decide  
  f := ![![![-164, 4535, -378], ![101, 19089, 0]], ![![-119, 3455, -288], ![102, 14544, 0]], ![![-96, 2963, -247], ![113, 12474, 0]]]
  g := ![![![1, 0, 0], ![-77, 101, 0], ![-66, 0, 101]], ![![-1, 1, 0], ![17, -24, 2], ![44, -38, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![11, -39, 1]] ![![101, 0, 0], ![-24, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2424, 101, 0]], ![![1111, -3939, 101], ![-303, 909, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-24, 1, 0]]], ![![![11, -39, 1]], ![![-3, 9, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![23, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![23, 1, 0]] 
 ![![103, 0, 0], ![23, 1, 0], ![45, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![23, 1, 0], ![1, 23, 2], ![0, -38, 24]]]
  hmulB := by decide  
  f := ![![![638, 16763, 1458], ![412, -75087, 0]], ![![139, 3725, 324], ![104, -16686, 0]], ![![287, 7324, 637], ![143, -32805, 0]]]
  g := ![![![1, 0, 0], ![-23, 103, 0], ![-45, 0, 103]], ![![0, 1, 0], ![-6, 23, 2], ![-2, -38, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![37, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![37, 1, 0]] 
 ![![103, 0, 0], ![37, 1, 0], ![37, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![37, 1, 0], ![1, 37, 2], ![0, -38, 38]]]
  hmulB := by decide  
  f := ![![![-1583, -75024, -4056], ![-1236, 208884, 0]], ![![-580, -26932, -1456], ![-411, 74984, 0]], ![![-592, -26951, -1457], ![-379, 75036, 0]]]
  g := ![![![1, 0, 0], ![-37, 103, 0], ![-37, 0, 103]], ![![0, 1, 0], ![-14, 37, 2], ![0, -38, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![42, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![42, 1, 0]] 
 ![![103, 0, 0], ![42, 1, 0], ![97, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![42, 1, 0], ![1, 42, 2], ![0, -38, 43]]]
  hmulB := by decide  
  f := ![![![1024, 62359, 2970], ![1133, -152955, 0]], ![![395, 25405, 1210], ![516, -62315, 0]], ![![988, 58727, 2797], ![1009, -144045, 0]]]
  g := ![![![1, 0, 0], ![-42, 103, 0], ![-97, 0, 103]], ![![0, 1, 0], ![-19, 42, 2], ![-25, -38, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![23, 1, 0]] ![![103, 0, 0], ![37, 1, 0]]
  ![![103, 0, 0], ![14, 30, 1]] where
 M := ![![![10609, 0, 0], ![3811, 103, 0]], ![![2369, 103, 0], ![852, 60, 2]]]
 hmul := by decide  
 g := ![![![![89, -30, -1], ![103, 0, 0]], ![![23, -29, -1], ![103, 0, 0]]], ![![![9, -29, -1], ![103, 0, 0]], ![![8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![14, 30, 1]] ![![103, 0, 0], ![42, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![4326, 103, 0]], ![![1442, 3090, 103], ![618, 1236, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![42, 1, 0]]], ![![![14, 30, 1]], ![![6, 12, 1]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [31, 2, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 31, 73], [63, 75, 34], [0, 1]]
 g := ![![[87, 10, 40], [44, 52, 69], [28, 61], [16], [63, 76], [1]], ![[53, 88, 27, 58], [48, 35, 70, 63], [87, 23], [27, 43, 41, 82], [102, 102], [85, 33, 36, 72]], ![[41, 54, 23, 86], [51, 6, 82, 11], [24, 12], [101, 46, 4, 25], [84, 34], [19, 80, 27, 35]]]
 h' := ![![[85, 31, 73], [27, 26, 88], [11, 58, 60], [39, 60, 32], [78, 103], [76, 105, 41], [0, 1]], ![[63, 75, 34], [63, 78, 45], [25, 76, 67], [49, 0, 39], [59, 90, 29], [92, 56, 40], [85, 31, 73]], ![[0, 1], [10, 3, 81], [61, 80, 87], [85, 47, 36], [40, 21, 78], [41, 53, 26], [63, 75, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6], []]
 b := ![[], [34, 84, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [31, 2, 66, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9951, -42586, -18832]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-93, -398, -176]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![8, 14, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![8, 14, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![8, 14, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![8, 14, 1], ![14, -30, 29], ![-19, -551, -16]]]
  hmulB := by decide  
  f := ![![![-7, -14, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -14, 109]], ![![0, 0, 1], ![-2, -4, 29], ![1, -3, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [28, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 108], [0, 1]]
 g := ![![[72, 74], [66], [107, 43], [12, 82], [82], [55, 1]], ![[0, 35], [66], [74, 66], [53, 27], [82], [1, 108]]]
 h' := ![![[55, 108], [89, 40], [56, 75], [100, 77], [80, 55], [95, 54], [0, 1]], ![[0, 1], [0, 69], [39, 34], [84, 32], [53, 54], [13, 55], [55, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [89, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [28, 54, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![330, -3401, 668]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46, -117, 668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-29, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-29, 1, 0]] 
 ![![109, 0, 0], ![80, 1, 0], ![16, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-29, 1, 0], ![1, -29, 2], ![0, -38, -28]]]
  hmulB := by decide  
  f := ![![![-738, 24791, -1710], ![436, 93195, 0]], ![![-539, 18180, -1254], ![328, 68343, 0]], ![![-107, 3639, -251], ![69, 13680, 0]]]
  g := ![![![1, 0, 0], ![-80, 109, 0], ![-16, 0, 109]], ![![-1, 1, 0], ![21, -29, 2], ![32, -38, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![8, 14, 1]] ![![109, 0, 0], ![-29, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3161, 109, 0]], ![![872, 1526, 109], ![-218, -436, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-29, 1, 0]]], ![![![8, 14, 1]], ![![-2, -4, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![41, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![41, 1, 0]] 
 ![![113, 0, 0], ![41, 1, 0], ![64, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![41, 1, 0], ![1, 41, 2], ![0, -38, 42]]]
  hmulB := by decide  
  f := ![![![-4949, -263430, -12852], ![-4068, 726138, 0]], ![![-1798, -95558, -4662], ![-1468, 263403, 0]], ![![-2832, -149200, -7279], ![-2224, 411264, 0]]]
  g := ![![![1, 0, 0], ![-41, 113, 0], ![-64, 0, 113]], ![![0, 1, 0], ![-16, 41, 2], ![-10, -38, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-21, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-21, 1, 0]] 
 ![![113, 0, 0], ![92, 1, 0], ![6, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-21, 1, 0], ![1, -21, 2], ![0, -38, -20]]]
  hmulB := by decide  
  f := ![![![-3316, 74937, -7138], ![1356, 403297, 0]], ![![-2694, 60995, -5810], ![1131, 328265, 0]], ![![-156, 3978, -379], ![180, 21414, 0]]]
  g := ![![![1, 0, 0], ![-92, 113, 0], ![-6, 0, 113]], ![![-1, 1, 0], ![17, -21, 2], ![32, -38, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![41, 1, 0]] ![![113, 0, 0], ![-21, 1, 0]]
  ![![113, 0, 0], ![22, 10, 1]] where
 M := ![![![12769, 0, 0], ![-2373, 113, 0]], ![![4633, 113, 0], ![-860, 20, 2]]]
 hmul := by decide  
 g := ![![![![91, -10, -1], ![113, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![19, -9, -1], ![113, 0, 0]], ![![-8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![22, 10, 1]] ![![113, 0, 0], ![-21, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2373, 113, 0]], ![![2486, 1130, 113], ![-452, -226, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-21, 1, 0]]], ![![![22, 10, 1]], ![![-4, -2, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![83, -59, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![83, -59, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![83, 68, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![83, -59, 1], ![-59, 45, -117], ![-19, 2223, -14]]]
  hmulB := by decide  
  f := ![![![-82, 59, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -68, 127]], ![![0, -1, 1], ![76, 63, -117], ![9, 25, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [4, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 126], [0, 1]]
 g := ![![[120, 32], [60, 16], [28, 81], [17, 8], [87, 70], [28, 1]], ![[0, 95], [0, 111], [10, 46], [114, 119], [15, 57], [56, 126]]]
 h' := ![![[28, 126], [14, 63], [15, 4], [59, 9], [33, 95], [15, 18], [0, 1]], ![[0, 1], [0, 64], [0, 123], [57, 118], [26, 32], [11, 109], [28, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [47, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [4, 99, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-352, 798, -627]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![407, 342, -627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-10, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-10, 1, 0]] 
 ![![127, 0, 0], ![117, 1, 0], ![14, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-10, 1, 0], ![1, -10, 2], ![0, -38, -9]]]
  hmulB := by decide  
  f := ![![![-1679, 17097, -3420], ![381, 217170, 0]], ![![-1554, 15748, -3150], ![255, 200025, 0]], ![![-178, 1884, -377], ![132, 23940, 0]]]
  g := ![![![1, 0, 0], ![-117, 127, 0], ![-14, 0, 127]], ![![-1, 1, 0], ![9, -10, 2], ![36, -38, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![83, -59, 1]] ![![127, 0, 0], ![-10, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1270, 127, 0]], ![![10541, -7493, 127], ![-889, 635, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-10, 1, 0]]], ![![![83, -59, 1]], ![![-7, 5, -1]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![5, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![5, 1, 0]] 
 ![![131, 0, 0], ![5, 1, 0], ![119, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![5, 1, 0], ![1, 5, 2], ![0, -38, 6]]]
  hmulB := by decide  
  f := ![![![-3979, -19948, -7980], ![-262, 522690, 0]], ![![-152, -760, -304], ![1, 19912, 0]], ![![-3616, -18121, -7249], ![-199, 474810, 0]]]
  g := ![![![1, 0, 0], ![-5, 131, 0], ![-119, 0, 131]], ![![0, 1, 0], ![-2, 5, 2], ![-4, -38, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![61, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![61, 1, 0]] 
 ![![131, 0, 0], ![61, 1, 0], ![105, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![61, 1, 0], ![1, 61, 2], ![0, -38, 62]]]
  hmulB := by decide  
  f := ![![![1638, 155657, 5104], ![1965, -334312, 0]], ![![761, 72461, 2376], ![918, -155628, 0]], ![![1298, 124763, 4091], ![1607, -267960, 0]]]
  g := ![![![1, 0, 0], ![-61, 131, 0], ![-105, 0, 131]], ![![0, 1, 0], ![-30, 61, 2], ![-32, -38, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![64, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![64, 1, 0]] 
 ![![131, 0, 0], ![64, 1, 0], ![114, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![64, 1, 0], ![1, 64, 2], ![0, -38, 65]]]
  hmulB := by decide  
  f := ![![![628, 68793, 2150], ![917, -140825, 0]], ![![269, 33596, 1050], ![525, -68775, 0]], ![![568, 59866, 1871], ![754, -122550, 0]]]
  g := ![![![1, 0, 0], ![-64, 131, 0], ![-114, 0, 131]], ![![0, 1, 0], ![-33, 64, 2], ![-38, -38, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![5, 1, 0]] ![![131, 0, 0], ![61, 1, 0]]
  ![![131, 0, 0], ![22, 33, 1]] where
 M := ![![![17161, 0, 0], ![7991, 131, 0]], ![![655, 131, 0], ![306, 66, 2]]]
 hmul := by decide  
 g := ![![![![109, -33, -1], ![131, 0, 0]], ![![39, -32, -1], ![131, 0, 0]]], ![![![-17, -32, -1], ![131, 0, 0]], ![![2, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![22, 33, 1]] ![![131, 0, 0], ![64, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![8384, 131, 0]], ![![2882, 4323, 131], ![1441, 2096, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![64, 1, 0]]], ![![![22, 33, 1]], ![![11, 16, 1]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![19, 18, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![19, 18, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![19, 18, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![19, 18, 1], ![18, -19, 37], ![-19, -703, -1]]]
  hmulB := by decide  
  f := ![![![-18, -18, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -18, 137]], ![![0, 0, 1], ![-5, -5, 37], ![0, -5, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [109, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 136], [0, 1]]
 g := ![![[86, 44], [15], [59], [51, 99], [119], [76], [1]], ![[0, 93], [15], [59], [63, 38], [119], [76], [1]]]
 h' := ![![[79, 136], [78, 110], [84, 120], [58, 14], [36, 109], [35, 16], [28, 79], [0, 1]], ![[0, 1], [0, 27], [111, 17], [68, 123], [16, 28], [66, 121], [104, 58], [79, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [109, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [109, 58, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74, -546, -350]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 42, -350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-37, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-37, 1, 0]] 
 ![![137, 0, 0], ![100, 1, 0], ![1, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-37, 1, 0], ![1, -37, 2], ![0, -38, -36]]]
  hmulB := by decide  
  f := ![![![-1590, 68443, -3700], ![959, 253450, 0]], ![![-1164, 49945, -2700], ![686, 184950, 0]], ![![10, 499, -27], ![87, 1850, 0]]]
  g := ![![![1, 0, 0], ![-100, 137, 0], ![-1, 0, 137]], ![![-1, 1, 0], ![27, -37, 2], ![28, -38, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![19, 18, 1]] ![![137, 0, 0], ![-37, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-5069, 137, 0]], ![![2603, 2466, 137], ![-685, -685, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-37, 1, 0]]], ![![![19, 18, 1]], ![![-5, -5, 0]]]]
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


lemma PB184I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB184I2 : PrimesBelowBoundCertificateInterval O 79 137 184 where
  m := 11
  g := ![1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB184I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![571787]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
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
      exact NI113N1
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I97N1, I101N1, I103N0, I103N1, I103N2, I109N1, I113N0, I113N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[], [], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [], [I109N1], [I113N0, I113N1, I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
