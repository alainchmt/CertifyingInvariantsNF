
import IdealArithmetic.Examples.NF3_3_405405_1.RI3_3_405405_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [45, 70, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 30, 12], [5, 52, 71], [0, 1]]
 g := ![![[17, 73, 65], [47, 34, 37], [24, 26], [47, 49], [16, 70, 1], []], ![[78, 35, 55, 78], [4, 4, 10, 16], [58, 30], [27, 69], [72, 56, 48, 78], [10, 61]], ![[1, 3, 11, 53], [17, 6, 35, 52], [62, 49], [81, 59], [30, 67, 34, 73], [34, 61]]]
 h' := ![![[65, 30, 12], [43, 17, 27], [43, 67, 28], [25, 60, 21], [27, 46, 76], [0, 0, 1], [0, 1]], ![[5, 52, 71], [70, 13, 31], [40, 59, 19], [34, 67, 69], [81, 21, 22], [40, 40, 52], [65, 30, 12]], ![[0, 1], [80, 53, 25], [70, 40, 36], [11, 39, 76], [2, 16, 68], [72, 43, 30], [5, 52, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 57], []]
 b := ![[], [59, 63, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [45, 70, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5727, -8964, -1992]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69, -108, -24]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [81, 78, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 80, 5], [60, 8, 84], [0, 1]]
 g := ![![[17, 38, 42], [72, 32], [70, 53], [67, 49, 36], [68, 18, 1], []], ![[44, 39, 83, 42], [2, 39], [77, 88], [57, 3, 39, 88], [34, 67, 11, 53], [4, 25]], ![[38, 77, 26, 9], [41, 21], [57, 40], [36, 55, 13, 79], [22, 79, 12, 40], [14, 25]]]
 h' := ![![[47, 80, 5], [52, 78, 65], [30, 58, 11], [2, 72, 26], [10, 2, 6], [0, 0, 1], [0, 1]], ![[60, 8, 84], [41, 40, 20], [84, 65, 22], [64, 76, 34], [22, 19, 58], [16, 21, 8], [47, 80, 5]], ![[0, 1], [16, 60, 4], [20, 55, 56], [86, 30, 29], [63, 68, 25], [63, 68, 80], [60, 8, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 87], []]
 b := ![[], [31, 64, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [81, 78, 71, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-89356, -43966, 91403]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1004, -494, 1027]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-42, 43, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-42, 43, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![55, 43, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-42, 43, 1], ![37, 6, 43], ![1591, 2101, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -43, 97]], ![![-1, 0, 1], ![-24, -19, 43], ![13, 19, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [11, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 96], [0, 1]]
 g := ![![[59, 53], [94], [88], [27], [62], [30, 1]], ![[0, 44], [94], [88], [27], [62], [60, 96]]]
 h' := ![![[30, 96], [49, 21], [4, 26], [83, 31], [63, 30], [58, 16], [0, 1]], ![[0, 1], [0, 76], [8, 71], [43, 66], [90, 67], [53, 81], [30, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [61, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [11, 67, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-255, -120, 110]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65, -50, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-43, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-43, 1, 0]] 
 ![![97, 0, 0], ![54, 1, 0], ![91, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-43, 1, 0], ![0, -43, 1], ![37, 48, -43]]]
  hmulB := by decide  
  f := ![![![4129, -96, 0], ![9312, 0, 0]], ![![2280, -53, 0], ![5142, 0, 0]], ![![3847, -89, 0], ![8676, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 97, 0], ![-91, 0, 97]], ![![-1, 1, 0], ![23, -43, 1], ![14, 48, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-42, 43, 1]] ![![97, 0, 0], ![-43, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4171, 97, 0]], ![![-4074, 4171, 97], ![1843, -1843, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-43, 1, 0]]], ![![![-42, 43, 1]], ![![19, -19, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [58, 46, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 24, 90], [46, 76, 11], [0, 1]]
 g := ![![[98, 25, 17], [35, 79], [41, 21, 20], [14, 25], [35, 21], [1]], ![[2, 46, 28, 53], [18, 33], [40, 26, 22, 55], [68, 81], [77, 5], [70, 26, 5, 83]], ![[83, 97, 32, 40], [12, 6], [10, 57, 12, 86], [28, 16], [24, 22], [63, 76, 36, 18]]]
 h' := ![![[73, 24, 90], [86, 25, 57], [46, 5, 33], [33, 20, 90], [21, 84, 96], [43, 55, 18], [0, 1]], ![[46, 76, 11], [47, 14, 17], [92, 4, 29], [17, 81, 55], [74, 35, 9], [46, 8, 56], [73, 24, 90]], ![[0, 1], [63, 62, 27], [70, 92, 39], [79, 0, 57], [17, 83, 97], [55, 38, 27], [46, 76, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 1], []]
 b := ![[], [34, 81, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [58, 46, 83, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7878, -29896, -25048]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -296, -248]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [42, 85, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 46], [9, 56], [0, 1]]
 g := ![![[54, 42, 76], [100, 27, 13], [70, 1, 81], [47, 68], [80, 49], [1]], ![[68, 102, 33], [98, 86, 7], [83, 77, 4], [14, 38], [85, 91], [1]], ![[99, 62, 97], [57, 93, 83], [48, 25, 18], [41, 100], [6, 66], [1]]]
 h' := ![![[101, 46], [23, 94, 73], [47, 63, 42], [9, 83, 9], [52, 33, 45], [61, 18, 7], [0, 1]], ![[9, 56], [24, 59, 71], [89, 11, 86], [85, 102, 92], [63, 36, 48], [53, 55, 83], [101, 46]], ![[0, 1], [87, 53, 62], [102, 29, 78], [43, 21, 2], [80, 34, 10], [69, 30, 13], [9, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92], []]
 b := ![[], [26, 66, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [42, 85, 96, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![412, 2060, 2060]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 20, 20]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [105, 75, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 9, 83], [88, 97, 24], [0, 1]]
 g := ![![[59, 18, 83], [61, 73, 42], [82, 47], [28, 46, 9], [46, 64], [1]], ![[29, 101, 36, 34], [17, 98, 34, 75], [74, 3], [104, 56, 4, 79], [98, 83], [25, 57, 98, 86]], ![[24, 11, 20, 68], [42, 67, 0, 63], [77, 102], [19, 55, 13, 74], [65, 27], [68, 27, 100, 21]]]
 h' := ![![[11, 9, 83], [15, 33, 46], [90, 24, 91], [56, 39, 58], [96, 16, 104], [2, 32, 99], [0, 1]], ![[88, 97, 24], [10, 88, 32], [54, 84, 12], [21, 27, 89], [82, 39, 74], [97, 8, 61], [11, 9, 83]], ![[0, 1], [80, 93, 29], [26, 106, 4], [34, 41, 67], [26, 52, 36], [18, 67, 54], [88, 97, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 3], []]
 b := ![[], [75, 94, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [105, 75, 8, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![372039, 526440, 60990]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3477, 4920, 570]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, -66, -9]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-46, -66, -9]] 
 ![![109, 0, 0], ![31, 1, 0], ![20, 0, 1]] where
  M :=![![![-46, -66, -9], ![-333, -478, -66], ![-2442, -3501, -478]]]
  hmulB := by decide  
  f := ![![![2582, 39, -54]], ![![716, 11, -15]], ![![487, 6, -10]]]
  g := ![![![20, -66, -9], ![145, -478, -66], ![1061, -3501, -478]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-381, -6, 8]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-381, -6, 8]] 
 ![![109, 0, 0], ![84, 1, 0], ![29, 0, 1]] where
  M :=![![![-381, -6, 8], ![296, 3, -6], ![-222, 8, 3]]]
  hmulB := by decide  
  f := ![![![-57, -82, -12]], ![![-48, -69, -10]], ![![-43, -62, -9]]]
  g := ![![![-1, -6, 8], ![2, 3, -6], ![-9, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![109, 0, 0], ![103, 1, 0], ![73, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![37, 48, -6]]]
  hmulB := by decide  
  f := ![![![-12, 6, 1]], ![![-11, 6, 1]], ![![-6, 7, 1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![-41, 48, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-46, -66, -9]] ![![-381, -6, 8]]
  ![![-12, 6, 1]] where
 M := ![![![-12, 6, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-12, 6, 1]] ![![-6, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-20, 49, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-20, 49, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![93, 49, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-20, 49, 1], ![37, 28, 49], ![1813, 2389, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -49, 113]], ![![-1, 0, 1], ![-40, -21, 49], ![-7, 9, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [95, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 112], [0, 1]]
 g := ![![[57, 69], [81], [82], [95], [53, 83], [9, 1]], ![[0, 44], [81], [82], [95], [9, 30], [18, 112]]]
 h' := ![![[9, 112], [74, 42], [57, 104], [29, 67], [50, 78], [49, 99], [0, 1]], ![[0, 1], [0, 71], [89, 9], [67, 46], [74, 35], [36, 14], [9, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [20, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [95, 104, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-230, 55, -45]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, 20, -45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-49, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-49, 1, 0]] 
 ![![113, 0, 0], ![64, 1, 0], ![85, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-49, 1, 0], ![0, -49, 1], ![37, 48, -49]]]
  hmulB := by decide  
  f := ![![![2353, -48, 0], ![5424, 0, 0]], ![![1324, -27, 0], ![3052, 0, 0]], ![![1737, -35, 0], ![4004, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 113, 0], ![-85, 0, 113]], ![![-1, 1, 0], ![27, -49, 1], ![10, 48, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-20, 49, 1]] ![![113, 0, 0], ![-49, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5537, 113, 0]], ![![-2260, 5537, 113], ![1017, -2373, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-49, 1, 0]]], ![![![-20, 49, 1]], ![![9, -21, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [52, 56, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 49, 46], [36, 77, 81], [0, 1]]
 g := ![![[124, 11, 100], [80, 43, 121], [25, 103, 124], [62, 20, 121], [75, 10, 34], [1]], ![[33, 59, 23, 59], [76, 54, 26, 43], [73, 99, 5, 95], [18, 75, 22, 92], [105, 76, 3, 92], [51, 126, 110, 54]], ![[19, 15, 11, 38], [27, 96, 89, 15], [53, 14, 51, 73], [32, 27, 3, 120], [102, 27, 8, 73], [56, 55, 19, 73]]]
 h' := ![![[29, 49, 46], [31, 26, 117], [97, 90, 116], [78, 32, 88], [37, 16, 116], [75, 71, 65], [0, 1]], ![[36, 77, 81], [104, 73, 45], [91, 79, 118], [90, 21, 120], [44, 9, 16], [20, 46, 16], [29, 49, 46]], ![[0, 1], [15, 28, 92], [80, 85, 20], [108, 74, 46], [23, 102, 122], [56, 10, 46], [36, 77, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 9], []]
 b := ![[], [51, 113, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [52, 56, 62, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41529, 77470, 31242]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![327, 610, 246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [41, 80, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 100, 104], [128, 30, 27], [0, 1]]
 g := ![![[59, 43, 91], [8, 58, 77], [120, 53], [4, 123], [39, 60], [67, 1], []], ![[67, 5, 22, 115], [63, 113, 85, 116], [25, 84], [96, 77], [16, 125], [42, 114], [82, 74]], ![[95, 82, 25, 5], [21, 118, 32, 89], [33, 62], [47, 74], [44, 53], [103, 44], [28, 74]]]
 h' := ![![[70, 100, 104], [65, 84, 109], [73, 11, 48], [88, 61, 61], [120, 75, 56], [4, 101, 86], [0, 0, 1], [0, 1]], ![[128, 30, 27], [12, 24, 85], [128, 106, 95], [57, 28, 52], [60, 96, 48], [89, 77, 115], [97, 83, 30], [70, 100, 104]], ![[0, 1], [112, 23, 68], [126, 14, 119], [118, 42, 18], [39, 91, 27], [128, 84, 61], [40, 48, 100], [128, 30, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 43], []]
 b := ![[], [99, 129, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [41, 80, 64, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-342303, -401384, 63928]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2613, -3064, 488]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [34, 27, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 11, 83], [115, 125, 54], [0, 1]]
 g := ![![[80, 9, 14], [17, 136], [27, 34], [48, 15, 93], [77, 118], [135, 1], []], ![[55, 128, 134, 108], [50, 87], [28, 126], [44, 13, 109, 35], [118, 50], [3, 7], [104, 39]], ![[11, 36, 111, 104], [17, 122], [81, 105], [72, 67, 100, 57], [70, 25], [59, 121], [133, 39]]]
 h' := ![![[20, 11, 83], [82, 61, 98], [48, 65, 37], [12, 47, 87], [88, 54, 97], [68, 20, 114], [0, 0, 1], [0, 1]], ![[115, 125, 54], [32, 65, 51], [122, 78, 19], [65, 130, 117], [20, 120, 30], [123, 105, 18], [15, 5, 125], [20, 11, 83]], ![[0, 1], [42, 11, 125], [49, 131, 81], [36, 97, 70], [130, 100, 10], [27, 12, 5], [72, 132, 11], [115, 125, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 18], []]
 b := ![[], [71, 94, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [34, 27, 2, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4110, -6302, 4932]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -46, 36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB142I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB142I2 : PrimesBelowBoundCertificateInterval O 79 137 142 where
  m := 11
  g := ![1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB142I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0]
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
    · exact ![1030301]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![2571353]
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
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I97N1, I109N0, I109N1, I109N2, I113N1]
  Il := ![[], [], [I97N1], [], [], [], [I109N0, I109N1, I109N2], [I113N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
