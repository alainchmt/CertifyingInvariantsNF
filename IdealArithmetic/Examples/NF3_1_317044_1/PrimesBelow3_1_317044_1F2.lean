
import IdealArithmetic.Examples.NF3_1_317044_1.RI3_1_317044_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [73, 60, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 2, 31], [53, 80, 52], [0, 1]]
 g := ![![[72, 6, 61], [60, 62, 36], [11, 3], [28, 78], [35, 26, 1], []], ![[66, 42, 25, 65], [71, 72, 33, 59], [55, 61], [30, 64], [31, 1, 10, 30], [44, 48]], ![[75, 68, 3, 72], [27, 59, 41, 80], [82, 44], [14, 7], [51, 30, 56, 42], [23, 48]]]
 h' := ![![[56, 2, 31], [19, 52, 71], [58, 24, 6], [23, 7, 13], [18, 69, 24], [0, 0, 1], [0, 1]], ![[53, 80, 52], [25, 13, 71], [33, 52, 62], [8, 78, 12], [66, 71, 75], [7, 56, 80], [56, 2, 31]], ![[0, 1], [5, 18, 24], [59, 7, 15], [61, 81, 58], [2, 26, 67], [51, 27, 2], [53, 80, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 12], []]
 b := ![[], [50, 63, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [73, 60, 57, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1266829, -697698, -348766]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15263, -8406, -4202]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-24, 8, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-24, 8, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![65, 8, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-24, 8, 1], ![-70, -36, 40], ![-546, -174, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -8, 89]], ![![-1, 0, 1], ![-30, -4, 40], ![26, 2, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [53, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 88], [0, 1]]
 g := ![![[12, 42], [1], [2], [68, 87], [71, 80], [1]], ![[0, 47], [1], [2], [5, 2], [10, 9], [1]]]
 h' := ![![[76, 88], [44, 65], [50, 88], [45, 25], [64, 49], [36, 76], [0, 1]], ![[0, 1], [0, 24], [63, 1], [76, 64], [50, 40], [27, 13], [76, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [21, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [53, 13, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-253, -954, -898]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![653, 70, -898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-40, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-40, 1, 0]] 
 ![![89, 0, 0], ![49, 1, 0], ![44, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-40, 1, 0], ![0, -39, 5], ![-70, -20, -40]]]
  hmulB := by decide  
  f := ![![![2921, -73, 0], ![6497, 0, 0]], ![![1601, -40, 0], ![3561, 0, 0]], ![![1436, -28, -1], ![3194, 18, 0]]]
  g := ![![![1, 0, 0], ![-49, 89, 0], ![-44, 0, 89]], ![![-1, 1, 0], ![19, -39, 5], ![30, -20, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-24, 8, 1]] ![![89, 0, 0], ![-40, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3560, 89, 0]], ![![-2136, 712, 89], ![890, -356, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-40, 1, 0]]], ![![![-24, 8, 1]], ![![10, -4, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [11, 85, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 51, 54], [43, 45, 43], [0, 1]]
 g := ![![[53, 0, 95], [44, 33], [58, 89], [85, 4], [18, 18], [1]], ![[1, 42, 1, 11], [45, 66], [92, 95], [59, 47], [88, 62], [9, 43, 73, 33]], ![[48, 75, 75, 1], [50, 53], [72, 79], [93, 3], [39, 66], [13, 52, 6, 64]]]
 h' := ![![[96, 51, 54], [71, 31, 17], [19, 22, 18], [47, 60, 34], [20, 45, 95], [86, 12, 42], [0, 1]], ![[43, 45, 43], [25, 65, 14], [61, 76, 58], [54, 28, 17], [11, 94, 12], [94, 79, 16], [96, 51, 54]], ![[0, 1], [96, 1, 66], [8, 96, 21], [11, 9, 46], [89, 55, 87], [18, 6, 39], [43, 45, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 36], []]
 b := ![[], [49, 49, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [11, 85, 55, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44911, 1358, -3007]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-463, 14, -31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [70, 49, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 40, 72], [15, 60, 29], [0, 1]]
 g := ![![[17, 33, 68], [46, 37], [22, 50, 31], [48, 9], [62, 56], [1]], ![[83, 78, 68, 89], [11, 4], [86, 20, 31, 63], [27, 64], [19, 25], [71, 72, 63, 53]], ![[86, 86, 83, 90], [35, 24], [5, 20, 28, 83], [0, 25], [52, 47], [64, 6, 40, 48]]]
 h' := ![![[22, 40, 72], [31, 45, 88], [76, 82, 80], [69, 75, 58], [55, 3, 3], [31, 52, 37], [0, 1]], ![[15, 60, 29], [94, 30, 36], [64, 9, 99], [59, 20, 93], [63, 39, 93], [22, 71, 5], [22, 40, 72]], ![[0, 1], [58, 26, 78], [65, 10, 23], [14, 6, 51], [32, 59, 5], [6, 79, 59], [15, 60, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 61], []]
 b := ![[], [69, 95, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [70, 49, 64, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2037978, -1195638, -649834]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20178, -11838, -6434]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [67, 66, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 13, 54], [93, 89, 49], [0, 1]]
 g := ![![[56, 53, 79], [11, 1, 68], [22, 98, 8], [16, 9], [44, 32], [1]], ![[42, 99, 34, 73], [90, 40, 87, 96], [52, 87, 50, 80], [24, 46], [71, 8], [22, 10, 18, 80]], ![[54, 45, 35, 76], [31, 56, 52, 52], [83, 2, 7, 83], [0, 28], [73, 72], [48, 45, 92, 23]]]
 h' := ![![[59, 13, 54], [87, 25, 39], [71, 74, 45], [77, 6, 27], [99, 88, 100], [36, 37, 49], [0, 1]], ![[93, 89, 49], [77, 4, 83], [101, 37, 70], [13, 38, 49], [73, 4, 56], [68, 46, 76], [59, 13, 54]], ![[0, 1], [100, 74, 84], [94, 95, 91], [1, 59, 27], [102, 11, 50], [7, 20, 81], [93, 89, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 83], []]
 b := ![[], [22, 37, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [67, 66, 54, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1262677, -692160, -344020]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12259, -6720, -3340]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![27, 51, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![27, 51, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![27, 51, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![27, 51, 1], ![-70, 58, 255], ![-3556, -1034, 7]]]
  hmulB := by decide  
  f := ![![![-26, -51, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -51, 107]], ![![0, 0, 1], ![-65, -121, 255], ![-35, -13, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [91, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 106], [0, 1]]
 g := ![![[80, 4], [55, 69], [79], [21, 69], [61], [103, 1]], ![[64, 103], [100, 38], [79], [66, 38], [61], [99, 106]]]
 h' := ![![[103, 106], [24, 2], [98, 47], [15, 87], [43, 47], [43, 32], [0, 1]], ![[0, 1], [16, 105], [17, 60], [95, 20], [69, 60], [22, 75], [103, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [16, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [91, 4, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134850, -156134, -128734]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31224, 59900, -128734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-41, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-41, 1, 0]] 
 ![![107, 0, 0], ![66, 1, 0], ![100, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-41, 1, 0], ![0, -40, 5], ![-70, -20, -41]]]
  hmulB := by decide  
  f := ![![![3486, -85, 0], ![9095, 0, 0]], ![![2174, -53, 0], ![5672, 0, 0]], ![![3202, -62, -2], ![8354, 43, 0]]]
  g := ![![![1, 0, 0], ![-66, 107, 0], ![-100, 0, 107]], ![![-1, 1, 0], ![20, -40, 5], ![50, -20, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![27, 51, 1]] ![![107, 0, 0], ![-41, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4387, 107, 0]], ![![2889, 5457, 107], ![-1177, -2033, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-41, 1, 0]]], ![![![27, 51, 1]], ![![-11, -19, 2]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2685, -74, 119]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![2685, -74, 119]] 
 ![![109, 0, 0], ![0, 109, 0], ![105, 58, 1]] where
  M :=![![![2685, -74, 119], ![-8330, 231, -370], ![6846, -186, 305]]]
  hmulB := by decide  
  f := ![![![15, 4, -1]], ![![70, 39, 20]], ![![49, 24, 10]]]
  g := ![![![-90, -64, 119], ![280, 199, -370], ![-231, -164, 305]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [1, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 108], [0, 1]]
 g := ![![[38, 1], [3], [40, 75], [3, 102], [22], [71, 1]], ![[0, 108], [3], [24, 34], [51, 7], [22], [33, 108]]]
 h' := ![![[71, 108], [71, 108], [69, 49], [106, 27], [5, 50], [38, 26], [0, 1]], ![[0, 1], [0, 1], [60, 60], [61, 82], [67, 59], [31, 83], [71, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [41, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [1, 38, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1310, -1170, -708]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![670, 366, -708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -4, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-15, -4, 1]] 
 ![![109, 0, 0], ![37, 1, 0], ![24, 0, 1]] where
  M :=![![![-15, -4, 1], ![-70, -39, -20], ![294, 66, -35]]]
  hmulB := by decide  
  f := ![![![-2685, 74, -119]], ![![-835, 23, -37]], ![![-654, 18, -29]]]
  g := ![![![1, -4, 1], ![17, -39, -20], ![-12, 66, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![2685, -74, 119]] ![![-15, -4, 1]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![26, -44, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![26, -44, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![26, 69, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![26, -44, 1], ![-70, -38, -220], ![3094, 866, 6]]]
  hmulB := by decide  
  f := ![![![-25, 44, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -69, 113]], ![![0, -1, 1], ![50, 134, -220], ![26, 4, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [108, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 112], [0, 1]]
 g := ![![[49, 72], [52], [95], [41], [110, 51], [19, 1]], ![[61, 41], [52], [95], [41], [62, 62], [38, 112]]]
 h' := ![![[19, 112], [8, 80], [55, 39], [91, 35], [98, 70], [95, 27], [0, 1]], ![[0, 1], [59, 33], [5, 74], [78, 78], [72, 43], [43, 86], [19, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [100, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [108, 94, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3028, -4133, -2559]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![562, 1526, -2559]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-6, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-6, 1, 0]] 
 ![![113, 0, 0], ![107, 1, 0], ![107, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-6, 1, 0], ![0, -5, 5], ![-70, -20, -6]]]
  hmulB := by decide  
  f := ![![![151, -25, 0], ![2825, 0, 0]], ![![145, -24, 0], ![2713, 0, 0]], ![![145, -21, -3], ![2713, 68, 0]]]
  g := ![![![1, 0, 0], ![-107, 113, 0], ![-107, 0, 113]], ![![-1, 1, 0], ![0, -5, 5], ![24, -20, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![26, -44, 1]] ![![113, 0, 0], ![-6, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-678, 113, 0]], ![![2938, -4972, 113], ![-226, 226, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-6, 1, 0]]], ![![![26, -44, 1]], ![![-2, 2, -2]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-29, 18, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-29, 18, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![98, 18, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-29, 18, 1], ![-70, -31, 90], ![-1246, -374, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, -18, 127]], ![![-1, 0, 1], ![-70, -13, 90], ![28, 4, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [81, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 126], [0, 1]]
 g := ![![[87, 69], [75, 19], [31, 35], [18, 18], [66, 50], [65, 1]], ![[0, 58], [40, 108], [20, 92], [45, 109], [14, 77], [3, 126]]]
 h' := ![![[65, 126], [21, 113], [29, 107], [66, 110], [115, 48], [69, 80], [0, 1]], ![[0, 1], [0, 14], [126, 20], [104, 17], [60, 79], [62, 47], [65, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [37, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [81, 62, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20791, -22664, -19660]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15007, 2608, -19660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![37, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![37, 1, 0]] 
 ![![127, 0, 0], ![37, 1, 0], ![49, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![37, 1, 0], ![0, 38, 5], ![-70, -20, 37]]]
  hmulB := by decide  
  f := ![![![1814, 49, 0], ![-6223, 0, 0]], ![![518, 14, 0], ![-1777, 0, 0]], ![![676, 3, -2], ![-2319, 51, 0]]]
  g := ![![![1, 0, 0], ![-37, 127, 0], ![-49, 0, 127]], ![![0, 1, 0], ![-13, 38, 5], ![-9, -20, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-29, 18, 1]] ![![127, 0, 0], ![37, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![4699, 127, 0]], ![![-3683, 2286, 127], ![-1143, 635, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![37, 1, 0]]], ![![![-29, 18, 1]], ![![-9, 5, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [119, 115, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 46, 39], [20, 84, 92], [0, 1]]
 g := ![![[31, 85, 108], [40, 14, 36], [77, 60], [39, 75], [99, 27], [130, 1], []], ![[98, 2, 8, 25], [120, 22, 84, 16], [86, 117], [118, 55], [54, 3], [72, 113], [102, 80]], ![[6, 120, 39, 19], [97, 76, 85, 10], [57, 11], [74, 15], [86, 48], [44, 20], [49, 80]]]
 h' := ![![[110, 46, 39], [87, 80, 97], [53, 26, 6], [35, 96, 86], [22, 39, 72], [119, 127, 17], [0, 0, 1], [0, 1]], ![[20, 84, 92], [92, 104, 2], [65, 47, 77], [122, 130, 95], [4, 58, 102], [81, 32, 93], [93, 5, 84], [110, 46, 39]], ![[0, 1], [59, 78, 32], [82, 58, 48], [70, 36, 81], [19, 34, 88], [67, 103, 21], [71, 126, 46], [20, 84, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 114], []]
 b := ![[], [60, 52, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [119, 115, 1, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5240, 0, 262]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 0, 2]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![58, 47, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![58, 47, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![58, 47, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![58, 47, 1], ![-70, 85, 235], ![-3276, -954, 38]]]
  hmulB := by decide  
  f := ![![![-57, -47, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -47, 137]], ![![0, 0, 1], ![-100, -80, 235], ![-40, -20, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [27, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 136], [0, 1]]
 g := ![![[38, 19], [44], [17], [117, 129], [64], [105], [1]], ![[135, 118], [44], [17], [105, 8], [64], [105], [1]]]
 h' := ![![[70, 136], [27, 108], [16, 27], [129, 47], [51, 102], [86, 8], [110, 70], [0, 1]], ![[0, 1], [52, 29], [125, 110], [131, 90], [67, 35], [98, 129], [78, 67], [70, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [68, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [27, 67, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8431, -10694, -10144]
  a := ![1, -5, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4233, 3402, -10144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![39, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![39, 1, 0]] 
 ![![137, 0, 0], ![39, 1, 0], ![99, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![39, 1, 0], ![0, 40, 5], ![-70, -20, 39]]]
  hmulB := by decide  
  f := ![![![4525, 116, 0], ![-15892, 0, 0]], ![![1287, 33, 0], ![-4520, 0, 0]], ![![3279, 68, -2], ![-11516, 55, 0]]]
  g := ![![![1, 0, 0], ![-39, 137, 0], ![-99, 0, 137]], ![![0, 1, 0], ![-15, 40, 5], ![-23, -20, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![58, 47, 1]] ![![137, 0, 0], ![39, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![5343, 137, 0]], ![![7946, 6439, 137], ![2192, 1918, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![39, 1, 0]]], ![![![58, 47, 1]], ![![16, 14, 2]]]]
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


lemma PB160I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB160I2 : PrimesBelowBoundCertificateInterval O 79 137 160 where
  m := 11
  g := ![1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB160I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I107N1, I109N1, I113N1, I127N1, I137N1]
  Il := ![[], [I89N1], [], [], [], [I107N1], [I109N1], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
