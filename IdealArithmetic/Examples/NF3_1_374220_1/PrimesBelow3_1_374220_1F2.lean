
import IdealArithmetic.Examples.NF3_1_374220_1.RI3_1_374220_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [56, 0, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 38, 10], [69, 44, 73], [0, 1]]
 g := ![![[8, 3, 10], [16, 62, 68], [9, 21], [32, 41], [51, 36, 1], []], ![[58, 40, 21, 40], [78, 11, 17, 75], [68, 69], [61, 31], [26, 57, 11, 21], [44, 17]], ![[2, 80, 64, 34], [45, 33, 2, 53], [52, 29], [65, 30], [7, 61, 36, 2], [64, 17]]]
 h' := ![![[50, 38, 10], [17, 62, 50], [31, 69, 20], [28, 0, 42], [49, 59, 37], [0, 0, 1], [0, 1]], ![[69, 44, 73], [20, 4, 81], [51, 71, 76], [46, 13, 22], [15, 50, 60], [36, 26, 44], [50, 38, 10]], ![[0, 1], [65, 17, 35], [29, 26, 70], [77, 70, 19], [27, 57, 69], [15, 57, 38], [69, 44, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 29], []]
 b := ![[], [23, 75, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [56, 0, 47, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3818, 6474, -1411]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 78, -17]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [45, 8, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 85, 16], [78, 3, 73], [0, 1]]
 g := ![![[22, 83, 44], [62, 18], [40, 40], [74, 9, 22], [31, 67, 1], []], ![[61, 57, 86, 22], [81, 42], [35, 36], [67, 78, 78, 2], [64, 3, 11, 55], [25, 78]], ![[16, 75, 11, 25], [20, 20], [73, 84], [43, 55, 70, 20], [51, 48, 88, 11], [57, 78]]]
 h' := ![![[78, 85, 16], [76, 16, 69], [14, 79, 75], [52, 22, 29], [29, 30, 72], [0, 0, 1], [0, 1]], ![[78, 3, 73], [44, 19, 18], [29, 18, 65], [64, 72, 83], [35, 44, 73], [64, 27, 3], [78, 85, 16]], ![[0, 1], [8, 54, 2], [75, 81, 38], [45, 84, 66], [40, 15, 33], [48, 62, 85], [78, 3, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 86], []]
 b := ![[], [10, 88, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [45, 8, 22, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![434854, -100392, -1157]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4886, -1128, -13]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [29, 22, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 80, 5], [74, 16, 92], [0, 1]]
 g := ![![[28, 18, 44], [89, 36], [1, 47], [], [44, 86], [1]], ![[44, 11, 4, 15], [63, 48], [57, 4], [49, 88], [70, 72], [23, 82, 80, 28]], ![[47, 28, 74, 28], [58, 79], [93, 2], [26, 88], [14, 79], [35, 25, 39, 69]]]
 h' := ![![[61, 80, 5], [65, 95, 74], [67, 47, 6], [75, 38, 85], [50, 45], [68, 75, 38], [0, 1]], ![[74, 16, 92], [60, 87, 10], [23, 18, 40], [67, 48, 95], [79, 11, 31], [13, 84, 13], [61, 80, 5]], ![[0, 1], [95, 12, 13], [15, 32, 51], [53, 11, 14], [82, 41, 66], [10, 35, 46], [74, 16, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 96], []]
 b := ![[], [23, 6, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [29, 22, 59, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10573, -10476, -2425]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-109, -108, -25]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 5, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![43, 5, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![43, 5, 1]] where
  M :=![![![43, 5, 1], ![114, 25, 5], ![570, 24, 25]]]
  hmulB := by decide  
  f := ![![![5, -1, 0]], ![![0, 5, -1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-1, 0, 5], ![-5, -1, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [35, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 100], [0, 1]]
 g := ![![[67, 100], [6], [7, 97], [25], [5], [79, 1]], ![[89, 1], [6], [95, 4], [25], [5], [57, 100]]]
 h' := ![![[79, 100], [23, 91], [58, 62], [51, 20], [57, 5], [63, 45], [0, 1]], ![[0, 1], [41, 10], [7, 39], [15, 81], [48, 96], [83, 56], [79, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [98, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [35, 22, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-626, 1158, -233]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![93, 23, -233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-5, 1, 0]] 
 ![![101, 0, 0], ![96, 1, 0], ![76, 0, 1]] where
  M :=![![![-5, 1, 0], ![0, -5, 1], ![114, -18, -5]]]
  hmulB := by decide  
  f := ![![![-43, -5, -1]], ![![-42, -5, -1]], ![![-38, -4, -1]]]
  g := ![![![-1, 1, 0], ![4, -5, 1], ![22, -18, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![43, 5, 1]] ![![-5, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [21, 0, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 88, 102], [30, 14, 1], [0, 1]]
 g := ![![[88, 7, 28], [102, 38, 30], [79, 44, 68], [100, 63], [100, 60], [1]], ![[92, 59, 68, 89], [37, 11, 102, 69], [72, 38, 23, 70], [44, 16], [87, 18], [89, 32, 22, 102]], ![[80, 94, 44, 76], [22, 8, 54, 92], [33, 49, 0, 83], [69, 97], [85, 7], [32, 87, 78, 1]]]
 h' := ![![[6, 88, 102], [21, 44, 53], [92, 75, 37], [81, 29, 58], [92, 79, 28], [82, 0, 36], [0, 1]], ![[30, 14, 1], [11, 17, 80], [32, 90, 31], [29, 61, 62], [52, 88, 4], [98, 77, 92], [6, 88, 102]], ![[0, 1], [57, 42, 73], [25, 41, 35], [22, 13, 86], [21, 39, 71], [63, 26, 78], [30, 14, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 65], []]
 b := ![[], [86, 19, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [21, 0, 67, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8343, 8034, -1751]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81, 78, -17]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![325, -9, -22]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![325, -9, -22]] 
 ![![107, 0, 0], ![0, 107, 0], ![29, 15, 1]] where
  M :=![![![325, -9, -22], ![-2508, 721, -9], ![-1026, -2346, 721]]]
  hmulB := by decide  
  f := ![![![4661, 543, 149]], ![![16986, 1979, 543]], ![![4223, 492, 135]]]
  g := ![![![9, 3, -22], ![-21, 8, -9], ![-205, -123, 721]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [39, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 106], [0, 1]]
 g := ![![[99, 11], [13, 49], [33], [4, 40], [52], [98, 1]], ![[0, 96], [0, 58], [33], [72, 67], [52], [89, 106]]]
 h' := ![![[98, 106], [28, 15], [44, 100], [58, 56], [49, 19], [30, 42], [0, 1]], ![[0, 1], [0, 92], [0, 7], [89, 51], [92, 88], [80, 65], [98, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [90, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [39, 9, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4381, -361, 354]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55, -53, 354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4661, -543, -149]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-4661, -543, -149]] 
 ![![107, 0, 0], ![92, 1, 0], ![96, 0, 1]] where
  M :=![![![-4661, -543, -149], ![-16986, -1979, -543], ![-61902, -7212, -1979]]]
  hmulB := by decide  
  f := ![![![-325, 9, 22]], ![![-256, 1, 19]], ![![-282, 30, 13]]]
  g := ![![![557, -543, -149], ![2030, -1979, -543], ![7398, -7212, -1979]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![325, -9, -22]] ![![-4661, -543, -149]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![11, 50, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![11, 50, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![11, 50, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![11, 50, 1], ![114, -7, 50], ![5700, -786, -7]]]
  hmulB := by decide  
  f := ![![![-10, -50, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -50, 109]], ![![0, 0, 1], ![-4, -23, 50], ![53, -4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [30, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 108], [0, 1]]
 g := ![![[15, 63], [100], [94, 3], [100, 16], [88], [95, 1]], ![[5, 46], [100], [52, 106], [94, 93], [88], [81, 108]]]
 h' := ![![[95, 108], [30, 64], [14, 99], [52, 60], [14, 105], [93, 57], [0, 1]], ![[0, 1], [6, 45], [45, 10], [84, 49], [70, 4], [58, 52], [95, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [83, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [30, 14, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-667, 258, -21]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, 12, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-50, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-50, 1, 0]] 
 ![![109, 0, 0], ![59, 1, 0], ![7, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-50, 1, 0], ![0, -50, 1], ![114, -18, -50]]]
  hmulB := by decide  
  f := ![![![2001, -40, 0], ![4360, 0, 0]], ![![1051, -21, 0], ![2290, 0, 0]], ![![123, -2, 0], ![268, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 109, 0], ![-7, 0, 109]], ![![-1, 1, 0], ![27, -50, 1], ![14, -18, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![11, 50, 1]] ![![109, 0, 0], ![-50, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-5450, 109, 0]], ![![1199, 5450, 109], ![-436, -2507, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-50, 1, 0]]], ![![![11, 50, 1]], ![![-4, -23, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [32, 65, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 17, 38], [93, 95, 75], [0, 1]]
 g := ![![[44, 97, 30], [26, 69], [85, 106], [64, 44], [7, 85, 99], [1]], ![[21, 53, 59, 39], [77, 60], [93, 52], [81, 1], [4, 78, 58, 5], [60, 70, 3, 67]], ![[78, 68, 105, 10], [18, 63], [58, 82], [4, 28], [99, 11, 49, 110], [54, 8, 72, 46]]]
 h' := ![![[61, 17, 38], [61, 46, 97], [92, 46, 42], [103, 66, 85], [2, 109, 48], [81, 48, 41], [0, 1]], ![[93, 95, 75], [31, 37, 2], [3, 68, 88], [70, 16, 74], [17, 20, 1], [78, 6, 69], [61, 17, 38]], ![[0, 1], [100, 30, 14], [87, 112, 96], [94, 31, 67], [30, 97, 64], [103, 59, 3], [93, 95, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 82], []]
 b := ![[], [68, 103, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [32, 65, 72, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112322, -565, -1130]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![994, -5, -10]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-61, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-61, 1, 0]] 
 ![![127, 0, 0], ![66, 1, 0], ![89, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-61, 1, 0], ![0, -61, 1], ![114, -18, -61]]]
  hmulB := by decide  
  f := ![![![2502, -41, 0], ![5207, 0, 0]], ![![1404, -23, 0], ![2922, 0, 0]], ![![1860, -30, 0], ![3871, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 127, 0], ![-89, 0, 127]], ![![-1, 1, 0], ![31, -61, 1], ![53, -18, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-45, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-45, 1, 0]] 
 ![![127, 0, 0], ![82, 1, 0], ![7, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-45, 1, 0], ![0, -45, 1], ![114, -18, -45]]]
  hmulB := by decide  
  f := ![![![3061, -68, 0], ![8636, 0, 0]], ![![2026, -45, 0], ![5716, 0, 0]], ![![241, -5, 0], ![680, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 127, 0], ![-7, 0, 127]], ![![-1, 1, 0], ![29, -45, 1], ![15, -18, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-21, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-21, 1, 0]] 
 ![![127, 0, 0], ![106, 1, 0], ![67, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-21, 1, 0], ![0, -21, 1], ![114, -18, -21]]]
  hmulB := by decide  
  f := ![![![2584, -123, 0], ![15621, 0, 0]], ![![2164, -103, 0], ![13082, 0, 0]], ![![1390, -66, 0], ![8403, 1, 0]]]
  g := ![![![1, 0, 0], ![-106, 127, 0], ![-67, 0, 127]], ![![-1, 1, 0], ![17, -21, 1], ![27, -18, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-61, 1, 0]] ![![127, 0, 0], ![-45, 1, 0]]
  ![![127, 0, 0], ![-49, 21, 1]] where
 M := ![![![16129, 0, 0], ![-5715, 127, 0]], ![![-7747, 127, 0], ![2745, -106, 1]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![4, -20, -1], ![127, 0, 0]]], ![![![-12, -20, -1], ![127, 0, 0]], ![![22, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-49, 21, 1]] ![![127, 0, 0], ![-21, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2667, 127, 0]], ![![-6223, 2667, 127], ![1143, -508, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-21, 1, 0]]], ![![![-49, 21, 1]], ![![9, -4, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1189, 139, 38]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![1189, 139, 38]] 
 ![![131, 0, 0], ![0, 131, 0], ![83, 14, 1]] where
  M :=![![![1189, 139, 38], ![4332, 505, 139], ![15846, 1830, 505]]]
  hmulB := by decide  
  f := ![![![5, -5, 1]], ![![114, -13, -5]], ![![11, -3, 0]]]
  g := ![![![-15, -3, 38], ![-55, -11, 139], ![-199, -40, 505]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [26, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 130], [0, 1]]
 g := ![![[103, 117], [29, 11], [3], [35], [11], [89], [1]], ![[129, 14], [46, 120], [3], [35], [11], [89], [1]]]
 h' := ![![[73, 130], [32, 36], [68, 81], [88, 93], [9, 67], [65, 81], [105, 73], [0, 1]], ![[0, 1], [40, 95], [86, 50], [65, 38], [53, 64], [83, 50], [63, 58], [73, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [65, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [26, 58, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4414, 556, 152]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-130, -12, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 5, -1]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-5, 5, -1]] 
 ![![131, 0, 0], ![117, 1, 0], ![66, 0, 1]] where
  M :=![![![-5, 5, -1], ![-114, 13, 5], ![570, -204, 13]]]
  hmulB := by decide  
  f := ![![![-1189, -139, -38]], ![![-1095, -128, -35]], ![![-720, -84, -23]]]
  g := ![![![-4, 5, -1], ![-15, 13, 5], ![180, -204, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![1189, 139, 38]] ![![-5, 5, -1]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![52, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![52, 1, 0]] 
 ![![137, 0, 0], ![52, 1, 0], ![36, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![52, 1, 0], ![0, 52, 1], ![114, -18, 52]]]
  hmulB := by decide  
  f := ![![![1197, 23, 0], ![-3151, 0, 0]], ![![468, 9, 0], ![-1232, 0, 0]], ![![332, 6, 0], ![-874, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 137, 0], ![-36, 0, 137]], ![![0, 1, 0], ![-20, 52, 1], ![-6, -18, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-29, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-29, 1, 0]] 
 ![![137, 0, 0], ![108, 1, 0], ![118, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-29, 1, 0], ![0, -29, 1], ![114, -18, -29]]]
  hmulB := by decide  
  f := ![![![1915, -66, 0], ![9042, 0, 0]], ![![1538, -53, 0], ![7262, 0, 0]], ![![1660, -57, 0], ![7838, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 137, 0], ![-118, 0, 137]], ![![-1, 1, 0], ![22, -29, 1], ![40, -18, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-23, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-23, 1, 0]] 
 ![![137, 0, 0], ![114, 1, 0], ![19, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-23, 1, 0], ![0, -23, 1], ![114, -18, -23]]]
  hmulB := by decide  
  f := ![![![185, -8, 0], ![1096, 0, 0]], ![![162, -7, 0], ![960, 0, 0]], ![![27, -1, 0], ![160, 1, 0]]]
  g := ![![![1, 0, 0], ![-114, 137, 0], ![-19, 0, 137]], ![![-1, 1, 0], ![19, -23, 1], ![19, -18, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![52, 1, 0]] ![![137, 0, 0], ![-29, 1, 0]]
  ![![137, 0, 0], ![-1, 23, 1]] where
 M := ![![![18769, 0, 0], ![-3973, 137, 0]], ![![7124, 137, 0], ![-1508, 23, 1]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![-28, -22, -1], ![137, 0, 0]]], ![![![52, 1, 0], ![0, 0, 0]], ![![-11, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-1, 23, 1]] ![![137, 0, 0], ![-23, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3151, 137, 0]], ![![-137, 3151, 137], ![137, -548, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-23, 1, 0]]], ![![![-1, 23, 1]], ![![1, -4, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB174I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB174I2 : PrimesBelowBoundCertificateInterval O 79 137 174 where
  m := 11
  g := ![1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB174I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I101N1, I107N1, I109N1, I127N0, I127N1, I127N2, I131N1, I137N0, I137N1, I137N2]
  Il := ![[], [], [], [I101N1], [], [I107N1], [I109N1], [], [I127N0, I127N1, I127N2], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
