
import IdealArithmetic.Examples.NF3_3_392472_1.RI3_3_392472_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [11, 39, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 81, 17], [0, 1, 66], [0, 1]]
 g := ![![[28, 15, 61], [3, 45, 28], [], [10, 38], [39, 24, 1], []], ![[46, 35, 24, 9], [48, 38, 16, 41], [8, 48], [18, 69], [47, 56, 68, 17], [62, 40]], ![[0, 48, 7, 60], [13, 9, 15, 39], [82, 48], [82, 38], [62, 32, 44, 15], [13, 40]]]
 h' := ![![[24, 81, 17], [50, 50, 71], [9, 50, 51], [3, 36], [69, 41, 72], [0, 0, 1], [0, 1]], ![[0, 1, 66], [32, 73, 8], [36, 57, 71], [37, 11, 31], [61, 42, 22], [60, 34, 1], [24, 81, 17]], ![[0, 1], [23, 43, 4], [20, 59, 44], [3, 36, 52], [65, 0, 72], [23, 49, 81], [0, 1, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 12], []]
 b := ![[], [79, 24, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [11, 39, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25564, -46480, -18758]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-308, -560, -226]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [69, 63, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 46, 36], [67, 42, 53], [0, 1]]
 g := ![![[56, 83, 1], [2, 57], [41, 50], [38, 42, 32], [36, 30, 1], []], ![[27, 9, 62, 80], [32, 17], [22, 53], [16, 27, 4, 9], [9, 3, 8, 47], [6, 50]], ![[84, 6, 37, 84], [88, 67], [20, 17], [35, 34, 28, 36], [59, 85, 31, 8], [78, 50]]]
 h' := ![![[52, 46, 36], [32, 71, 1], [9, 2, 18], [48, 23, 36], [8, 23, 11], [0, 0, 1], [0, 1]], ![[67, 42, 53], [51, 39, 17], [37, 34, 27], [24, 52, 26], [50, 4, 44], [65, 66, 42], [52, 46, 36]], ![[0, 1], [69, 68, 71], [0, 53, 44], [57, 14, 27], [3, 62, 34], [86, 23, 46], [67, 42, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 88], []]
 b := ![[], [69, 52, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [69, 63, 59, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39338, 71467, 122820]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-442, 803, 1380]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-248, 2, 7]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-248, 2, 7]] 
 ![![97, 0, 0], ![0, 97, 0], ![20, 28, 1]] where
  M :=![![![-248, 2, 7], ![231, 13, -3], ![-165, 60, 16]]]
  hmulB := by decide  
  f := ![![![4, 4, -1]], ![![-33, -29, 9]], ![![-7, -6, 2]]]
  g := ![![![-4, -2, 7], ![3, 1, -3], ![-5, -4, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [79, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 96], [0, 1]]
 g := ![![[82, 70], [94], [95], [8], [94], [21, 1]], ![[0, 27], [94], [95], [8], [94], [42, 96]]]
 h' := ![![[21, 96], [11, 78], [29, 71], [29, 17], [46, 69], [87, 71], [0, 1]], ![[0, 1], [0, 19], [65, 26], [95, 80], [40, 28], [26, 26], [21, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [25, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [79, 76, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-722, -2, 90]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -26, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 4, -1]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![4, 4, -1]] 
 ![![97, 0, 0], ![42, 1, 0], ![67, 0, 1]] where
  M :=![![![4, 4, -1], ![-33, -29, 9], ![165, 150, -38]]]
  hmulB := by decide  
  f := ![![![-248, 2, 7]], ![![-105, 1, 3]], ![![-173, 2, 5]]]
  g := ![![![-1, 4, -1], ![6, -29, 9], ![-37, 150, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-248, 2, 7]] ![![4, 4, -1]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [32, 96, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 99, 63], [100, 1, 38], [0, 1]]
 g := ![![[40, 63, 58], [30, 9], [55, 68, 47], [49, 1], [61, 14], [1]], ![[22, 73, 70, 46], [43, 37], [85, 45, 92, 86], [75, 58], [83, 17], [24, 41, 3, 72]], ![[12, 19, 61, 59], [15, 71], [63, 55, 17, 74], [13, 21], [30, 19], [62, 21, 8, 29]]]
 h' := ![![[33, 99, 63], [81, 2, 82], [58, 43, 98], [5, 31, 42], [82, 42, 100], [69, 5, 32], [0, 1]], ![[100, 1, 38], [62, 45, 6], [23, 44, 80], [73, 37, 76], [7, 94, 19], [21, 51, 44], [33, 99, 63]], ![[0, 1], [11, 54, 13], [84, 14, 24], [18, 33, 84], [63, 66, 83], [35, 45, 25], [100, 1, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 90], []]
 b := ![[], [67, 83, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [32, 96, 69, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33330, -139986, -108474]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-330, -1386, -1074]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4265, -3796, 1058]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-4265, -3796, 1058]] 
 ![![103, 0, 0], ![0, 103, 0], ![50, 41, 1]] where
  M :=![![![-4265, -3796, 1058], ![34914, 31085, -8650], ![-160182, -142568, 39735]]]
  hmulB := by decide  
  f := ![![![18925, -28, -510]], ![![-16830, 27, 454]], ![![2642, -3, -71]]]
  g := ![![![-555, -458, 1058], ![4538, 3745, -8650], ![-20844, -17201, 39735]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [73, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 102], [0, 1]]
 g := ![![[85, 7], [63, 56], [1, 79], [41], [30], [78, 1]], ![[13, 96], [2, 47], [86, 24], [41], [30], [53, 102]]]
 h' := ![![[78, 102], [36, 78], [30, 57], [94, 39], [93, 91], [74, 37], [0, 1]], ![[0, 1], [43, 25], [47, 46], [46, 64], [84, 12], [76, 66], [78, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [29, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [73, 25, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172, 380, 263]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-126, -101, 263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18925, -28, -510]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![18925, -28, -510]] 
 ![![103, 0, 0], ![22, 1, 0], ![56, 0, 1]] where
  M :=![![![18925, -28, -510], ![-16830, 27, 454], ![15906, -16, -427]]]
  hmulB := by decide  
  f := ![![![-4265, -3796, 1058]], ![![-572, -509, 142]], ![![-3874, -3448, 961]]]
  g := ![![![467, -28, -510], ![-416, 27, 454], ![390, -16, -427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-4265, -3796, 1058]] ![![18925, -28, -510]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-882164, -785280, 218703]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-882164, -785280, 218703]] 
 ![![107, 0, 0], ![0, 107, 0], ![54, 87, 1]] where
  M :=![![![-882164, -785280, 218703], ![7217199, 6424567, -1789263], ![-33131439, -29492766, 8213830]]]
  hmulB := by decide  
  f := ![![![-129064, 186, 3477]], ![![114741, -229, -3105]], ![![27144, -93, -743]]]
  g := ![![![-118618, -185163, 218703], ![970443, 1514864, -1789263], ![-4454937, -6954168, 8213830]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [81, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 106], [0, 1]]
 g := ![![[47, 37], [78, 37], [12], [34, 100], [3], [45, 1]], ![[0, 70], [31, 70], [12], [40, 7], [3], [90, 106]]]
 h' := ![![[45, 106], [102, 12], [26, 95], [28, 36], [20, 97], [100, 18], [0, 1]], ![[0, 1], [0, 95], [21, 12], [43, 71], [105, 10], [54, 89], [45, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [64, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [81, 62, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13311, 31878, 18062]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8991, -14388, 18062]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129064, 186, 3477]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-129064, 186, 3477]] 
 ![![107, 0, 0], ![41, 1, 0], ![102, 0, 1]] where
  M :=![![![-129064, 186, 3477], ![114741, -229, -3105], ![-108603, -72, 2876]]]
  hmulB := by decide  
  f := ![![![-882164, -785280, 218703]], ![![-270575, -240859, 67080]], ![![-1150581, -1024218, 285248]]]
  g := ![![![-4592, 186, 3477], ![4120, -229, -3105], ![-3729, -72, 2876]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-882164, -785280, 218703]] ![![-129064, 186, 3477]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![434680, 386976, -107773]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![434680, 386976, -107773]] 
 ![![109, 0, 0], ![0, 109, 0], ![93, 71, 1]] where
  M :=![![![434680, 386976, -107773], ![-3556509, -3165945, 881725], ![16326717, 14533658, -4047670]]]
  hmulB := by decide  
  f := ![![![100900, 139654, 27735]], ![![915255, 1266749, 251573]], ![![716148, 991181, 196846]]]
  g := ![![![95941, 73751, -107773], ![-784926, -603380, 881725], ![3603303, 2769892, -4047670]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [21, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 108], [0, 1]]
 g := ![![[18, 26], [102], [75, 4], [94, 106], [97], [58, 1]], ![[0, 83], [102], [89, 105], [29, 3], [97], [7, 108]]]
 h' := ![![[58, 108], [41, 35], [60, 50], [97, 2], [68, 18], [90, 73], [0, 1]], ![[0, 1], [0, 74], [17, 59], [104, 107], [22, 91], [73, 36], [58, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [93, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [21, 51, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70, 248, 91]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -57, 91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100900, -139654, -27735]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-100900, -139654, -27735]] 
 ![![109, 0, 0], ![77, 1, 0], ![49, 0, 1]] where
  M :=![![![-100900, -139654, -27735], ![-915255, -1266749, -251573], ![-3693327, -5111728, -1015176]]]
  hmulB := by decide  
  f := ![![![-434680, -386976, 107773]], ![![-274439, -244323, 68044]], ![![-345193, -307298, 85583]]]
  g := ![![![110197, -139654, -27735], ![999555, -1266749, -251573], ![4033517, -5111728, -1015176]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![434680, 386976, -107773]] ![![-100900, -139654, -27735]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7214, 6440, -1793]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![7214, 6440, -1793]] 
 ![![113, 0, 0], ![0, 113, 0], ![44, 15, 1]] where
  M :=![![![7214, 6440, -1793], ![-59169, -52687, 14673], ![271689, 241866, -67360]]]
  hmulB := by decide  
  f := ![![![-854, -1174, -233]], ![![-7689, -10649, -2115]], ![![-1628, -2251, -447]]]
  g := ![![![762, 295, -1793], ![-6237, -2414, 14673], ![28633, 11082, -67360]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [32, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 112], [0, 1]]
 g := ![![[5, 53], [60], [22], [13], [28, 109], [66, 1]], ![[0, 60], [60], [22], [13], [103, 4], [19, 112]]]
 h' := ![![[66, 112], [110, 36], [30, 25], [100, 94], [8, 37], [35, 30], [0, 1]], ![[0, 1], [0, 77], [98, 88], [89, 19], [77, 76], [94, 83], [66, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [112, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [32, 47, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![197, 1210, 1173]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-455, -145, 1173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-854, -1174, -233]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-854, -1174, -233]] 
 ![![113, 0, 0], ![84, 1, 0], ![46, 0, 1]] where
  M :=![![![-854, -1174, -233], ![-7689, -10649, -2115], ![-31053, -42972, -8534]]]
  hmulB := by decide  
  f := ![![![7214, 6440, -1793]], ![![4839, 4321, -1203]], ![![5341, 4762, -1326]]]
  g := ![![![960, -1174, -233], ![8709, -10649, -2115], ![35143, -42972, -8534]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![7214, 6440, -1793]] ![![-854, -1174, -233]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![256, 226, -63]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![256, 226, -63]] 
 ![![127, 0, 0], ![33, 1, 0], ![74, 0, 1]] where
  M :=![![![256, 226, -63], ![-2079, -1849, 515], ![9537, 8488, -2364]]]
  hmulB := by decide  
  f := ![![![-284, -480, -97]], ![![-99, -159, -32]], ![![-265, -418, -84]]]
  g := ![![![-20, 226, -63], ![164, -1849, 515], ![-753, 8488, -2364]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76913, -68466, 19068]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-76913, -68466, 19068]] 
 ![![127, 0, 0], ![106, 1, 0], ![44, 0, 1]] where
  M :=![![![-76913, -68466, 19068], ![629244, 560137, -156000], ![-2888622, -2571378, 716137]]]
  hmulB := by decide  
  f := ![![![-137231, 138, 3684]], ![![-113582, 109, 3048]], ![![-48466, 30, 1297]]]
  g := ![![![49933, -68466, 19068], ![-408514, 560137, -156000], ![1875334, -2571378, 716137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![298370, 265602, -73971]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![298370, 265602, -73971]] 
 ![![127, 0, 0], ![115, 1, 0], ![61, 0, 1]] where
  M :=![![![298370, 265602, -73971], ![-2441043, -2172955, 605175], ![11205909, 9975216, -2778130]]]
  hmulB := by decide  
  f := ![![![-131350, -181524, -36045]], ![![-128305, -177337, -35214]], ![![-100891, -139506, -27703]]]
  g := ![![![-202627, 265602, -73971], ![1657741, -2172955, 605175], ![-7610063, 9975216, -2778130]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![256, 226, -63]] ![![-76913, -68466, 19068]]
  ![![304502602, 271060480, -75491223]] where
 M := ![![![304502602, 271060480, -75491223]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![304502602, 271060480, -75491223]] ![![298370, 265602, -73971]]
  ![![127, 0, 0]] where
 M := ![![![-1416763621158607, -1261166980751164, 351239095364448]]]
 hmul := by decide  
 g := ![![![![-11155619064241, -9930448667332, 2765662168224]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2954830, 2630314, -732551]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![2954830, 2630314, -732551]] 
 ![![131, 0, 0], ![0, 131, 0], ![125, 96, 1]] where
  M :=![![![2954830, 2630314, -732551], ![-24174183, -21519243, 5993179], ![110974545, 98786720, -27512422]]]
  hmulB := by decide  
  f := ![![![-9514, -13452, -2677]], ![![-88341, -122015, -24227]], ![![-76531, -106010, -21055]]]
  g := ![![![721555, 556910, -732551], ![-5903218, -4556217, 5993179], ![27099445, 20915872, -27512422]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [88, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 130], [0, 1]]
 g := ![![[1, 39], [5, 48], [91], [5], [7], [15], [1]], ![[106, 92], [104, 83], [91], [5], [7], [15], [1]]]
 h' := ![![[43, 130], [84, 68], [127, 110], [119, 22], [64, 108], [5, 20], [43, 43], [0, 1]], ![[0, 1], [126, 63], [10, 21], [17, 109], [123, 23], [79, 111], [58, 88], [43, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [92, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [88, 88, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2248, 2808, 848]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-792, -600, 848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9514, 13452, 2677]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![9514, 13452, 2677]] 
 ![![131, 0, 0], ![71, 1, 0], ![64, 0, 1]] where
  M :=![![![9514, 13452, 2677], ![88341, 122015, 24227], ![355575, 492370, 97788]]]
  hmulB := by decide  
  f := ![![![-2954830, -2630314, 732551]], ![![-1416937, -1261321, 351282]], ![![-2290715, -2039136, 567906]]]
  g := ![![![-8526, 13452, 2677], ![-77292, 122015, 24227], ![-311917, 492370, 97788]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![2954830, 2630314, -732551]] ![![9514, 13452, 2677]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-589, -500, 140]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-589, -500, 140]] 
 ![![137, 0, 0], ![0, 137, 0], ![32, 16, 1]] where
  M :=![![![-589, -500, 140], ![4620, 4091, -1140], ![-21120, -18780, 5231]]]
  hmulB := by decide  
  f := ![![![67, 100, 20]], ![![660, 907, 180]], ![![112, 156, 31]]]
  g := ![![![-37, -20, 140], ![300, 163, -1140], ![-1376, -748, 5231]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [60, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 136], [0, 1]]
 g := ![![[70, 16], [50], [11], [28, 135], [61], [17], [1]], ![[0, 121], [50], [11], [71, 2], [61], [17], [1]]]
 h' := ![![[47, 136], [86, 4], [88, 119], [101, 55], [20, 51], [114, 91], [77, 47], [0, 1]], ![[0, 1], [0, 133], [64, 18], [83, 82], [88, 86], [7, 46], [94, 90], [47, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [103, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [60, 90, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1366, -2, 154]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -18, 154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 100, 20]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![67, 100, 20]] 
 ![![137, 0, 0], ![106, 1, 0], ![83, 0, 1]] where
  M :=![![![67, 100, 20], ![660, 907, 180], ![2640, 3660, 727]]]
  hmulB := by decide  
  f := ![![![-589, -500, 140]], ![![-422, -357, 100]], ![![-511, -440, 123]]]
  g := ![![![-89, 100, 20], ![-806, 907, 180], ![-3253, 3660, 727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-589, -500, 140]] ![![67, 100, 20]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB140I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB140I2 : PrimesBelowBoundCertificateInterval O 79 137 140 where
  m := 11
  g := ![1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB140I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
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
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I97N1, I103N1, I107N1, I109N1, I113N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[], [], [I97N1], [], [I103N1], [I107N1], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
