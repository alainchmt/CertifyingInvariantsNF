
import IdealArithmetic.Examples.NF3_1_536787_1.RI3_1_536787_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-13, -30, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-13, -30, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![70, 53, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-13, -30, 1], ![141, -13, -30], ![-4230, 141, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -53, 83]], ![![-1, -1, 1], ![27, 19, -30], ![-40, 10, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [15, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 82], [0, 1]]
 g := ![![[25, 36], [59, 41], [25], [28], [52, 23], [1]], ![[54, 47], [39, 42], [25], [28], [59, 60], [1]]]
 h' := ![![[40, 82], [28, 77], [65, 37], [5, 78], [50, 51], [68, 40], [0, 1]], ![[0, 1], [37, 6], [51, 46], [54, 5], [15, 32], [8, 43], [40, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [55, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [15, 43, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297, 98, -42]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, 28, -42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![30, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![30, 1, 0]] 
 ![![83, 0, 0], ![30, 1, 0], ![13, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![30, 1, 0], ![0, 30, 1], ![141, 0, 30]]]
  hmulB := by decide  
  f := ![![![781, 26, 0], ![-2158, 0, 0]], ![![270, 9, 0], ![-746, 0, 0]], ![![71, 2, 0], ![-196, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 83, 0], ![-13, 0, 83]], ![![0, 1, 0], ![-11, 30, 1], ![-3, 0, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-13, -30, 1]] ![![83, 0, 0], ![30, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2490, 83, 0]], ![![-1079, -2490, 83], ![-249, -913, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![30, 1, 0]]], ![![![-13, -30, 1]], ![![-3, -11, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-34, -12, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-34, -12, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![55, 77, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-34, -12, 1], ![141, -34, -12], ![-1692, 141, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -77, 89]], ![![-1, -1, 1], ![9, 10, -12], ![2, 31, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [1, 13, 1] where
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
 g := ![![[13, 1], [8], [40], [27, 44], [54, 80], [1]], ![[0, 88], [8], [40], [78, 45], [82, 9], [1]]]
 h' := ![![[76, 88], [76, 88], [66, 50], [62, 29], [35, 20], [88, 76], [0, 1]], ![[0, 1], [0, 1], [39, 39], [41, 60], [42, 69], [79, 13], [76, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [1, 13, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1703, 1247, 37]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -18, 37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![12, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![12, 1, 0]] 
 ![![89, 0, 0], ![12, 1, 0], ![34, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![12, 1, 0], ![0, 12, 1], ![141, 0, 12]]]
  hmulB := by decide  
  f := ![![![505, 42, 0], ![-3738, 0, 0]], ![![60, 5, 0], ![-444, 0, 0]], ![![194, 16, 0], ![-1436, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 89, 0], ![-34, 0, 89]], ![![0, 1, 0], ![-2, 12, 1], ![-3, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-34, -12, 1]] ![![89, 0, 0], ![12, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1068, 89, 0]], ![![-3026, -1068, 89], ![-267, -178, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![12, 1, 0]]], ![![![-34, -12, 1]], ![![-3, -2, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [11, 4, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 77, 49], [52, 19, 48], [0, 1]]
 g := ![![[31, 21, 11], [51, 1], [18, 25], [20, 11], [89, 4], [1]], ![[61, 31, 53, 3], [30, 49], [35, 44], [34, 61], [86, 35], [39, 96, 58, 85]], ![[28, 15, 85, 1], [82, 64], [52, 33], [87, 4], [25, 86], [43, 11, 14, 12]]]
 h' := ![![[47, 77, 49], [74, 38, 37], [21, 73, 1], [5, 42, 92], [15, 76, 37], [86, 93, 2], [0, 1]], ![[52, 19, 48], [10, 49, 43], [7, 9, 7], [95, 60, 23], [88, 65, 62], [89, 11, 36], [47, 77, 49]], ![[0, 1], [66, 10, 17], [80, 15, 89], [19, 92, 79], [43, 53, 95], [67, 90, 59], [52, 19, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 20], []]
 b := ![[], [8, 29, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [11, 4, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![134345, -13968, 194]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1385, -144, 2]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![49, 7, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![49, 7, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![49, 7, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![49, 7, 1], ![141, 49, 7], ![987, 141, 49]]]
  hmulB := by decide  
  f := ![![![-48, -7, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -7, 101]], ![![0, 0, 1], ![-2, 0, 7], ![-14, -2, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [2, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 100], [0, 1]]
 g := ![![[30, 5], [54], [26, 49], [43], [30], [41, 1]], ![[33, 96], [54], [15, 52], [43], [30], [82, 100]]]
 h' := ![![[41, 100], [71, 45], [49, 16], [19, 94], [99, 89], [19, 63], [0, 1]], ![[0, 1], [98, 56], [99, 85], [35, 7], [11, 12], [77, 38], [41, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [84, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [2, 60, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-783, 1331, -185]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![82, 26, -185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-7, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-7, 1, 0]] 
 ![![101, 0, 0], ![94, 1, 0], ![52, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-7, 1, 0], ![0, -7, 1], ![141, 0, -7]]]
  hmulB := by decide  
  f := ![![![232, -33, 0], ![3333, 0, 0]], ![![218, -31, 0], ![3132, 0, 0]], ![![120, -17, 0], ![1724, 1, 0]]]
  g := ![![![1, 0, 0], ![-94, 101, 0], ![-52, 0, 101]], ![![-1, 1, 0], ![6, -7, 1], ![5, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![49, 7, 1]] ![![101, 0, 0], ![-7, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-707, 101, 0]], ![![4949, 707, 101], ![-202, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-7, 1, 0]]], ![![![49, 7, 1]], ![![-2, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [40, 92, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 68, 22], [24, 34, 81], [0, 1]]
 g := ![![[83, 81, 16], [94, 84, 92], [100, 83, 63], [44, 15], [], [1]], ![[77, 96, 98, 3], [56, 19, 31, 22], [62, 77, 54, 73], [28, 4], [90, 60], [74, 81, 62, 39]], ![[52, 65, 58, 56], [5, 48, 91, 19], [52, 33, 55, 81], [44, 50], [58, 60], [31, 44, 31, 64]]]
 h' := ![![[79, 68, 22], [51, 23, 4], [17, 63, 35], [29, 7, 28], [55, 47, 18], [63, 11], [0, 1]], ![[24, 34, 81], [76, 74, 24], [26, 53, 1], [89, 37, 76], [30, 96, 101], [5, 27, 36], [79, 68, 22]], ![[0, 1], [11, 6, 75], [57, 90, 67], [70, 59, 102], [64, 63, 87], [18, 65, 67], [24, 34, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 5], []]
 b := ![[], [63, 79, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [40, 92, 0, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19982, -515, -515]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-194, -5, -5]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-24, -46, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-24, -46, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![83, 61, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-24, -46, 1], ![141, -24, -46], ![-6486, 141, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -61, 107]], ![![-1, -1, 1], ![37, 26, -46], ![-42, 15, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [83, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 106], [0, 1]]
 g := ![![[91, 49], [102, 101], [57], [20, 39], [86], [44, 1]], ![[0, 58], [52, 6], [57], [24, 68], [86], [88, 106]]]
 h' := ![![[44, 106], [94, 100], [6, 84], [52, 59], [13, 50], [93, 34], [0, 1]], ![[0, 1], [0, 7], [64, 23], [80, 48], [73, 57], [91, 73], [44, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [63, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [83, 63, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5505, 1376, 426]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-279, -230, 426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![46, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![46, 1, 0]] 
 ![![107, 0, 0], ![46, 1, 0], ![24, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![46, 1, 0], ![0, 46, 1], ![141, 0, 46]]]
  hmulB := by decide  
  f := ![![![231, 5, 0], ![-535, 0, 0]], ![![46, 1, 0], ![-106, 0, 0]], ![![20, 0, 0], ![-46, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 107, 0], ![-24, 0, 107]], ![![0, 1, 0], ![-20, 46, 1], ![-9, 0, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-24, -46, 1]] ![![107, 0, 0], ![46, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4922, 107, 0]], ![![-2568, -4922, 107], ![-963, -2140, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![46, 1, 0]]], ![![![-24, -46, 1]], ![![-9, -20, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![30, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![30, 1, 0]] 
 ![![109, 0, 0], ![30, 1, 0], ![81, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![30, 1, 0], ![0, 30, 1], ![141, 0, 30]]]
  hmulB := by decide  
  f := ![![![961, 32, 0], ![-3488, 0, 0]], ![![210, 7, 0], ![-762, 0, 0]], ![![669, 22, 0], ![-2428, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 109, 0], ![-81, 0, 109]], ![![0, 1, 0], ![-9, 30, 1], ![-21, 0, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![37, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![37, 1, 0]] 
 ![![109, 0, 0], ![37, 1, 0], ![48, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![37, 1, 0], ![0, 37, 1], ![141, 0, 37]]]
  hmulB := by decide  
  f := ![![![1407, 38, 0], ![-4142, 0, 0]], ![![481, 13, 0], ![-1416, 0, 0]], ![![568, 15, 0], ![-1672, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 109, 0], ![-48, 0, 109]], ![![0, 1, 0], ![-13, 37, 1], ![-15, 0, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![42, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![42, 1, 0]] 
 ![![109, 0, 0], ![42, 1, 0], ![89, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![42, 1, 0], ![0, 42, 1], ![141, 0, 42]]]
  hmulB := by decide  
  f := ![![![463, 11, 0], ![-1199, 0, 0]], ![![126, 3, 0], ![-326, 0, 0]], ![![395, 9, 0], ![-1023, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 109, 0], ![-89, 0, 109]], ![![0, 1, 0], ![-17, 42, 1], ![-33, 0, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![30, 1, 0]] ![![109, 0, 0], ![37, 1, 0]]
  ![![109, 0, 0], ![20, -42, 1]] where
 M := ![![![11881, 0, 0], ![4033, 109, 0]], ![![3270, 109, 0], ![1110, 67, 1]]]
 hmul := by decide  
 g := ![![![![89, 42, -1], ![109, 0, 0]], ![![17, 43, -1], ![109, 0, 0]]], ![![![10, 43, -1], ![109, 0, 0]], ![![-10, 43, -1], ![110, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![20, -42, 1]] ![![109, 0, 0], ![42, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![4578, 109, 0]], ![![2180, -4578, 109], ![981, -1744, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![42, 1, 0]]], ![![![20, -42, 1]], ![![9, -16, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![30, 16, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![30, 16, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![30, 16, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![30, 16, 1], ![141, 30, 16], ![2256, 141, 30]]]
  hmulB := by decide  
  f := ![![![-29, -16, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -16, 113]], ![![0, 0, 1], ![-3, -2, 16], ![12, -3, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [30, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 112], [0, 1]]
 g := ![![[76, 49], [102], [16], [82], [13, 57], [93, 1]], ![[0, 64], [102], [16], [82], [3, 56], [73, 112]]]
 h' := ![![[93, 112], [86, 106], [78, 21], [28, 109], [62, 46], [35, 31], [0, 1]], ![[0, 1], [0, 7], [110, 92], [108, 4], [46, 67], [93, 82], [93, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [8, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [30, 20, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-835, 195, -9]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, 3, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-16, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-16, 1, 0]] 
 ![![113, 0, 0], ![97, 1, 0], ![83, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-16, 1, 0], ![0, -16, 1], ![141, 0, -16]]]
  hmulB := by decide  
  f := ![![![1729, -108, 0], ![12204, 0, 0]], ![![1489, -93, 0], ![10510, 0, 0]], ![![1283, -80, 0], ![9056, 1, 0]]]
  g := ![![![1, 0, 0], ![-97, 113, 0], ![-83, 0, 113]], ![![-1, 1, 0], ![13, -16, 1], ![13, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![30, 16, 1]] ![![113, 0, 0], ![-16, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1808, 113, 0]], ![![3390, 1808, 113], ![-339, -226, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-16, 1, 0]]], ![![![30, 16, 1]], ![![-3, -2, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [69, 43, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 88, 116], [19, 38, 11], [0, 1]]
 g := ![![[15, 113, 16], [42, 82, 120], [46, 112, 35], [7, 74, 82], [71], [1]], ![[76, 5, 2, 91], [70, 1, 47, 116], [30, 93, 83, 27], [42, 40, 32, 101], [29, 76, 58, 114], [37, 16, 67, 66]], ![[76, 94, 117, 42], [35, 63, 0, 35], [17, 123, 60, 64], [53, 3, 22, 74], [5, 19, 77, 13], [92, 110, 78, 61]]]
 h' := ![![[108, 88, 116], [23, 30, 4], [1, 63, 45], [25, 49, 110], [54, 57, 92], [58, 84], [0, 1]], ![[19, 38, 11], [55, 62, 76], [52, 100, 1], [28, 92, 85], [117, 78, 75], [113, 26, 92], [108, 88, 116]], ![[0, 1], [28, 35, 47], [17, 91, 81], [87, 113, 59], [80, 119, 87], [3, 17, 35], [19, 38, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 30], []]
 b := ![[], [78, 2, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [69, 43, 0, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159258, 889, 1778]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1254, 7, 14]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![15, -43, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![15, -43, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![15, 88, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![15, -43, 1], ![141, 15, -43], ![-6063, 141, 15]]]
  hmulB := by decide  
  f := ![![![-14, 43, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -88, 131]], ![![0, -1, 1], ![6, 29, -43], ![-48, -9, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [112, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 130], [0, 1]]
 g := ![![[107, 62], [92, 129], [61], [1], [16], [39], [1]], ![[0, 69], [87, 2], [61], [1], [16], [39], [1]]]
 h' := ![![[68, 130], [45, 113], [24, 103], [31, 89], [76, 1], [54, 127], [19, 68], [0, 1]], ![[0, 1], [0, 18], [85, 28], [57, 42], [13, 130], [44, 4], [58, 63], [68, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [94, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [112, 63, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5398, -106, 234]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -158, 234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![43, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![43, 1, 0]] 
 ![![131, 0, 0], ![43, 1, 0], ![116, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![43, 1, 0], ![0, 43, 1], ![141, 0, 43]]]
  hmulB := by decide  
  f := ![![![1893, 44, 0], ![-5764, 0, 0]], ![![559, 13, 0], ![-1702, 0, 0]], ![![1692, 39, 0], ![-5152, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 131, 0], ![-116, 0, 131]], ![![0, 1, 0], ![-15, 43, 1], ![-37, 0, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![15, -43, 1]] ![![131, 0, 0], ![43, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![5633, 131, 0]], ![![1965, -5633, 131], ![786, -1834, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![43, 1, 0]]], ![![![15, -43, 1]], ![![6, -14, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![59, 14, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![59, 14, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![59, 14, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![59, 14, 1], ![141, 59, 14], ![1974, 141, 59]]]
  hmulB := by decide  
  f := ![![![-58, -14, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -14, 137]], ![![0, 0, 1], ![-5, -1, 14], ![-11, -5, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [114, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 136], [0, 1]]
 g := ![![[23, 105], [121], [11], [125, 36], [22], [87], [1]], ![[83, 32], [121], [11], [126, 101], [22], [87], [1]]]
 h' := ![![[118, 136], [58, 67], [120, 11], [135, 82], [81, 131], [64, 76], [23, 118], [0, 1]], ![[0, 1], [18, 70], [48, 126], [84, 55], [58, 6], [127, 61], [110, 19], [118, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [55, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [114, 19, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![248, 96, 46]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -4, 46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-14, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-14, 1, 0]] 
 ![![137, 0, 0], ![123, 1, 0], ![78, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-14, 1, 0], ![0, -14, 1], ![141, 0, -14]]]
  hmulB := by decide  
  f := ![![![799, -57, 0], ![7809, 0, 0]], ![![701, -50, 0], ![6851, 0, 0]], ![![450, -32, 0], ![4398, 1, 0]]]
  g := ![![![1, 0, 0], ![-123, 137, 0], ![-78, 0, 137]], ![![-1, 1, 0], ![12, -14, 1], ![9, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![59, 14, 1]] ![![137, 0, 0], ![-14, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-1918, 137, 0]], ![![8083, 1918, 137], ![-685, -137, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-14, 1, 0]]], ![![![59, 14, 1]], ![![-5, -1, 0]]]]
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


lemma PB208I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB208I2 : PrimesBelowBoundCertificateInterval O 79 137 208 where
  m := 11
  g := ![2, 2, 1, 2, 1, 2, 3, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB208I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI83N1
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I101N1, I107N1, I109N0, I109N1, I109N2, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [], [I107N1], [I109N0, I109N1, I109N2], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
