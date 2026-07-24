
import IdealArithmetic.Examples.NF3_1_655215_2.RI3_1_655215_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [27, 13, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 16, 15], [61, 66, 68], [0, 1]]
 g := ![![[13, 64, 63], [3, 81, 44], [46, 4], [74, 61], [8, 42, 1], []], ![[11, 39, 25, 6], [56, 67, 45, 22], [12, 63], [80, 7], [38, 41, 13, 19], [53, 59]], ![[36, 43, 6, 4], [71, 53, 33, 17], [42, 10], [23, 16], [17, 66, 15, 61], [0, 59]]]
 h' := ![![[64, 16, 15], [2, 44, 48], [19, 46, 25], [4, 11, 2], [33, 7, 12], [0, 0, 1], [0, 1]], ![[61, 66, 68], [13, 13, 10], [34, 32, 16], [62, 40, 48], [8, 43, 67], [9, 15, 66], [64, 16, 15]], ![[0, 1], [22, 26, 25], [68, 5, 42], [66, 32, 33], [43, 33, 4], [69, 68, 16], [61, 66, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 1], []]
 b := ![[], [8, 32, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [27, 13, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10707, 49800, -48057]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![129, 600, -579]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![48, -21, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![48, -21, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![48, 68, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![48, -21, 1], ![120, -8, -42], ![-2580, 795, 13]]]
  hmulB := by decide  
  f := ![![![-47, 21, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -68, 89]], ![![0, -1, 1], ![24, 32, -42], ![-36, -1, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [69, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 88], [0, 1]]
 g := ![![[70, 40], [67], [69], [58, 21], [79, 42], [1]], ![[0, 49], [67], [69], [88, 68], [50, 47], [1]]]
 h' := ![![[65, 88], [73, 29], [54, 44], [3, 46], [67, 56], [20, 65], [0, 1]], ![[0, 1], [0, 60], [66, 45], [56, 43], [58, 33], [62, 24], [65, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [64, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [69, 24, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46, 703, -470]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![254, 367, -470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, 1, 0]] 
 ![![89, 0, 0], ![42, 1, 0], ![76, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, 1, 0], ![0, 43, 2], ![120, -35, 42]]]
  hmulB := by decide  
  f := ![![![1639, 39, 0], ![-3471, 0, 0]], ![![714, 17, 0], ![-1512, 0, 0]], ![![1376, 11, -1], ![-2914, 45, 0]]]
  g := ![![![1, 0, 0], ![-42, 89, 0], ![-76, 0, 89]], ![![0, 1, 0], ![-22, 43, 2], ![-18, -35, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![48, -21, 1]] ![![89, 0, 0], ![42, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3738, 89, 0]], ![![4272, -1869, 89], ![2136, -890, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![42, 1, 0]]], ![![![48, -21, 1]], ![![24, -10, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![14, 32, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![14, 32, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![14, 32, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![14, 32, 1], ![120, 11, 64], ![3780, -1060, -21]]]
  hmulB := by decide  
  f := ![![![-13, -32, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -32, 97]], ![![0, 0, 1], ![-8, -21, 64], ![42, -4, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [52, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 96], [0, 1]]
 g := ![![[78, 18], [43], [25], [54], [70], [18, 1]], ![[14, 79], [43], [25], [54], [70], [36, 96]]]
 h' := ![![[18, 96], [4, 42], [94, 25], [91, 92], [38, 65], [34, 78], [0, 1]], ![[0, 1], [81, 55], [59, 72], [1, 5], [44, 32], [80, 19], [18, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [52, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [52, 79, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-968, 60, 14]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -4, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![33, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![33, 1, 0]] 
 ![![97, 0, 0], ![33, 1, 0], ![21, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![33, 1, 0], ![0, 34, 2], ![120, -35, 33]]]
  hmulB := by decide  
  f := ![![![1387, 42, 0], ![-4074, 0, 0]], ![![429, 13, 0], ![-1260, 0, 0]], ![![303, -8, -1], ![-890, 49, 0]]]
  g := ![![![1, 0, 0], ![-33, 97, 0], ![-21, 0, 97]], ![![0, 1, 0], ![-12, 34, 2], ![6, -35, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![14, 32, 1]] ![![97, 0, 0], ![33, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3201, 97, 0]], ![![1358, 3104, 97], ![582, 1067, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![33, 1, 0]]], ![![![14, 32, 1]], ![![6, 11, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-18, -37, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-18, -37, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![83, 64, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-18, -37, 1], ![120, -90, -74], ![-4500, 1355, -53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -64, 101]], ![![-1, -1, 1], ![62, 46, -74], ![-1, 47, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [90, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 100], [0, 1]]
 g := ![![[31, 96], [68], [24, 58], [21], [65], [38, 1]], ![[43, 5], [68], [6, 43], [21], [65], [76, 100]]]
 h' := ![![[38, 100], [47, 55], [62, 13], [33, 19], [2, 83], [14, 41], [0, 1]], ![[0, 1], [16, 46], [51, 88], [48, 82], [25, 18], [57, 60], [38, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [36, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [90, 63, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1054, 674, -1192]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![990, 762, -1192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-27, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-27, 1, 0]] 
 ![![101, 0, 0], ![74, 1, 0], ![53, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-27, 1, 0], ![0, -26, 2], ![120, -35, -27]]]
  hmulB := by decide  
  f := ![![![838, -31, 0], ![3131, 0, 0]], ![![622, -23, 0], ![2324, 0, 0]], ![![436, -3, -1], ![1629, 51, 0]]]
  g := ![![![1, 0, 0], ![-74, 101, 0], ![-53, 0, 101]], ![![-1, 1, 0], ![18, -26, 2], ![41, -35, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-18, -37, 1]] ![![101, 0, 0], ![-27, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2727, 101, 0]], ![![-1818, -3737, 101], ![606, 909, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-27, 1, 0]]], ![![![-18, -37, 1]], ![![6, 9, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![29, -37, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![29, -37, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![29, 66, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![29, -37, 1], ![120, -43, -74], ![-4500, 1355, -6]]]
  hmulB := by decide  
  f := ![![![-28, 37, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -66, 103]], ![![0, -1, 1], ![22, 47, -74], ![-42, 17, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [31, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 102], [0, 1]]
 g := ![![[95, 61], [29, 14], [80, 17], [52], [15], [42, 1]], ![[82, 42], [102, 89], [73, 86], [52], [15], [84, 102]]]
 h' := ![![[42, 102], [28, 24], [95, 80], [50, 74], [80, 19], [37, 85], [0, 1]], ![[0, 1], [6, 79], [56, 23], [68, 29], [54, 84], [2, 18], [42, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [72, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [31, 61, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![931, 2, -490]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147, 314, -490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-29, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-29, 1, 0]] 
 ![![103, 0, 0], ![74, 1, 0], ![6, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-29, 1, 0], ![0, -28, 2], ![120, -35, -29]]]
  hmulB := by decide  
  f := ![![![1857, -64, 0], ![6592, 0, 0]], ![![1364, -47, 0], ![4842, 0, 0]], ![![120, 10, -1], ![426, 52, 0]]]
  g := ![![![1, 0, 0], ![-74, 103, 0], ![-6, 0, 103]], ![![-1, 1, 0], ![20, -28, 2], ![28, -35, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![29, -37, 1]] ![![103, 0, 0], ![-29, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2987, 103, 0]], ![![2987, -3811, 103], ![-721, 1030, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-29, 1, 0]]], ![![![29, -37, 1]], ![![-7, 10, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [91, 28, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 100, 83], [99, 6, 24], [0, 1]]
 g := ![![[104, 25, 13], [42, 93, 57], [37, 85], [70, 61, 42], [4, 33], [1]], ![[67, 54, 72, 34], [53, 66, 25, 87], [77, 10], [52, 61, 35, 87], [7, 11], [88, 52, 101, 86]], ![[91, 85, 22, 6], [37, 56, 106, 70], [32, 49], [37, 89, 46, 5], [75, 76], [28, 82, 97, 21]]]
 h' := ![![[59, 100, 83], [30, 5, 86], [96, 36, 59], [50, 87, 70], [106, 55, 91], [16, 79, 51], [0, 1]], ![[99, 6, 24], [66, 21, 75], [23, 90, 25], [90, 96, 44], [15, 50, 82], [63, 60, 15], [59, 100, 83]], ![[0, 1], [90, 81, 53], [6, 88, 23], [55, 31, 100], [53, 2, 41], [43, 75, 41], [99, 6, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 40], []]
 b := ![[], [87, 1, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [91, 28, 56, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18698464, -5039700, 11355803]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-174752, -47100, 106129]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [107, 42, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 3, 31], [92, 105, 78], [0, 1]]
 g := ![![[82, 26, 82], [44, 84], [57, 67, 94], [98, 29, 36], [14, 27], [1]], ![[71, 92, 9, 73], [13, 71], [31, 53, 52, 36], [7, 16, 96, 81], [19, 61], [99, 106, 22, 34]], ![[87, 22, 90, 66], [37, 104], [1, 75, 37, 75], [8, 56, 25, 26], [78, 1], [22, 6, 38, 75]]]
 h' := ![![[55, 3, 31], [4, 71, 55], [5, 77, 56], [87, 18, 51], [32, 61, 6], [2, 67, 38], [0, 1]], ![[92, 105, 78], [106, 95, 19], [25, 95, 92], [12, 8, 27], [43, 75, 14], [21, 62, 72], [55, 3, 31]], ![[0, 1], [10, 52, 35], [46, 46, 70], [10, 83, 31], [35, 82, 89], [36, 89, 108], [92, 105, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 66], []]
 b := ![[], [95, 2, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [107, 42, 71, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14715, -1744, -872]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![135, -16, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [23, 49, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 83, 107], [105, 29, 6], [0, 1]]
 g := ![![[0, 112, 63], [64, 26], [80, 100], [0, 1], [56, 46, 64], [1]], ![[20, 26, 87, 71], [78, 87], [45, 111], [14, 25], [15, 73, 4, 101], [103, 39, 70, 10]], ![[21, 1, 46, 55], [45, 102], [20, 53], [62, 36], [41, 79, 86, 94], [10, 29, 48, 103]]]
 h' := ![![[0, 83, 107], [25, 55, 96], [49, 109, 79], [104, 69, 103], [68, 4, 1], [90, 64, 105], [0, 1]], ![[105, 29, 6], [40, 82, 81], [79, 81, 55], [53, 19, 87], [107, 44, 5], [4, 45, 62], [0, 83, 107]], ![[0, 1], [35, 89, 49], [77, 36, 92], [56, 25, 36], [76, 65, 107], [49, 4, 59], [105, 29, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 75], []]
 b := ![[], [76, 17, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [23, 49, 8, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![240803, -235944, 156618]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2131, -2088, 1386]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![81, -51, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![81, -51, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![81, 76, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![81, -51, 1], ![120, -5, -102], ![-6180, 1845, 46]]]
  hmulB := by decide  
  f := ![![![-80, 51, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -76, 127]], ![![0, -1, 1], ![66, 61, -102], ![-78, -13, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [64, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 126], [0, 1]]
 g := ![![[121, 2], [31, 32], [124, 1], [121, 2], [96, 104], [3, 1]], ![[0, 125], [0, 95], [0, 126], [0, 125], [27, 23], [6, 126]]]
 h' := ![![[3, 126], [48, 111], [65, 63], [3, 126], [79, 16], [62, 72], [0, 1]], ![[0, 1], [0, 16], [0, 64], [0, 1], [0, 111], [24, 55], [3, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [73, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [64, 124, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9676, -2160, -1900]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1288, 1120, -1900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-25, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-25, 1, 0]] 
 ![![127, 0, 0], ![102, 1, 0], ![81, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-25, 1, 0], ![0, -24, 2], ![120, -35, -25]]]
  hmulB := by decide  
  f := ![![![1976, -79, 0], ![10033, 0, 0]], ![![1576, -63, 0], ![8002, 0, 0]], ![![1278, -39, -1], ![6489, 64, 0]]]
  g := ![![![1, 0, 0], ![-102, 127, 0], ![-81, 0, 127]], ![![-1, 1, 0], ![18, -24, 2], ![45, -35, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![81, -51, 1]] ![![127, 0, 0], ![-25, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3175, 127, 0]], ![![10287, -6477, 127], ![-1905, 1270, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-25, 1, 0]]], ![![![81, -51, 1]], ![![-15, 10, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![81, 25, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![81, 25, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![81, 25, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![81, 25, 1], ![120, 71, 50], ![2940, -815, 46]]]
  hmulB := by decide  
  f := ![![![-80, -25, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -25, 131]], ![![0, 0, 1], ![-30, -9, 50], ![-6, -15, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [42, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 130], [0, 1]]
 g := ![![[77, 129], [92, 125], [7], [109], [5], [109], [1]], ![[126, 2], [108, 6], [7], [109], [5], [109], [1]]]
 h' := ![![[41, 130], [66, 28], [14, 115], [35, 20], [91, 90], [68, 108], [89, 41], [0, 1]], ![[0, 1], [35, 103], [13, 16], [69, 111], [113, 41], [42, 23], [67, 90], [41, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [97, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [42, 90, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1321, 60, 81]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, -15, 81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-50, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-50, 1, 0]] 
 ![![131, 0, 0], ![81, 1, 0], ![85, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-50, 1, 0], ![0, -49, 2], ![120, -35, -50]]]
  hmulB := by decide  
  f := ![![![5501, -110, 0], ![14410, 0, 0]], ![![3451, -69, 0], ![9040, 0, 0]], ![![3635, -48, -1], ![9522, 66, 0]]]
  g := ![![![1, 0, 0], ![-81, 131, 0], ![-85, 0, 131]], ![![-1, 1, 0], ![29, -49, 2], ![55, -35, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![81, 25, 1]] ![![131, 0, 0], ![-50, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-6550, 131, 0]], ![![10611, 3275, 131], ![-3930, -1179, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-50, 1, 0]]], ![![![81, 25, 1]], ![![-30, -9, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![54, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![54, 1, 0]] 
 ![![137, 0, 0], ![54, 1, 0], ![22, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![54, 1, 0], ![0, 55, 2], ![120, -35, 54]]]
  hmulB := by decide  
  f := ![![![1675, 31, 0], ![-4247, 0, 0]], ![![594, 11, 0], ![-1506, 0, 0]], ![![254, -23, -1], ![-644, 69, 0]]]
  g := ![![![1, 0, 0], ![-54, 137, 0], ![-22, 0, 137]], ![![0, 1, 0], ![-22, 55, 2], ![6, -35, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-41, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-41, 1, 0]] 
 ![![137, 0, 0], ![96, 1, 0], ![2, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-41, 1, 0], ![0, -40, 2], ![120, -35, -41]]]
  hmulB := by decide  
  f := ![![![5290, -129, 0], ![17673, 0, 0]], ![![3732, -91, 0], ![12468, 0, 0]], ![![88, 18, -1], ![294, 69, 0]]]
  g := ![![![1, 0, 0], ![-96, 137, 0], ![-2, 0, 137]], ![![-1, 1, 0], ![28, -40, 2], ![26, -35, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-14, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-14, 1, 0]] 
 ![![137, 0, 0], ![123, 1, 0], ![46, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-14, 1, 0], ![0, -13, 2], ![120, -35, -14]]]
  hmulB := by decide  
  f := ![![![883, -63, 0], ![8631, 0, 0]], ![![813, -58, 0], ![7947, 0, 0]], ![![302, -15, -1], ![2952, 69, 0]]]
  g := ![![![1, 0, 0], ![-123, 137, 0], ![-46, 0, 137]], ![![-1, 1, 0], ![11, -13, 2], ![37, -35, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![54, 1, 0]] ![![137, 0, 0], ![-41, 1, 0]]
  ![![137, 0, 0], ![-11, 7, 1]] where
 M := ![![![18769, 0, 0], ![-5617, 137, 0]], ![![7398, 137, 0], ![-2214, 14, 2]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![-30, -6, -1], ![137, 0, 0]]], ![![![54, 1, 0], ![0, 0, 0]], ![![-16, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-11, 7, 1]] ![![137, 0, 0], ![-14, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-1918, 137, 0]], ![![-1507, 959, 137], ![274, -137, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-14, 1, 0]]], ![![![-11, 7, 1]], ![![2, -1, 0]]]]
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


lemma PB230I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB230I2 : PrimesBelowBoundCertificateInterval O 79 137 230 where
  m := 11
  g := ![1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB230I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
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
      exact NI89N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I89N1, I97N1, I101N1, I103N1, I127N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N1], [], [], [], [I127N1], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
