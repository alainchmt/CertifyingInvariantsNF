
import IdealArithmetic.Examples.NF3_1_387731_1.RI3_1_387731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![34, 22, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![34, 22, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![34, 22, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![34, 22, 1], ![4, 27, 88], ![87, -637, 5]]]
  hmulB := by decide  
  f := ![![![-33, -22, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -22, 83]], ![![0, 0, 1], ![-36, -23, 88], ![-1, -9, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [16, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 82], [0, 1]]
 g := ![![[29, 26], [55, 3], [78], [1], [36, 77], [1]], ![[0, 57], [74, 80], [78], [1], [81, 6], [1]]]
 h' := ![![[34, 82], [33, 21], [78, 13], [9, 24], [5, 82], [67, 34], [0, 1]], ![[0, 1], [0, 62], [22, 70], [78, 59], [54, 1], [61, 49], [34, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [9, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [16, 49, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![79, -857, -1748]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![717, 453, -1748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-5, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-5, 1, 0]] 
 ![![83, 0, 0], ![78, 1, 0], ![78, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-5, 1, 0], ![0, -4, 4], ![4, -29, -5]]]
  hmulB := by decide  
  f := ![![![261, -52, 0], ![4316, 0, 0]], ![![246, -49, 0], ![4068, 0, 0]], ![![246, -48, -1], ![4068, 21, 0]]]
  g := ![![![1, 0, 0], ![-78, 83, 0], ![-78, 0, 83]], ![![-1, 1, 0], ![0, -4, 4], ![32, -29, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![34, 22, 1]] ![![83, 0, 0], ![-5, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-415, 83, 0]], ![![2822, 1826, 83], ![-166, -83, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-5, 1, 0]]], ![![![34, 22, 1]], ![![-2, -1, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [66, 85, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 40, 64], [14, 48, 25], [0, 1]]
 g := ![![[19, 48, 64], [55, 68], [21, 44], [58, 80, 44], [40, 6, 1], []], ![[45, 36, 80, 53], [50, 49], [14, 88], [17, 0, 30, 21], [22, 33, 26, 72], [59, 2]], ![[78, 58, 1, 69], [10, 73], [23, 18], [31, 22, 26, 69], [5, 0, 44, 39], [9, 2]]]
 h' := ![![[81, 40, 64], [27, 21, 81], [39, 47, 54], [88, 35, 69], [30, 31, 20], [0, 0, 1], [0, 1]], ![[14, 48, 25], [61, 55, 70], [35, 81, 82], [46, 16, 34], [78, 43, 7], [86, 87, 48], [81, 40, 64]], ![[0, 1], [34, 13, 27], [31, 50, 42], [83, 38, 75], [69, 15, 62], [47, 2, 40], [14, 48, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 37], []]
 b := ![[], [71, 48, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [66, 85, 83, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4361, 52777, 96120]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, 593, 1080]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [63, 80, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 60, 88], [38, 36, 9], [0, 1]]
 g := ![![[52, 15, 65], [4, 93], [36, 48], [85, 49], [81, 11], [1]], ![[24, 71, 2, 43], [39, 31], [5, 12], [73, 47], [84, 27], [42, 17, 37, 47]], ![[8, 83, 30, 96], [26, 65], [13, 12], [54, 25], [5, 27], [31, 49, 11, 50]]]
 h' := ![![[22, 60, 88], [86, 25, 29], [12, 16, 44], [7, 21, 57], [30, 94, 7], [34, 17, 60], [0, 1]], ![[38, 36, 9], [74, 83, 43], [3, 51, 82], [30, 67, 20], [19, 70, 85], [48, 45, 67], [22, 60, 88]], ![[0, 1], [90, 86, 25], [51, 30, 68], [26, 9, 20], [79, 30, 5], [54, 35, 67], [38, 36, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 32], []]
 b := ![[], [90, 14, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [63, 80, 37, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-115527, -97, -3977]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1191, -1, -41]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![64, 30, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![64, 30, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![64, 30, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![64, 30, 1], ![4, 65, 120], ![119, -869, 35]]]
  hmulB := by decide  
  f := ![![![-63, -30, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -30, 101]], ![![0, 0, 1], ![-76, -35, 120], ![-21, -19, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [39, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 100], [0, 1]]
 g := ![![[19, 97], [58], [59, 4], [31], [36], [67, 1]], ![[54, 4], [58], [24, 97], [31], [36], [33, 100]]]
 h' := ![![[67, 100], [40, 20], [22, 82], [27, 99], [78, 43], [13, 6], [0, 1]], ![[0, 1], [67, 81], [62, 19], [95, 2], [30, 58], [11, 95], [67, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [64, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [39, 34, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![137, -1031, -2657]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1685, 779, -2657]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-19, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-19, 1, 0]] 
 ![![101, 0, 0], ![82, 1, 0], ![66, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-19, 1, 0], ![0, -18, 4], ![4, -29, -19]]]
  hmulB := by decide  
  f := ![![![723, -38, 0], ![3838, 0, 0]], ![![590, -31, 0], ![3132, 0, 0]], ![![486, -12, -3], ![2580, 76, 0]]]
  g := ![![![1, 0, 0], ![-82, 101, 0], ![-66, 0, 101]], ![![-1, 1, 0], ![12, -18, 4], ![36, -29, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![64, 30, 1]] ![![101, 0, 0], ![-19, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1919, 101, 0]], ![![6464, 3030, 101], ![-1212, -505, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-19, 1, 0]]], ![![![64, 30, 1]], ![![-12, -5, 1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![15, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![15, 1, 0]] 
 ![![103, 0, 0], ![15, 1, 0], ![43, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![15, 1, 0], ![0, 16, 4], ![4, -29, 15]]]
  hmulB := by decide  
  f := ![![![676, 45, 0], ![-4635, 0, 0]], ![![90, 6, 0], ![-617, 0, 0]], ![![256, 13, -1], ![-1755, 26, 0]]]
  g := ![![![1, 0, 0], ![-15, 103, 0], ![-43, 0, 103]], ![![0, 1, 0], ![-4, 16, 4], ![-2, -29, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![21, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![21, 1, 0]] 
 ![![103, 0, 0], ![21, 1, 0], ![39, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![21, 1, 0], ![0, 22, 4], ![4, -29, 21]]]
  hmulB := by decide  
  f := ![![![715, 34, 0], ![-3502, 0, 0]], ![![147, 7, 0], ![-720, 0, 0]], ![![243, 6, -1], ![-1190, 26, 0]]]
  g := ![![![1, 0, 0], ![-21, 103, 0], ![-39, 0, 103]], ![![0, 1, 0], ![-6, 22, 4], ![-2, -29, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-37, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-37, 1, 0]] 
 ![![103, 0, 0], ![66, 1, 0], ![79, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-37, 1, 0], ![0, -36, 4], ![4, -29, -37]]]
  hmulB := by decide  
  f := ![![![2628, -71, 0], ![7313, 0, 0]], ![![1740, -47, 0], ![4842, 0, 0]], ![![2076, -47, -1], ![5777, 26, 0]]]
  g := ![![![1, 0, 0], ![-66, 103, 0], ![-79, 0, 103]], ![![-1, 1, 0], ![20, -36, 4], ![47, -29, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![15, 1, 0]] ![![103, 0, 0], ![21, 1, 0]]
  ![![103, 0, 0], ![53, 35, 1]] where
 M := ![![![10609, 0, 0], ![2163, 103, 0]], ![![1545, 103, 0], ![315, 37, 4]]]
 hmul := by decide  
 g := ![![![![50, -35, -1], ![103, 0, 0]], ![![-32, -34, -1], ![103, 0, 0]]], ![![![-38, -34, -1], ![103, 0, 0]], ![![1, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![53, 35, 1]] ![![103, 0, 0], ![-37, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3811, 103, 0]], ![![5459, 3605, 103], ![-1957, -1236, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-37, 1, 0]]], ![![![53, 35, 1]], ![![-19, -12, 1]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [13, 60, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 88, 68], [93, 18, 39], [0, 1]]
 g := ![![[9, 2, 47], [96, 21, 79], [2, 13], [1, 74, 101], [77, 41], [1]], ![[65, 3, 40, 54], [37, 76, 50, 43], [43, 100], [66, 43, 95, 84], [93, 3], [15, 16, 101, 66]], ![[8, 52, 21, 47], [28, 4, 77, 99], [96, 105], [26, 21, 52, 37], [4, 52], [35, 42, 44, 41]]]
 h' := ![![[97, 88, 68], [36, 78, 58], [36, 72, 20], [94, 89, 21], [24, 45, 23], [94, 47, 83], [0, 1]], ![[93, 18, 39], [85, 35, 35], [52, 48, 13], [41, 74, 10], [78, 3, 50], [89, 40, 89], [97, 88, 68]], ![[0, 1], [60, 101, 14], [29, 94, 74], [97, 51, 76], [69, 59, 34], [11, 20, 42], [93, 18, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 43], []]
 b := ![[], [13, 106, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [13, 60, 24, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24182, -242676, -313724]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![226, -2268, -2932]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-15, 29, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-15, 29, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![94, 29, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-15, 29, 1], ![4, -15, 116], ![115, -840, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -29, 109]], ![![-1, 0, 1], ![-100, -31, 116], ![39, 4, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [12, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 108], [0, 1]]
 g := ![![[81, 100], [16], [37, 46], [56, 46], [74], [9, 1]], ![[0, 9], [16], [15, 63], [34, 63], [74], [18, 108]]]
 h' := ![![[9, 108], [90, 99], [101, 105], [91, 68], [94, 41], [1, 69], [0, 1]], ![[0, 1], [0, 10], [65, 4], [49, 41], [27, 68], [77, 40], [9, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [30, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [12, 100, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6152, -64599, -100087]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![86370, 26036, -100087]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-7, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-7, 1, 0]] 
 ![![109, 0, 0], ![102, 1, 0], ![44, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-7, 1, 0], ![0, -6, 4], ![4, -29, -7]]]
  hmulB := by decide  
  f := ![![![575, -82, 0], ![8938, 0, 0]], ![![540, -77, 0], ![8394, 0, 0]], ![![242, -30, -3], ![3762, 82, 0]]]
  g := ![![![1, 0, 0], ![-102, 109, 0], ![-44, 0, 109]], ![![-1, 1, 0], ![4, -6, 4], ![30, -29, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-15, 29, 1]] ![![109, 0, 0], ![-7, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-763, 109, 0]], ![![-1635, 3161, 109], ![109, -218, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-7, 1, 0]]], ![![![-15, 29, 1]], ![![1, -2, 1]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [55, 100, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 64, 92], [1, 48, 21], [0, 1]]
 g := ![![[69, 109, 63], [14, 63], [46, 87], [95, 57], [10, 83, 44], [1]], ![[63, 111, 70, 10], [43, 9], [49, 91], [110, 112], [3, 78, 63, 37], [63, 6, 49, 5]], ![[110, 15, 90, 93], [86, 61], [4, 1], [2, 82], [90, 65, 54, 37], [49, 98, 97, 108]]]
 h' := ![![[47, 64, 92], [23, 4, 17], [62, 42, 96], [85, 96, 55], [15, 59, 82], [58, 13, 48], [0, 1]], ![[1, 48, 21], [52, 73, 54], [48, 46, 110], [101, 108, 59], [7, 55, 98], [14, 76, 110], [47, 64, 92]], ![[0, 1], [20, 36, 42], [111, 25, 20], [52, 22, 112], [7, 112, 46], [18, 24, 68], [1, 48, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 77], []]
 b := ![[], [20, 37, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [55, 100, 65, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9718, 82264, 54579]
  a := ![-1, 2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, 728, 483]
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


def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, 1457, 73]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-199, 1457, 73]] 
 ![![127, 0, 0], ![43, 1, 0], ![35, 0, 1]] where
  M :=![![![-199, 1457, 73], ![292, -859, 5828], ![5755, -42180, -2316]]]
  hmulB := by decide  
  f := ![![![-247814484, -295272, -8554103]], ![![-84175112, -100295, -2905571]], ![![-68237275, -81305, -2355426]]]
  g := ![![![-515, 1457, 73], ![-1313, -859, 5828], ![14965, -42180, -2316]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-22, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-22, 1, 0]] 
 ![![127, 0, 0], ![105, 1, 0], ![75, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-22, 1, 0], ![0, -21, 4], ![4, -29, -22]]]
  hmulB := by decide  
  f := ![![![1673, -76, 0], ![9652, 0, 0]], ![![1387, -63, 0], ![8002, 0, 0]], ![![997, -40, -1], ![5752, 32, 0]]]
  g := ![![![1, 0, 0], ![-105, 127, 0], ![-75, 0, 127]], ![![-1, 1, 0], ![15, -21, 4], ![37, -29, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-199, 1457, 73]] ![![127, 0, 0], ![-22, 1, 0]]
  ![![127, 0, 0], ![81, -58, 1]] where
 M := ![![![-25273, 185039, 9271], ![4670, -32913, 4222]]]
 hmul := by decide  
 g := ![![![![44, 1283, 76], ![-381, 0, 0]], ![![-64, -187, 32], ![158, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![81, -58, 1]] ![![127, 0, 0], ![-22, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2794, 127, 0]], ![![10287, -7366, 127], ![-1778, 1270, -254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-22, 1, 0]]], ![![![81, -58, 1]], ![![-14, 10, -2]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![53, -42, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![53, -42, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![53, 89, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![53, -42, 1], ![4, -18, -168], ![-169, 1219, 24]]]
  hmulB := by decide  
  f := ![![![-52, 42, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -89, 131]], ![![0, -1, 1], ![68, 114, -168], ![-11, -7, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [92, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 130], [0, 1]]
 g := ![![[94, 11], [65, 11], [41], [45], [41], [4], [1]], ![[72, 120], [43, 120], [41], [45], [41], [4], [1]]]
 h' := ![![[129, 130], [46, 81], [31, 50], [129, 98], [48, 62], [105, 98], [39, 129], [0, 1]], ![[0, 1], [15, 50], [62, 81], [64, 33], [55, 69], [40, 33], [43, 2], [129, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [18, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [92, 2, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![235, -1778, -3451]
  a := ![0, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1398, 2331, -3451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![37, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![37, 1, 0]] 
 ![![131, 0, 0], ![37, 1, 0], ![107, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![37, 1, 0], ![0, 38, 4], ![4, -29, 37]]]
  hmulB := by decide  
  f := ![![![1814, 49, 0], ![-6419, 0, 0]], ![![518, 14, 0], ![-1833, 0, 0]], ![![1502, 31, -1], ![-5315, 33, 0]]]
  g := ![![![1, 0, 0], ![-37, 131, 0], ![-107, 0, 131]], ![![0, 1, 0], ![-14, 38, 4], ![-22, -29, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![53, -42, 1]] ![![131, 0, 0], ![37, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![4847, 131, 0]], ![![6943, -5502, 131], ![1965, -1572, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![37, 1, 0]]], ![![![53, -42, 1]], ![![15, -12, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![87, 63, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![87, 63, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![87, 63, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![87, 63, 1], ![4, 121, 252], ![251, -1826, 58]]]
  hmulB := by decide  
  f := ![![![-86, -63, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -63, 137]], ![![0, 0, 1], ![-160, -115, 252], ![-35, -40, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [125, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 136], [0, 1]]
 g := ![![[15, 109], [81], [119], [29, 133], [15], [68], [1]], ![[44, 28], [81], [119], [131, 4], [15], [68], [1]]]
 h' := ![![[43, 136], [52, 71], [54, 9], [74, 121], [44, 63], [1, 120], [12, 43], [0, 1]], ![[0, 1], [91, 66], [30, 128], [71, 16], [13, 74], [92, 17], [80, 94], [43, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [11, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [125, 94, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1241, -10444, -15936]
  a := ![2, -8, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10129, 7252, -15936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![22, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![22, 1, 0]] 
 ![![137, 0, 0], ![22, 1, 0], ![79, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![22, 1, 0], ![0, 23, 4], ![4, -29, 22]]]
  hmulB := by decide  
  f := ![![![1739, 79, 0], ![-10823, 0, 0]], ![![242, 11, 0], ![-1506, 0, 0]], ![![997, 28, -3], ![-6205, 103, 0]]]
  g := ![![![1, 0, 0], ![-22, 137, 0], ![-79, 0, 137]], ![![0, 1, 0], ![-6, 23, 4], ![-8, -29, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![87, 63, 1]] ![![137, 0, 0], ![22, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![3014, 137, 0]], ![![11919, 8631, 137], ![1918, 1507, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![22, 1, 0]]], ![![![87, 63, 1]], ![![14, 11, 2]]]]
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


lemma PB177I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB177I2 : PrimesBelowBoundCertificateInterval O 79 137 177 where
  m := 11
  g := ![2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB177I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N1]
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
    · exact ![704969]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
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
      exact NI83N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I101N1, I103N0, I103N1, I103N2, I109N1, I127N0, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [], [], [I101N1], [I103N0, I103N1, I103N2], [], [I109N1], [], [I127N0, I127N1, I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
