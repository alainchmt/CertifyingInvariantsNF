
import IdealArithmetic.Examples.NF3_1_138580_1.RI3_1_138580_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [72, 72, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 19, 64], [18, 63, 19], [0, 1]]
 g := ![![[17, 29, 63], [63, 49, 31], [56, 23], [61, 3], [38, 39, 1], []], ![[37, 72, 77, 17], [76, 28, 18, 48], [31, 61], [71, 4], [17, 32, 8, 36], [77, 29]], ![[7, 38, 48, 57], [30, 40, 70, 80], [72, 37], [41, 38], [14, 32, 40, 53], [39, 29]]]
 h' := ![![[21, 19, 64], [29, 8, 35], [42, 18, 60], [16, 59, 40], [3, 17, 13], [0, 0, 1], [0, 1]], ![[18, 63, 19], [42, 2, 61], [12, 73, 35], [70, 1, 71], [6, 42, 81], [43, 55, 63], [21, 19, 64]], ![[0, 1], [51, 73, 70], [62, 75, 71], [73, 23, 55], [55, 24, 72], [6, 28, 19], [18, 63, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 79], []]
 b := ![[], [57, 6, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [72, 72, 44, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-250411, 54531, -11620]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3017, 657, -140]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-18, 6, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-18, 6, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![71, 6, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-18, 6, 1], ![84, -28, 25], ![466, -7, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -6, 89]], ![![-1, 0, 1], ![-19, -2, 25], ![18, 1, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [79, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 88], [0, 1]]
 g := ![![[76, 80], [9], [50], [66, 32], [35, 79], [1]], ![[0, 9], [9], [50], [0, 57], [0, 10], [1]]]
 h' := ![![[48, 88], [1, 76], [0, 3], [37, 53], [83, 78], [10, 48], [0, 1]], ![[0, 1], [0, 13], [55, 86], [0, 36], [0, 11], [0, 41], [48, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [55, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [79, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1129, 851, 127]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-114, 1, 127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-25, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-25, 1, 0]] 
 ![![89, 0, 0], ![64, 1, 0], ![16, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-25, 1, 0], ![2, -26, 4], ![72, -4, -24]]]
  hmulB := by decide  
  f := ![![![5008, -73191, 11264], ![-2225, -250624, 0]], ![![3599, -52606, 8096], ![-1601, -180136, 0]], ![![902, -13158, 2025], ![-394, -45056, 0]]]
  g := ![![![1, 0, 0], ![-64, 89, 0], ![-16, 0, 89]], ![![-1, 1, 0], ![18, -26, 4], ![8, -4, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-18, 6, 1]] ![![89, 0, 0], ![-25, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2225, 89, 0]], ![![-1602, 534, 89], ![534, -178, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-25, 1, 0]]], ![![![-18, 6, 1]], ![![6, -2, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [71, 92, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 64, 46], [60, 32, 51], [0, 1]]
 g := ![![[59, 3, 70], [68, 62], [73, 18], [80, 3], [12, 18], [1]], ![[25, 64, 70, 51], [26, 70], [3, 27], [30, 86], [50, 96], [24, 56, 83, 45]], ![[32, 5, 46, 71], [32, 61], [88, 43], [84, 8], [68, 22], [81, 87, 68, 52]]]
 h' := ![![[79, 64, 46], [46, 58, 19], [11, 55, 81], [76, 37, 55], [18, 12, 87], [26, 5, 42], [0, 1]], ![[60, 32, 51], [33, 47, 75], [6, 92, 78], [92, 14, 67], [66, 32, 38], [30, 55, 22], [79, 64, 46]], ![[0, 1], [20, 89, 3], [35, 47, 35], [50, 46, 72], [0, 53, 69], [50, 37, 33], [60, 32, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 1], []]
 b := ![[], [2, 53, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [71, 92, 55, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-335579745, 29080988, -16336352]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3459585, 299804, -168416]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-25, 4, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-25, 4, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![76, 4, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-25, 4, 1], ![80, -33, 17], ![322, 1, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -4, 101]], ![![-1, 0, 1], ![-12, -1, 17], ![22, 1, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [40, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 100], [0, 1]]
 g := ![![[76, 21], [45], [4, 96], [58], [65], [91, 1]], ![[68, 80], [45], [54, 5], [58], [65], [81, 100]]]
 h' := ![![[91, 100], [65, 83], [42, 34], [50, 46], [42, 82], [97, 60], [0, 1]], ![[0, 1], [43, 18], [5, 67], [95, 55], [30, 19], [2, 41], [91, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [17, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [40, 10, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1100, 1590, -360]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![260, 30, -360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-17, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-17, 1, 0]] 
 ![![101, 0, 0], ![84, 1, 0], ![25, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-17, 1, 0], ![2, -18, 4], ![72, -4, -16]]]
  hmulB := by decide  
  f := ![![![15298, -143601, 31920], ![-3939, -805980, 0]], ![![12729, -119416, 26544], ![-3231, -670236, 0]], ![![3790, -35545, 7901], ![-955, -199500, 0]]]
  g := ![![![1, 0, 0], ![-84, 101, 0], ![-25, 0, 101]], ![![-1, 1, 0], ![14, -18, 4], ![8, -4, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-25, 4, 1]] ![![101, 0, 0], ![-17, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1717, 101, 0]], ![![-2525, 404, 101], ![505, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-17, 1, 0]]], ![![![-25, 4, 1]], ![![5, -1, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [17, 49, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6, 27], [36, 96, 76], [0, 1]]
 g := ![![[18, 89, 13], [88, 86, 19], [9, 87, 66], [17, 17], [83, 79], [1]], ![[95, 67, 60, 24], [60, 82, 7, 86], [17, 93, 82, 43], [88, 13], [17, 26], [14, 46, 19, 10]], ![[92, 11, 73, 55], [22, 79, 38, 81], [25, 41, 43, 68], [23, 66], [26, 41], [0, 34, 60, 93]]]
 h' := ![![[3, 6, 27], [49, 22, 42], [53, 39, 88], [38, 43, 13], [11, 67, 29], [86, 54, 39], [0, 1]], ![[36, 96, 76], [1, 88, 94], [93, 29, 25], [14, 58, 40], [45, 43, 61], [98, 33, 52], [3, 6, 27]], ![[0, 1], [54, 96, 70], [68, 35, 93], [50, 2, 50], [82, 96, 13], [100, 16, 12], [36, 96, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 47], []]
 b := ![[], [43, 96, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [17, 49, 64, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-242977, 67568, -13802]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2359, 656, -134]
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



lemma PB106I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 105 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 105 (by omega)

def PB106I2 : PrimesBelowBoundCertificateInterval O 79 105 106 where
  m := 5
  g := ![1, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103]
  hP := PB106I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I89N1, I101N1]
  Il := ![[], [I89N1], [], [I101N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
