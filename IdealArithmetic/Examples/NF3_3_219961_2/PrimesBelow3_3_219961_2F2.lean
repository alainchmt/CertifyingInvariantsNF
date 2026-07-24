
import IdealArithmetic.Examples.NF3_3_219961_2.RI3_3_219961_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [41, 43, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 60, 9], [39, 22, 74], [0, 1]]
 g := ![![[71, 39, 69], [16, 7, 59], [74, 21], [15, 78], [50, 33, 1], []], ![[63, 9, 32, 49], [12, 37, 67, 81], [37, 1], [34, 23], [71, 57, 1, 40], [18, 81]], ![[34, 76, 81, 66], [22, 15, 47, 32], [70, 23], [70, 7], [53, 34, 23, 53], [36, 81]]]
 h' := ![![[77, 60, 9], [8, 32, 61], [54, 37, 68], [10, 38, 41], [25, 66, 24], [0, 0, 1], [0, 1]], ![[39, 22, 74], [71, 33, 53], [70, 77, 3], [50, 81, 82], [45, 35, 43], [45, 82, 22], [77, 60, 9]], ![[0, 1], [17, 18, 52], [75, 52, 12], [17, 47, 43], [27, 65, 16], [45, 1, 60], [39, 22, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 43], []]
 b := ![[], [65, 32, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [41, 43, 50, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3100797, -1333312, -470444]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37359, -16064, -5668]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [62, 21, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 42, 19], [76, 46, 70], [0, 1]]
 g := ![![[54, 19, 1], [6, 11], [65, 36], [29, 9, 87], [64, 21, 1], []], ![[44, 85, 60, 56], [24, 69], [66, 44], [42, 69, 37, 15], [46, 48, 88, 65], [10, 5]], ![[57, 29, 43, 56], [4, 21], [53, 53], [5, 53, 36, 60], [82, 38, 87, 37], [48, 5]]]
 h' := ![![[34, 42, 19], [29, 1, 88], [32, 78, 79], [71, 24, 6], [37, 24, 40], [0, 0, 1], [0, 1]], ![[76, 46, 70], [61, 20, 62], [83, 30, 43], [9, 72, 20], [43, 19, 71], [2, 22, 46], [34, 42, 19]], ![[0, 1], [64, 68, 28], [32, 70, 56], [5, 82, 63], [30, 46, 67], [41, 67, 42], [76, 46, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 32], []]
 b := ![[], [19, 75, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [62, 21, 68, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1598084, 927380, 430404]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17956, 10420, 4836]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [63, 66, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 78, 69], [4, 18, 28], [0, 1]]
 g := ![![[49, 18, 85], [62, 95], [41, 88], [13, 66], [87, 53], [1]], ![[33, 5, 66, 34], [58, 43], [23, 89], [4, 36], [11, 25], [72, 86, 78, 67]], ![[21, 78, 80, 21], [17, 64], [90, 9], [45, 85], [20, 62], [25, 7, 92, 30]]]
 h' := ![![[17, 78, 69], [9, 3, 45], [61, 54, 80], [5, 35, 31], [40, 11, 39], [34, 31, 21], [0, 1]], ![[4, 18, 28], [26, 82, 47], [24, 51, 25], [42, 30, 63], [10, 2, 6], [86, 32, 92], [17, 78, 69]], ![[0, 1], [89, 12, 5], [53, 89, 89], [0, 32, 3], [33, 84, 52], [41, 34, 81], [4, 18, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 60], []]
 b := ![[], [45, 32, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [63, 66, 76, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45105, -7372, -8633]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![465, -76, -89]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-48, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-48, 1, 0]] 
 ![![101, 0, 0], ![53, 1, 0], ![42, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-48, 1, 0], ![0, -47, 4], ![152, 39, -48]]]
  hmulB := by decide  
  f := ![![![2881, -60, 0], ![6060, 0, 0]], ![![1585, -33, 0], ![3334, 0, 0]], ![![1218, 10, -3], ![2562, 76, 0]]]
  g := ![![![1, 0, 0], ![-53, 101, 0], ![-42, 0, 101]], ![![-1, 1, 0], ![23, -47, 4], ![1, 39, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-39, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-39, 1, 0]] 
 ![![101, 0, 0], ![62, 1, 0], ![84, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-39, 1, 0], ![0, -38, 4], ![152, 39, -39]]]
  hmulB := by decide  
  f := ![![![2380, -61, 0], ![6161, 0, 0]], ![![1444, -37, 0], ![3738, 0, 0]], ![![1974, -22, -3], ![5110, 76, 0]]]
  g := ![![![1, 0, 0], ![-62, 101, 0], ![-84, 0, 101]], ![![-1, 1, 0], ![20, -38, 4], ![10, 39, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-15, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-15, 1, 0]] 
 ![![101, 0, 0], ![86, 1, 0], ![99, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-15, 1, 0], ![0, -14, 4], ![152, 39, -15]]]
  hmulB := by decide  
  f := ![![![616, -41, 0], ![4141, 0, 0]], ![![526, -35, 0], ![3536, 0, 0]], ![![594, -29, -3], ![3993, 76, 0]]]
  g := ![![![1, 0, 0], ![-86, 101, 0], ![-99, 0, 101]], ![![-1, 1, 0], ![8, -14, 4], ![-17, 39, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-48, 1, 0]] ![![101, 0, 0], ![-39, 1, 0]]
  ![![101, 0, 0], ![-37, 29, 1]] where
 M := ![![![10201, 0, 0], ![-3939, 101, 0]], ![![-4848, 101, 0], ![1872, -86, 4]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![-2, -28, -1], ![101, 0, 0]]], ![![![-11, -28, -1], ![101, 0, 0]], ![![20, -2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-37, 29, 1]] ![![101, 0, 0], ![-15, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1515, 101, 0]], ![![-3737, 2929, 101], ![707, -404, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-15, 1, 0]]], ![![![-37, 29, 1]], ![![7, -4, 1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [58, 45, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 54, 24], [38, 48, 79], [0, 1]]
 g := ![![[82, 58, 28], [16, 55, 18], [8, 23, 60], [31, 8], [20, 91], [1]], ![[57, 47, 60, 73], [82, 8, 21, 94], [32, 26, 26, 95], [8, 30], [19, 83], [86, 5, 22, 22]], ![[50, 41, 0, 76], [65, 59, 44, 91], [51, 97, 11, 2], [90, 79], [36, 9], [77, 78, 1, 81]]]
 h' := ![![[85, 54, 24], [102, 30, 50], [51, 47, 11], [89, 28, 36], [41, 72, 27], [45, 58, 20], [0, 1]], ![[38, 48, 79], [90, 74, 30], [71, 39, 8], [97, 94, 31], [56, 95, 37], [98, 21, 86], [85, 54, 24]], ![[0, 1], [43, 102, 23], [55, 17, 84], [59, 84, 36], [51, 39, 39], [39, 24, 100], [38, 48, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 41], []]
 b := ![[], [54, 94, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [58, 45, 83, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5810127, -2536478, -900735]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56409, -24626, -8745]
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



lemma PB105I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 104 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 104 (by omega)

def PB105I2 : PrimesBelowBoundCertificateInterval O 79 104 105 where
  m := 5
  g := ![1, 1, 1, 3, 1]
  P := ![83, 89, 97, 101, 103]
  hP := PB105I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![704969]
    · exact ![912673]
    · exact ![101, 101, 101]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I101N0, I101N1, I101N2]
  Il := ![[], [], [], [I101N0, I101N1, I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
