
import IdealArithmetic.Examples.NF3_1_996008_1.RI3_1_996008_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [7, 6, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 22, 27], [80, 60, 56], [0, 1]]
 g := ![![[66, 33, 12], [9, 25, 41], [76, 40], [26, 17], [4, 33, 1], []], ![[77, 8, 62, 44], [33, 36, 42, 38], [36, 41], [82, 31], [68, 44, 82, 7], [13, 65]], ![[72, 79, 56, 34], [66, 66, 25, 60], [34, 11], [49, 10], [16, 80, 33, 46], [67, 65]]]
 h' := ![![[36, 22, 27], [20, 1, 26], [75, 0, 46], [21, 61, 66], [55, 77, 10], [0, 0, 1], [0, 1]], ![[80, 60, 56], [12, 41, 10], [61, 40, 21], [75, 75, 46], [20, 3, 23], [43, 55, 60], [36, 22, 27]], ![[0, 1], [9, 41, 47], [80, 43, 16], [22, 30, 54], [38, 3, 50], [38, 28, 22], [80, 60, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 8], []]
 b := ![[], [15, 74, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [7, 6, 50, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34445, 0, 0]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-415, 0, 0]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [69, 70, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 77, 30], [66, 11, 59], [0, 1]]
 g := ![![[53, 20, 4], [30, 10], [29, 36], [20, 10, 84], [1, 58, 1], []], ![[80, 63, 29, 59], [82, 88], [51, 50], [66, 10, 34, 28], [30, 18, 38, 70], [38, 10]], ![[48, 54, 56, 13], [58, 16], [40, 73], [73, 22, 33, 66], [36, 55, 34, 41], [9, 10]]]
 h' := ![![[81, 77, 30], [19, 53, 87], [24, 24, 59], [44, 1, 83], [20, 22, 23], [0, 0, 1], [0, 1]], ![[66, 11, 59], [83, 73, 55], [32, 23, 34], [76, 68, 53], [17, 82, 23], [23, 46, 11], [81, 77, 30]], ![[0, 1], [52, 52, 36], [7, 42, 85], [39, 20, 42], [68, 74, 43], [86, 43, 77], [66, 11, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 41], []]
 b := ![[], [71, 6, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [69, 70, 31, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![723125, 281952, 13528]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8125, 3168, 152]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![27, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![27, 1, 0]] 
 ![![97, 0, 0], ![27, 1, 0], ![47, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![27, 1, 0], ![0, 27, 1], ![198, 25, 27]]]
  hmulB := by decide  
  f := ![![![433, 16, 0], ![-1552, 0, 0]], ![![81, 3, 0], ![-290, 0, 0]], ![![197, 7, 0], ![-706, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 97, 0], ![-47, 0, 97]], ![![0, 1, 0], ![-8, 27, 1], ![-18, 25, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![29, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![29, 1, 0]] 
 ![![97, 0, 0], ![29, 1, 0], ![32, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![29, 1, 0], ![0, 29, 1], ![198, 25, 29]]]
  hmulB := by decide  
  f := ![![![1248, 43, 0], ![-4171, 0, 0]], ![![348, 12, 0], ![-1163, 0, 0]], ![![386, 13, 0], ![-1290, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 97, 0], ![-32, 0, 97]], ![![0, 1, 0], ![-9, 29, 1], ![-15, 25, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![41, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![41, 1, 0]] 
 ![![97, 0, 0], ![41, 1, 0], ![65, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![41, 1, 0], ![0, 41, 1], ![198, 25, 41]]]
  hmulB := by decide  
  f := ![![![1354, 33, 0], ![-3201, 0, 0]], ![![574, 14, 0], ![-1357, 0, 0]], ![![920, 22, 0], ![-2175, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 97, 0], ![-65, 0, 97]], ![![0, 1, 0], ![-18, 41, 1], ![-36, 25, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![27, 1, 0]] ![![97, 0, 0], ![29, 1, 0]]
  ![![97, 0, 0], ![7, -41, 1]] where
 M := ![![![9409, 0, 0], ![2813, 97, 0]], ![![2619, 97, 0], ![783, 56, 1]]]
 hmul := by decide  
 g := ![![![![90, 41, -1], ![97, 0, 0]], ![![22, 42, -1], ![97, 0, 0]]], ![![![20, 42, -1], ![97, 0, 0]], ![![8, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![7, -41, 1]] ![![97, 0, 0], ![41, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3977, 97, 0]], ![![679, -3977, 97], ![485, -1649, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![41, 1, 0]]], ![![![7, -41, 1]], ![![5, -17, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [1, 86, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 50, 20], [6, 50, 81], [0, 1]]
 g := ![![[46, 67, 87], [45, 68], [4, 53, 22], [33, 31], [46, 85], [1]], ![[5, 41, 67, 1], [65, 97], [56, 67, 3, 20], [90, 23], [53, 87], [70, 3, 75, 21]], ![[36, 11, 64, 47], [16, 49], [39, 38, 23, 76], [12, 31], [40, 24], [23, 98, 38, 80]]]
 h' := ![![[55, 50, 20], [72, 36, 17], [97, 84, 88], [73, 22, 74], [56, 70, 43], [100, 15, 61], [0, 1]], ![[6, 50, 81], [92, 71, 55], [37, 86, 20], [47, 14, 100], [95, 0, 15], [59, 95, 17], [55, 50, 20]], ![[0, 1], [62, 95, 29], [49, 32, 94], [53, 65, 28], [41, 31, 43], [92, 92, 23], [6, 50, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 99], []]
 b := ![[], [26, 4, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [1, 86, 40, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67771, -23836, -11312]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-671, -236, -112]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [16, 81, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 65, 71], [8, 37, 32], [0, 1]]
 g := ![![[29, 17, 83], [82, 57, 68], [6, 93, 79], [0, 91], [18, 82], [1]], ![[47, 58, 20, 85], [55, 42, 94, 53], [65, 77, 10, 12], [30, 28], [40, 30], [40, 92, 64, 89]], ![[79, 18, 47, 91], [67, 63, 80, 58], [16, 24, 35, 58], [42, 59], [43, 49], [59, 21, 57, 14]]]
 h' := ![![[51, 65, 71], [27, 14, 17], [7, 19, 45], [97, 48, 64], [71, 28, 20], [87, 22, 59], [0, 1]], ![[8, 37, 32], [98, 32, 78], [1, 56, 27], [94, 63, 8], [70, 60, 50], [68, 49, 37], [51, 65, 71]], ![[0, 1], [40, 57, 8], [6, 28, 31], [78, 95, 31], [21, 15, 33], [83, 32, 7], [8, 37, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 38], []]
 b := ![[], [79, 54, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [16, 81, 44, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-980354, -175306, -1648]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9518, -1702, -16]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-6, -33, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-6, -33, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![101, 74, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-6, -33, 1], ![198, 19, -33], ![-6534, -627, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -74, 107]], ![![-1, -1, 1], ![33, 23, -33], ![-79, -19, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [46, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 106], [0, 1]]
 g := ![![[20, 57], [49, 86], [37], [14, 83], [42], [43, 1]], ![[10, 50], [2, 21], [37], [52, 24], [42], [86, 106]]]
 h' := ![![[43, 106], [100, 59], [14, 34], [105, 95], [23, 46], [55, 91], [0, 1]], ![[0, 1], [69, 48], [85, 73], [17, 12], [75, 61], [9, 16], [43, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [56, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [46, 64, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442, 184, -38]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 28, -38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![33, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![33, 1, 0]] 
 ![![107, 0, 0], ![33, 1, 0], ![88, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![33, 1, 0], ![0, 33, 1], ![198, 25, 33]]]
  hmulB := by decide  
  f := ![![![364, 11, 0], ![-1177, 0, 0]], ![![66, 2, 0], ![-213, 0, 0]], ![![308, 9, 0], ![-996, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 107, 0], ![-88, 0, 107]], ![![0, 1, 0], ![-11, 33, 1], ![-33, 25, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-6, -33, 1]] ![![107, 0, 0], ![33, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![3531, 107, 0]], ![![-642, -3531, 107], ![0, -1070, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![33, 1, 0]]], ![![![-6, -33, 1]], ![![0, -10, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [92, 37, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 35, 23], [40, 73, 86], [0, 1]]
 g := ![![[20, 76, 28], [3, 81], [29, 19, 71], [42, 72, 89], [94, 84], [1]], ![[66, 84, 108, 55], [6, 83], [99, 37, 80, 53], [17, 70, 1, 47], [69, 66], [16, 19, 71, 68]], ![[28, 30, 23, 33], [86, 84], [105, 59, 99, 69], [26, 74, 15, 11], [20, 34], [105, 96, 86, 41]]]
 h' := ![![[13, 35, 23], [30, 38, 79], [57, 16, 9], [60, 63, 17], [34, 71, 31], [17, 72, 53], [0, 1]], ![[40, 73, 86], [106, 46, 101], [107, 95, 44], [84, 55, 74], [1, 84, 81], [71, 36, 75], [13, 35, 23]], ![[0, 1], [33, 25, 38], [73, 107, 56], [57, 100, 18], [107, 63, 106], [58, 1, 90], [40, 73, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 94], []]
 b := ![[], [5, 36, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [92, 37, 56, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2123538, 502054, 61912]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19482, 4606, 568]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [91, 25, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 47, 91], [108, 65, 22], [0, 1]]
 g := ![![[80, 41, 30], [42, 14], [5, 56], [86, 4], [88, 108, 97], [1]], ![[12, 39, 53, 4], [65, 32], [68, 49], [61, 18], [47, 77, 63, 2], [72, 22, 14, 87]], ![[40, 96, 99, 25], [62, 99], [48, 61], [102, 88], [64, 38, 10, 53], [66, 33, 3, 26]]]
 h' := ![![[65, 47, 91], [69, 111, 16], [106, 44, 50], [83, 110, 13], [15, 95, 111], [22, 88, 60], [0, 1]], ![[108, 65, 22], [75, 99, 67], [1, 58, 22], [55, 37, 7], [71, 48, 40], [37, 29, 43], [65, 47, 91]], ![[0, 1], [17, 16, 30], [3, 11, 41], [90, 79, 93], [28, 83, 75], [84, 109, 10], [108, 65, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 53], []]
 b := ![[], [6, 95, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [91, 25, 53, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48590, -6780, 2260]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-430, -60, 20]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-53, 37, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-53, 37, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![74, 37, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-53, 37, 1], ![198, -28, 37], ![7326, 1123, -28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -37, 127]], ![![-1, 0, 1], ![-20, -11, 37], ![74, 17, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [119, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [119, 126], [0, 1]]
 g := ![![[126, 74], [103, 76], [66, 70], [123, 8], [112, 104], [119, 1]], ![[42, 53], [3, 51], [14, 57], [59, 119], [42, 23], [111, 126]]]
 h' := ![![[119, 126], [62, 57], [20, 40], [95, 18], [7, 95], [63, 72], [0, 1]], ![[0, 1], [114, 70], [81, 87], [78, 109], [9, 32], [122, 55], [119, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [74, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [119, 8, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![911, 900, 117]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -27, 117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-37, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-37, 1, 0]] 
 ![![127, 0, 0], ![90, 1, 0], ![28, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-37, 1, 0], ![0, -37, 1], ![198, 25, -37]]]
  hmulB := by decide  
  f := ![![![4256, -115, 0], ![14605, 0, 0]], ![![2998, -81, 0], ![10288, 0, 0]], ![![936, -25, 0], ![3212, 1, 0]]]
  g := ![![![1, 0, 0], ![-90, 127, 0], ![-28, 0, 127]], ![![-1, 1, 0], ![26, -37, 1], ![-8, 25, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-53, 37, 1]] ![![127, 0, 0], ![-37, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4699, 127, 0]], ![![-6731, 4699, 127], ![2159, -1397, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-37, 1, 0]]], ![![![-53, 37, 1]], ![![17, -11, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-20, -23, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-20, -23, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![111, 108, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-20, -23, 1], ![198, 5, -23], ![-4554, -377, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -108, 131]], ![![-1, -1, 1], ![21, 19, -23], ![-39, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [9, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 130], [0, 1]]
 g := ![![[117, 102], [39, 34], [77], [101], [46], [25], [1]], ![[0, 29], [0, 97], [77], [101], [46], [25], [1]]]
 h' := ![![[126, 130], [42, 87], [8, 54], [35, 83], [17, 25], [118, 96], [122, 126], [0, 1]], ![[0, 1], [0, 44], [0, 77], [13, 48], [23, 106], [31, 35], [16, 5], [126, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [60, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [9, 5, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7897, -298, 218]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-245, -182, 218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![23, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![23, 1, 0]] 
 ![![131, 0, 0], ![23, 1, 0], ![126, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![23, 1, 0], ![0, 23, 1], ![198, 25, 23]]]
  hmulB := by decide  
  f := ![![![1082, 47, 0], ![-6157, 0, 0]], ![![184, 8, 0], ![-1047, 0, 0]], ![![1040, 45, 0], ![-5918, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 131, 0], ![-126, 0, 131]], ![![0, 1, 0], ![-5, 23, 1], ![-25, 25, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-20, -23, 1]] ![![131, 0, 0], ![23, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![3013, 131, 0]], ![![-2620, -3013, 131], ![-262, -524, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![23, 1, 0]]], ![![![-20, -23, 1]], ![![-2, -4, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [19, 124, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 125, 19], [75, 11, 118], [0, 1]]
 g := ![![[93, 37, 15], [43, 121], [57, 136], [114, 24, 61], [26, 7], [89, 1], []], ![[125, 24, 97, 74], [133, 133], [100, 101], [113, 46, 103, 100], [2, 87], [66, 121], [26, 87]], ![[12, 99, 109, 122], [121, 101], [118, 112], [111, 8, 134, 9], [50, 2], [44, 7], [64, 87]]]
 h' := ![![[14, 125, 19], [21, 14, 120], [4, 48, 11], [26, 39, 37], [71, 93, 91], [90, 42, 125], [0, 0, 1], [0, 1]], ![[75, 11, 118], [77, 88, 79], [1, 32, 74], [95, 95, 52], [11, 28, 28], [7, 128, 118], [113, 130, 11], [14, 125, 19]], ![[0, 1], [98, 35, 75], [43, 57, 52], [40, 3, 48], [5, 16, 18], [63, 104, 31], [25, 7, 125], [75, 11, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 106], []]
 b := ![[], [28, 16, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [19, 124, 48, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1644, 19591, 4247]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 143, 31]
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



lemma PB283I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB283I2 : PrimesBelowBoundCertificateInterval O 79 137 283 where
  m := 11
  g := ![1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB283I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
      exact NI97N2
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
  β := ![I97N0, I97N1, I97N2, I107N1, I127N1, I131N1]
  Il := ![[], [], [I97N0, I97N1, I97N2], [], [], [I107N1], [], [], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
