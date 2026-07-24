
import IdealArithmetic.Examples.NF3_1_466627_1.RI3_1_466627_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-33, -16, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-33, -16, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![50, 67, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-33, -16, 1], ![412, 74, -15], ![-6180, -1193, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -67, 83]], ![![-1, -1, 1], ![14, 13, -15], ![-110, -62, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [30, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 82], [0, 1]]
 g := ![![[50, 36], [32, 33], [36], [63], [61, 36], [1]], ![[0, 47], [0, 50], [36], [63], [11, 47], [1]]]
 h' := ![![[77, 82], [36, 6], [62, 38], [35, 6], [79, 35], [53, 77], [0, 1]], ![[0, 1], [0, 77], [0, 45], [82, 77], [35, 48], [6, 6], [77, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [30, 6, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1266, 727, 105]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -76, 105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![15, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![15, 1, 0]] 
 ![![83, 0, 0], ![15, 1, 0], ![24, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![15, 1, 0], ![0, 15, 1], ![412, 107, 16]]]
  hmulB := by decide  
  f := ![![![751, 50, 0], ![-4150, 0, 0]], ![![135, 9, 0], ![-746, 0, 0]], ![![198, 13, 0], ![-1094, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 83, 0], ![-24, 0, 83]], ![![0, 1, 0], ![-3, 15, 1], ![-19, 107, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-33, -16, 1]] ![![83, 0, 0], ![15, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1245, 83, 0]], ![![-2739, -1328, 83], ![-83, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![15, 1, 0]]], ![![![-33, -16, 1]], ![![-1, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-38, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-38, 1, 0]] 
 ![![89, 0, 0], ![51, 1, 0], ![69, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-38, 1, 0], ![0, -38, 1], ![412, 107, -37]]]
  hmulB := by decide  
  f := ![![![3345, -88, 0], ![7832, 0, 0]], ![![1939, -51, 0], ![4540, 0, 0]], ![![2601, -68, 0], ![6090, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 89, 0], ![-69, 0, 89]], ![![-1, 1, 0], ![21, -38, 1], ![-28, 107, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-26, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-26, 1, 0]] 
 ![![89, 0, 0], ![63, 1, 0], ![36, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-26, 1, 0], ![0, -26, 1], ![412, 107, -25]]]
  hmulB := by decide  
  f := ![![![885, -34, 0], ![3026, 0, 0]], ![![651, -25, 0], ![2226, 0, 0]], ![![372, -14, 0], ![1272, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 89, 0], ![-36, 0, 89]], ![![-1, 1, 0], ![18, -26, 1], ![-61, 107, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-38, 1, 0]] ![![89, 0, 0], ![-26, 1, 0]]
  ![![89, 0, 0], ![-80, 25, 1]] where
 M := ![![![7921, 0, 0], ![-2314, 89, 0]], ![![-3382, 89, 0], ![988, -64, 1]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![54, -24, -1], ![89, 0, 0]]], ![![![42, -24, -1], ![89, 0, 0]], ![![12, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-80, 25, 1]] ![![89, 0, 0], ![-26, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2314, 89, 0]], ![![-7120, 2225, 89], ![2492, -623, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-26, 1, 0]]], ![![![-80, 25, 1]], ![![28, -7, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-114, 9, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-114, 9, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![80, 9, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-114, 9, 1], ![412, -7, 10], ![4120, 1482, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -9, 97]], ![![-2, 0, 1], ![-4, -1, 10], ![40, 15, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [89, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 96], [0, 1]]
 g := ![![[33, 12], [35], [89], [88], [66], [70, 1]], ![[0, 85], [35], [89], [88], [66], [43, 96]]]
 h' := ![![[70, 96], [55, 20], [39, 36], [43, 34], [42, 31], [75, 58], [0, 1]], ![[0, 1], [0, 77], [37, 61], [95, 63], [78, 66], [61, 39], [70, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [60, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [89, 27, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1173, 3337, 1039]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-869, -62, 1039]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-10, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-10, 1, 0]] 
 ![![97, 0, 0], ![87, 1, 0], ![94, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-10, 1, 0], ![0, -10, 1], ![412, 107, -9]]]
  hmulB := by decide  
  f := ![![![741, -74, 0], ![7178, 0, 0]], ![![651, -65, 0], ![6306, 0, 0]], ![![702, -70, 0], ![6800, 1, 0]]]
  g := ![![![1, 0, 0], ![-87, 97, 0], ![-94, 0, 97]], ![![-1, 1, 0], ![8, -10, 1], ![-83, 107, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-114, 9, 1]] ![![97, 0, 0], ![-10, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-970, 97, 0]], ![![-11058, 873, 97], ![1552, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-10, 1, 0]]], ![![![-114, 9, 1]], ![![16, -1, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-91, 20, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-91, 20, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![10, 20, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-91, 20, 1], ![412, 16, 21], ![8652, 2659, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -20, 101]], ![![-1, 0, 1], ![2, -4, 21], ![82, 19, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [9, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 100], [0, 1]]
 g := ![![[25, 45], [65], [96, 31], [19], [23], [78, 1]], ![[0, 56], [65], [90, 70], [19], [23], [55, 100]]]
 h' := ![![[78, 100], [26, 67], [45, 60], [27, 58], [20, 25], [5, 15], [0, 1]], ![[0, 1], [0, 34], [79, 41], [6, 43], [51, 76], [64, 86], [78, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [44, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [9, 23, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2221, 200, 212]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -40, 212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-21, 1, 0]] 
 ![![101, 0, 0], ![80, 1, 0], ![64, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-21, 1, 0], ![0, -21, 1], ![412, 107, -20]]]
  hmulB := by decide  
  f := ![![![1786, -85, 0], ![8585, 0, 0]], ![![1408, -67, 0], ![6768, 0, 0]], ![![1160, -55, 0], ![5576, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 101, 0], ![-64, 0, 101]], ![![-1, 1, 0], ![16, -21, 1], ![-68, 107, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-91, 20, 1]] ![![101, 0, 0], ![-21, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2121, 101, 0]], ![![-9191, 2020, 101], ![2323, -404, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-21, 1, 0]]], ![![![-91, 20, 1]], ![![23, -4, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![0, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![0, 1, 0]] 
 ![![103, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![0, 1, 0], ![0, 0, 1], ![412, 107, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![0, 1, 0], ![0, 0, 1], ![4, 107, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![14, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![14, 1, 0]] 
 ![![103, 0, 0], ![14, 1, 0], ![10, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![14, 1, 0], ![0, 14, 1], ![412, 107, 15]]]
  hmulB := by decide  
  f := ![![![883, 63, 0], ![-6489, 0, 0]], ![![98, 7, 0], ![-720, 0, 0]], ![![86, 6, 0], ![-632, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 103, 0], ![-10, 0, 103]], ![![0, 1, 0], ![-2, 14, 1], ![-12, 107, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-15, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-15, 1, 0]] 
 ![![103, 0, 0], ![88, 1, 0], ![84, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-15, 1, 0], ![0, -15, 1], ![412, 107, -14]]]
  hmulB := by decide  
  f := ![![![946, -63, 0], ![6489, 0, 0]], ![![826, -55, 0], ![5666, 0, 0]], ![![768, -51, 0], ![5268, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 103, 0], ![-84, 0, 103]], ![![-1, 1, 0], ![12, -15, 1], ![-76, 107, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![0, 1, 0]] ![![103, 0, 0], ![14, 1, 0]]
  ![![103, 0, 0], ![-103, 14, 1]] where
 M := ![![![10609, 0, 0], ![1442, 103, 0]], ![![0, 103, 0], ![0, 14, 1]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![103, -13, -1], ![103, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-103, 14, 1]] ![![103, 0, 0], ![-15, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1545, 103, 0]], ![![-10609, 1442, 103], ![1957, -206, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-15, 1, 0]]], ![![![-103, 14, 1]], ![![19, -2, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![35, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![35, 1, 0]] 
 ![![107, 0, 0], ![35, 1, 0], ![59, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![35, 1, 0], ![0, 35, 1], ![412, 107, 36]]]
  hmulB := by decide  
  f := ![![![1261, 36, 0], ![-3852, 0, 0]], ![![385, 11, 0], ![-1176, 0, 0]], ![![677, 19, 0], ![-2068, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 107, 0], ![-59, 0, 107]], ![![0, 1, 0], ![-12, 35, 1], ![-51, 107, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![36, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![36, 1, 0]] 
 ![![107, 0, 0], ![36, 1, 0], ![95, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![36, 1, 0], ![0, 36, 1], ![412, 107, 37]]]
  hmulB := by decide  
  f := ![![![37, 1, 0], ![-107, 0, 0]], ![![-36, -1, 0], ![108, 0, 0]], ![![49, 1, 0], ![-143, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 107, 0], ![-95, 0, 107]], ![![0, 1, 0], ![-13, 36, 1], ![-65, 107, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![35, 1, 0]] ![![107, 0, 0], ![35, 1, 0]]
  ![![107, 0, 0], ![-59, -37, 1]] where
 M := ![![![11449, 0, 0], ![3745, 107, 0]], ![![3745, 107, 0], ![1225, 70, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![35, 1, 0], ![0, 0, 0]]], ![![![35, 1, 0], ![0, 0, 0]], ![![12, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-59, -37, 1]] ![![107, 0, 0], ![36, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![3852, 107, 0]], ![![-6313, -3959, 107], ![-1712, -1284, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![36, 1, 0]]], ![![![-59, -37, 1]], ![![-16, -12, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-53, -17, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-53, -17, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![56, 92, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-53, -17, 1], ![412, 54, -16], ![-6592, -1300, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -92, 109]], ![![-1, -1, 1], ![12, 14, -16], ![-80, -44, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [59, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 108], [0, 1]]
 g := ![![[29, 102], [102], [26, 12], [72, 105], [3], [33, 1]], ![[16, 7], [102], [95, 97], [49, 4], [3], [66, 108]]]
 h' := ![![[33, 108], [41, 59], [101, 50], [3, 11], [48, 43], [15, 49], [0, 1]], ![[0, 1], [26, 50], [7, 59], [39, 98], [50, 66], [106, 60], [33, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [4, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [59, 76, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1372, 4107, 733]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-364, -581, 733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![16, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![16, 1, 0]] 
 ![![109, 0, 0], ![16, 1, 0], ![71, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![16, 1, 0], ![0, 16, 1], ![412, 107, 17]]]
  hmulB := by decide  
  f := ![![![945, 59, 0], ![-6431, 0, 0]], ![![112, 7, 0], ![-762, 0, 0]], ![![627, 39, 0], ![-4267, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 109, 0], ![-71, 0, 109]], ![![0, 1, 0], ![-3, 16, 1], ![-23, 107, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-53, -17, 1]] ![![109, 0, 0], ![16, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![1744, 109, 0]], ![![-5777, -1853, 109], ![-436, -218, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![16, 1, 0]]], ![![![-53, -17, 1]], ![![-4, -2, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [37, 22, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 2, 4], [88, 110, 109], [0, 1]]
 g := ![![[109, 70, 2], [76, 77], [47, 77], [60, 112], [93, 108, 100], [1]], ![[18, 42, 92, 44], [93, 53], [5, 104], [29, 4], [68, 42, 7, 100], [38, 109, 58, 64]], ![[75, 51, 61, 100], [59, 56], [75, 104], [32, 63], [14, 69, 5, 13], [53, 57, 7, 49]]]
 h' := ![![[35, 2, 4], [73, 16, 51], [25, 93, 23], [42, 85, 23], [62, 73, 98], [76, 91, 10], [0, 1]], ![[88, 110, 109], [49, 84, 24], [103, 61, 77], [66, 45, 45], [110, 31, 111], [111, 108, 108], [35, 2, 4]], ![[0, 1], [62, 13, 38], [18, 72, 13], [9, 96, 45], [17, 9, 17], [42, 27, 108], [88, 110, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 87], []]
 b := ![[], [27, 102, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [37, 22, 103, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-266115, -73676, -3390]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2355, -652, -30]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![127, 0, 0], ![3, 1, 0], ![118, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![412, 107, 4]]]
  hmulB := by decide  
  f := ![![![-95, -4, 1]], ![![1, 0, 0]], ![![-98, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-3, 107, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![35, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![35, 1, 0]] 
 ![![127, 0, 0], ![35, 1, 0], ![45, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![35, 1, 0], ![0, 35, 1], ![412, 107, 36]]]
  hmulB := by decide  
  f := ![![![2031, 58, 0], ![-7366, 0, 0]], ![![525, 15, 0], ![-1904, 0, 0]], ![![675, 19, 0], ![-2448, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 127, 0], ![-45, 0, 127]], ![![0, 1, 0], ![-10, 35, 1], ![-39, 107, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-39, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-39, 1, 0]] 
 ![![127, 0, 0], ![88, 1, 0], ![3, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-39, 1, 0], ![0, -39, 1], ![412, 107, -38]]]
  hmulB := by decide  
  f := ![![![4759, -122, 0], ![15494, 0, 0]], ![![3316, -85, 0], ![10796, 0, 0]], ![![129, -3, 0], ![420, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 127, 0], ![-3, 0, 127]], ![![-1, 1, 0], ![27, -39, 1], ![-70, 107, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![127, 0, 0], ![35, 1, 0]]
  ![![127, 0, 0], ![-22, 38, 1]] where
 M := ![![![381, 127, 0], ![105, 38, 1]]]
 hmul := by decide  
 g := ![![![![3, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-22, 38, 1]] ![![127, 0, 0], ![-39, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4953, 127, 0]], ![![-2794, 4826, 127], ![1270, -1397, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-39, 1, 0]]], ![![![-22, 38, 1]], ![![10, -11, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-66, -39, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-66, -39, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![65, 92, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-66, -39, 1], ![412, 41, -38], ![-15656, -3654, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -92, 131]], ![![-1, -1, 1], ![22, 27, -38], ![-121, -30, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [43, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 130], [0, 1]]
 g := ![![[57, 64], [68, 12], [121], [34], [100], [3], [1]], ![[0, 67], [0, 119], [121], [34], [100], [3], [1]]]
 h' := ![![[38, 130], [89, 8], [6, 55], [121, 11], [50, 54], [17, 121], [88, 38], [0, 1]], ![[0, 1], [0, 123], [0, 76], [15, 120], [6, 77], [30, 10], [91, 93], [38, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [130, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [43, 93, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16205, 6390, 602]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-175, -374, 602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![38, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![38, 1, 0]] 
 ![![131, 0, 0], ![38, 1, 0], ![128, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![38, 1, 0], ![0, 38, 1], ![412, 107, 39]]]
  hmulB := by decide  
  f := ![![![2205, 58, 0], ![-7598, 0, 0]], ![![646, 17, 0], ![-2226, 0, 0]], ![![2140, 56, 0], ![-7374, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 131, 0], ![-128, 0, 131]], ![![0, 1, 0], ![-12, 38, 1], ![-66, 107, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-66, -39, 1]] ![![131, 0, 0], ![38, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![4978, 131, 0]], ![![-8646, -5109, 131], ![-2096, -1441, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![38, 1, 0]]], ![![![-66, -39, 1]], ![![-16, -11, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-56, 21, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-56, 21, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![81, 21, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-56, 21, 1], ![412, 51, 22], ![9064, 2766, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -21, 137]], ![![-1, 0, 1], ![-10, -3, 22], ![23, 9, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [132, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 136], [0, 1]]
 g := ![![[123, 36], [25], [25], [76, 133], [130], [105], [1]], ![[69, 101], [25], [25], [82, 4], [130], [105], [1]]]
 h' := ![![[67, 136], [88, 131], [127, 132], [106, 5], [106, 74], [2, 33], [5, 67], [0, 1]], ![[0, 1], [97, 6], [66, 5], [30, 132], [132, 63], [21, 104], [110, 70], [67, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [120, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [132, 70, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1997, 81, 43]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, -6, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-22, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-22, 1, 0]] 
 ![![137, 0, 0], ![115, 1, 0], ![64, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-22, 1, 0], ![0, -22, 1], ![412, 107, -21]]]
  hmulB := by decide  
  f := ![![![2047, -93, 0], ![12741, 0, 0]], ![![1717, -78, 0], ![10687, 0, 0]], ![![972, -44, 0], ![6050, 1, 0]]]
  g := ![![![1, 0, 0], ![-115, 137, 0], ![-64, 0, 137]], ![![-1, 1, 0], ![18, -22, 1], ![-77, 107, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-56, 21, 1]] ![![137, 0, 0], ![-22, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3014, 137, 0]], ![![-7672, 2877, 137], ![1644, -411, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-22, 1, 0]]], ![![![-56, 21, 1]], ![![12, -3, 0]]]]
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


lemma PB194I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB194I2 : PrimesBelowBoundCertificateInterval O 79 137 194 where
  m := 11
  g := ![2, 3, 2, 2, 3, 3, 2, 1, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB194I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
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
      exact NI89N1
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
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
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
  β := ![I83N1, I89N0, I89N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N0, I107N1, I109N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N0, I107N0, I107N1], [I109N1], [], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
