
import IdealArithmetic.Examples.NF3_1_271660_2.RI3_1_271660_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-59, 3, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-59, 3, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![24, 3, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-59, 3, 1], ![238, 9, 3], ![714, 442, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -3, 83]], ![![-1, 0, 1], ![2, 0, 3], ![6, 5, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [30, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 82], [0, 1]]
 g := ![![[65, 36], [58, 7], [26], [28], [22, 21], [1]], ![[0, 47], [20, 76], [26], [28], [74, 62], [1]]]
 h' := ![![[42, 82], [3, 77], [3, 16], [6, 21], [4, 32], [53, 42], [0, 1]], ![[0, 1], [0, 6], [11, 67], [58, 62], [20, 51], [74, 41], [42, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [70, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [30, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![506, 333, 28]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 3, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-3, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-3, 1, 0]] 
 ![![83, 0, 0], ![80, 1, 0], ![74, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-3, 1, 0], ![0, -3, 1], ![238, 68, -3]]]
  hmulB := by decide  
  f := ![![![91, -30, 0], ![2490, 0, 0]], ![![88, -29, 0], ![2408, 0, 0]], ![![82, -27, 0], ![2244, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 83, 0], ![-74, 0, 83]], ![![-1, 1, 0], ![2, -3, 1], ![-60, 68, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-59, 3, 1]] ![![83, 0, 0], ![-3, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-249, 83, 0]], ![![-4897, 249, 83], ![415, 0, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-3, 1, 0]]], ![![![-59, 3, 1]], ![![5, 0, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [17, 48, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 37, 56], [24, 51, 33], [0, 1]]
 g := ![![[9, 34, 64], [27, 18], [74, 8], [46, 24, 80], [39, 49, 1], []], ![[41, 58, 36, 41], [73, 22], [22, 21], [77, 11, 42, 83], [42, 80, 38, 52], [11, 21]], ![[3, 0, 78, 62], [86, 9], [69, 36], [70, 34, 16, 56], [14, 51, 31, 54], [34, 21]]]
 h' := ![![[25, 37, 56], [35, 27, 81], [82, 68, 14], [19, 52, 50], [49, 54, 76], [0, 0, 1], [0, 1]], ![[24, 51, 33], [54, 43, 36], [82, 6, 72], [79, 67, 33], [66, 44, 47], [82, 75, 51], [25, 37, 56]], ![[0, 1], [76, 19, 61], [84, 15, 3], [10, 59, 6], [36, 80, 55], [87, 14, 37], [24, 51, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 17], []]
 b := ![[], [82, 40, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [17, 48, 40, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![547884, 681384, 137149]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6156, 7656, 1541]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-56, 20, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-56, 20, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![41, 20, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-56, 20, 1], ![238, 12, 20], ![4760, 1598, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -20, 97]], ![![-1, 0, 1], ![-6, -4, 20], ![44, 14, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [43, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 96], [0, 1]]
 g := ![![[74, 88], [96], [96], [9], [50], [19, 1]], ![[0, 9], [96], [96], [9], [50], [38, 96]]]
 h' := ![![[19, 96], [7, 66], [35, 22], [63, 75], [16, 94], [56, 27], [0, 1]], ![[0, 1], [0, 31], [65, 75], [33, 22], [56, 3], [84, 70], [19, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [35, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [43, 78, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1329, 52, 119]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -24, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-20, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-20, 1, 0]] 
 ![![97, 0, 0], ![77, 1, 0], ![85, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-20, 1, 0], ![0, -20, 1], ![238, 68, -20]]]
  hmulB := by decide  
  f := ![![![881, -44, 0], ![4268, 0, 0]], ![![701, -35, 0], ![3396, 0, 0]], ![![765, -38, 0], ![3706, 1, 0]]]
  g := ![![![1, 0, 0], ![-77, 97, 0], ![-85, 0, 97]], ![![-1, 1, 0], ![15, -20, 1], ![-34, 68, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-56, 20, 1]] ![![97, 0, 0], ![-20, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1940, 97, 0]], ![![-5432, 1940, 97], ![1358, -388, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-20, 1, 0]]], ![![![-56, 20, 1]], ![![14, -4, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [70, 53, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 68, 20], [51, 32, 81], [0, 1]]
 g := ![![[70, 67, 14], [71, 25], [83, 52, 21], [63, 56], [4, 1], [1]], ![[98, 93, 1, 65], [34, 78], [30, 89, 16, 65], [27, 70], [5, 58], [29, 38, 72, 21]], ![[72, 20, 67, 37], [68, 88], [91, 5, 47, 96], [55, 30], [55, 21], [23, 24, 41, 80]]]
 h' := ![![[49, 68, 20], [61, 95, 69], [48, 50, 5], [3, 12, 83], [75, 68, 64], [31, 48, 100], [0, 1]], ![[51, 32, 81], [45, 51, 68], [100, 30, 49], [53, 20, 68], [23, 70, 75], [75, 100, 19], [49, 68, 20]], ![[0, 1], [9, 56, 65], [27, 21, 47], [13, 69, 51], [5, 64, 63], [44, 54, 83], [51, 32, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 31], []]
 b := ![[], [89, 71, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [70, 53, 1, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1097769, -744168, -116756]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10869, -7368, -1156]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-4, -8, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-4, -8, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![99, 95, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-4, -8, 1], ![238, 64, -8], ![-1904, -306, 64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -95, 103]], ![![-1, -1, 1], ![10, 8, -8], ![-80, -62, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [83, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 102], [0, 1]]
 g := ![![[99, 36], [79, 76], [8, 76], [15], [23], [23, 1]], ![[0, 67], [76, 27], [5, 27], [15], [23], [46, 102]]]
 h' := ![![[23, 102], [35, 97], [57, 73], [74, 30], [86, 85], [48, 34], [0, 1]], ![[0, 1], [0, 6], [88, 30], [43, 73], [84, 18], [6, 69], [23, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [89, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [83, 80, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![559, 294, -11]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 13, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![8, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![8, 1, 0]] 
 ![![103, 0, 0], ![8, 1, 0], ![39, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![8, 1, 0], ![0, 8, 1], ![238, 68, 8]]]
  hmulB := by decide  
  f := ![![![89, 11, 0], ![-1133, 0, 0]], ![![-8, -1, 0], ![104, 0, 0]], ![![25, 3, 0], ![-317, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 103, 0], ![-39, 0, 103]], ![![0, 1, 0], ![-1, 8, 1], ![-6, 68, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-4, -8, 1]] ![![103, 0, 0], ![8, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![824, 103, 0]], ![![-412, -824, 103], ![206, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![8, 1, 0]]], ![![![-4, -8, 1]], ![![2, 0, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [70, 62, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 25, 48], [29, 81, 59], [0, 1]]
 g := ![![[29, 97, 39], [25, 52, 3], [1, 41], [95, 76, 56], [17, 61], [1]], ![[91, 99, 105, 57], [32, 7, 81, 52], [104, 81], [37, 87, 23, 69], [31, 10], [4, 91, 21, 61]], ![[106, 90, 78, 94], [56, 93, 57, 63], [19, 11], [37, 66, 11, 73], [100, 105], [86, 55, 22, 46]]]
 h' := ![![[3, 25, 48], [69, 88, 50], [79, 82, 18], [91, 73, 24], [72, 39, 85], [37, 45, 32], [0, 1]], ![[29, 81, 59], [10, 64, 35], [106, 27, 44], [18, 55, 98], [100, 83, 90], [68, 49, 44], [3, 25, 48]], ![[0, 1], [8, 62, 22], [44, 105, 45], [25, 86, 92], [3, 92, 39], [72, 13, 31], [29, 81, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 39], []]
 b := ![[], [88, 34, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [70, 62, 75, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3317214, 1244303, 125511]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31002, 11629, 1173]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-485878641, -189282550, -19657610]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-485878641, -189282550, -19657610]] 
 ![![109, 0, 0], ![0, 109, 0], ![70, 47, 1]] where
  M :=![![![-485878641, -189282550, -19657610], ![-4678511180, -1822596121, -189282550], ![-45049246900, -17549724580, -1822596121]]]
  hmulB := by decide  
  f := ![![![145251, 17750, -3410]], ![![-811580, -86629, 17750]], ![![-217910, -22327, 4669]]]
  g := ![![![8166551, 6739680, -19657610], ![78635480, 64896181, -189282550], ![757178730, 624883423, -1822596121]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [62, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 108], [0, 1]]
 g := ![![[106, 1], [64], [87, 9], [81, 27], [34], [77, 1]], ![[74, 108], [64], [17, 100], [89, 82], [34], [45, 108]]]
 h' := ![![[77, 108], [40, 108], [56, 101], [101, 106], [11, 38], [22, 90], [0, 1]], ![[0, 1], [72, 1], [94, 8], [88, 3], [103, 71], [85, 19], [77, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [73, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [62, 32, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1397, -80, 47]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -21, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145251, 17750, -3410]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![145251, 17750, -3410]] 
 ![![109, 0, 0], ![62, 1, 0], ![80, 0, 1]] where
  M :=![![![145251, 17750, -3410], ![-811580, -86629, 17750], ![4224500, 395420, -86629]]]
  hmulB := by decide  
  f := ![![![-485878641, -189282550, -19657610]], ![![-319293458, -124386369, -12917930]], ![![-769904020, -299929620, -31148669]]]
  g := ![![![-6261, 17750, -3410], ![28802, -86629, 17750], ![-122580, 395420, -86629]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-485878641, -189282550, -19657610]] ![![145251, 17750, -3410]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244353, 95192, 9886]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![244353, 95192, 9886]] 
 ![![113, 0, 0], ![24, 1, 0], ![102, 0, 1]] where
  M :=![![![244353, 95192, 9886], ![2352868, 916601, 95192], ![22655696, 8825924, 916601]]]
  hmulB := by decide  
  f := ![![![35793, 2272, -622]], ![![6292, 425, -112]], ![![37094, 2108, -619]]]
  g := ![![![-26979, 95192, 9886], ![-259780, 916601, 95192], ![-2501414, 8825924, 916601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![26, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![26, 1, 0]] 
 ![![113, 0, 0], ![26, 1, 0], ![2, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![26, 1, 0], ![0, 26, 1], ![238, 68, 26]]]
  hmulB := by decide  
  f := ![![![1561, 60, 0], ![-6780, 0, 0]], ![![338, 13, 0], ![-1468, 0, 0]], ![![6, 0, 0], ![-26, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 113, 0], ![-2, 0, 113]], ![![0, 1, 0], ![-6, 26, 1], ![-14, 68, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-50, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-50, 1, 0]] 
 ![![113, 0, 0], ![63, 1, 0], ![99, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-50, 1, 0], ![0, -50, 1], ![238, 68, -50]]]
  hmulB := by decide  
  f := ![![![3701, -74, 0], ![8362, 0, 0]], ![![2051, -41, 0], ![4634, 0, 0]], ![![3223, -64, 0], ![7282, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 113, 0], ![-99, 0, 113]], ![![-1, 1, 0], ![27, -50, 1], ![8, 68, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![244353, 95192, 9886]] ![![113, 0, 0], ![26, 1, 0]]
  ![![113, 0, 0], ![-54, 50, 1]] where
 M := ![![![27611889, 10756696, 1117118], ![8706046, 3391593, 352228]]]
 hmul := by decide  
 g := ![![![![219351, 118342, 10349], ![-52319, 0, 0]], ![![69164, 37311, 3263], ![-16491, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-54, 50, 1]] ![![113, 0, 0], ![-50, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5650, 113, 0]], ![![-6102, 5650, 113], ![2938, -2486, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-50, 1, 0]]], ![![![-54, 50, 1]], ![![26, -22, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [93, 109, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 84, 9], [72, 42, 118], [0, 1]]
 g := ![![[103, 88, 113], [60, 78, 72], [81, 46, 11], [89, 41, 88], [68, 3, 70], [1]], ![[52, 126, 31, 72], [89, 74, 44, 115], [50, 116, 87, 122], [126, 25, 96, 79], [75, 5, 39, 76], [37, 120, 6, 94]], ![[56, 73, 34, 116], [101, 115, 45, 29], [2, 15, 73, 92], [25, 58, 116, 53], [26, 95, 19, 58], [49, 16, 5, 33]]]
 h' := ![![[73, 84, 9], [8, 125, 42], [87, 77, 96], [105, 116, 30], [26, 69, 56], [34, 18, 18], [0, 1]], ![[72, 42, 118], [28, 120, 95], [64, 105, 26], [110, 80, 18], [35, 84, 52], [4, 57, 29], [73, 84, 9]], ![[0, 1], [86, 9, 117], [115, 72, 5], [34, 58, 79], [83, 101, 19], [10, 52, 80], [72, 42, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 69], []]
 b := ![[], [19, 65, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [93, 109, 109, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![751459, 449453, 70231]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5917, 3539, 553]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [130, 90, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 17, 91], [5, 113, 40], [0, 1]]
 g := ![![[11, 6, 60], [52, 119, 9], [87, 5], [117, 16], [90, 46], [16, 1], []], ![[22, 11, 115, 5], [5, 32, 67, 34], [128, 100], [23, 107], [79, 12], [100, 62], [5, 28]], ![[86, 128, 63, 85], [90, 84, 104, 118], [32, 38], [69, 129], [110, 7], [99, 27], [56, 28]]]
 h' := ![![[11, 17, 91], [52, 63, 86], [63, 105, 3], [99, 3, 23], [84, 1, 127], [16, 2, 35], [0, 0, 1], [0, 1]], ![[5, 113, 40], [53, 87, 124], [24, 69, 69], [17, 126, 121], [115, 78, 32], [125, 57, 76], [126, 83, 113], [11, 17, 91]], ![[0, 1], [128, 112, 52], [45, 88, 59], [12, 2, 118], [27, 52, 103], [110, 72, 20], [81, 48, 17], [5, 113, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 100], []]
 b := ![[], [11, 95, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [130, 90, 115, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2878070, -440684, 95368]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21970, -3364, 728]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [37, 134, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 6, 16], [117, 130, 121], [0, 1]]
 g := ![![[91, 49, 11], [13, 73], [58, 50], [119, 50, 60], [13, 38], [38, 1], []], ![[123, 87, 106, 128], [1, 8], [36, 38], [49, 58, 14, 22], [74, 64], [33, 49], [56, 119]], ![[48, 3, 61, 39], [112, 93], [15, 56], [25, 87, 70, 129], [60, 101], [133, 36], [88, 119]]]
 h' := ![![[58, 6, 16], [83, 32, 82], [133, 40, 22], [118, 63, 18], [130, 76, 34], [101, 77, 77], [0, 0, 1], [0, 1]], ![[117, 130, 121], [64, 23, 75], [52, 61, 75], [39, 107, 60], [105, 5, 19], [68, 41, 8], [59, 23, 130], [58, 6, 16]], ![[0, 1], [69, 82, 117], [69, 36, 40], [58, 104, 59], [9, 56, 84], [41, 19, 52], [21, 114, 6], [117, 130, 121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 46], []]
 b := ![[], [47, 56, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [37, 134, 99, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37127, 30003, 16851]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-271, 219, 123]
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



lemma PB148I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB148I2 : PrimesBelowBoundCertificateInterval O 79 137 148 where
  m := 11
  g := ![2, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB148I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![2571353]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I97N1, I103N1, I109N1, I113N0, I113N1, I113N2]
  Il := ![[I83N1], [], [I97N1], [], [I103N1], [], [I109N1], [I113N0, I113N1, I113N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
