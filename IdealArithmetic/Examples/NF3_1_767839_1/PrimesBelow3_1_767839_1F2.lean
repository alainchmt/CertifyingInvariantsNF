
import IdealArithmetic.Examples.NF3_1_767839_1.RI3_1_767839_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [18, 29, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 29, 37], [80, 53, 46], [0, 1]]
 g := ![![[1, 53, 12], [9, 47, 78], [16, 21], [54, 17], [80, 62, 1], []], ![[71, 65, 79, 29], [28, 35, 42, 7], [26, 33], [80, 64], [47, 77, 66, 17], [40, 41]], ![[29, 66, 73, 50], [69, 64, 14, 5], [51, 16], [78, 75], [0, 13, 29, 8], [31, 41]]]
 h' := ![![[65, 29, 37], [4, 50, 57], [24, 23, 24], [35, 42, 42], [54, 50, 73], [0, 0, 1], [0, 1]], ![[80, 53, 46], [21, 5, 57], [66, 28, 48], [77, 79, 45], [43, 77, 75], [19, 46, 53], [65, 29, 37]], ![[0, 1], [18, 28, 52], [59, 32, 11], [8, 45, 79], [82, 39, 18], [32, 37, 29], [80, 53, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 39], []]
 b := ![[], [13, 80, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [18, 29, 21, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3237, 8217, -1992]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, 99, -24]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [24, 12, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 14, 29], [78, 74, 60], [0, 1]]
 g := ![![[0, 69, 49], [71, 72], [73, 80], [79, 19, 84], [20, 78, 1], []], ![[19, 24, 28, 41], [40, 78], [67, 69], [20, 54, 12, 48], [8, 77, 5, 28], [16, 40]], ![[83, 9, 34, 27], [64, 55], [29, 21], [73, 7, 42, 35], [50, 4, 9, 12], [74, 40]]]
 h' := ![![[0, 14, 29], [54, 18, 7], [45, 17, 28], [62, 88, 13], [54, 24, 66], [0, 0, 1], [0, 1]], ![[78, 74, 60], [36, 20, 61], [62, 22, 73], [54, 51, 43], [75, 43, 62], [61, 5, 74], [0, 14, 29]], ![[0, 1], [19, 51, 21], [65, 50, 77], [7, 39, 33], [30, 22, 50], [36, 84, 14], [78, 74, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 86], []]
 b := ![[], [50, 13, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [24, 12, 11, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![892047, -291386, 14240]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10023, -3274, 160]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![37, -43, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![37, -43, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![37, 54, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![37, -43, 1], ![155, 6, -43], ![-6665, 1488, 6]]]
  hmulB := by decide  
  f := ![![![-36, 43, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -54, 97]], ![![0, -1, 1], ![18, 24, -43], ![-71, 12, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [8, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 96], [0, 1]]
 g := ![![[87, 85], [31], [53], [18], [3], [80, 1]], ![[0, 12], [31], [53], [18], [3], [63, 96]]]
 h' := ![![[80, 96], [11, 52], [29, 15], [68, 21], [42, 42], [39, 87], [0, 1]], ![[0, 1], [0, 45], [65, 82], [2, 76], [7, 55], [15, 10], [80, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [49, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [8, 17, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2706, 106, 81]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -44, 81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![43, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![43, 1, 0]] 
 ![![97, 0, 0], ![43, 1, 0], ![91, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![43, 1, 0], ![0, 43, 1], ![155, -31, 43]]]
  hmulB := by decide  
  f := ![![![1205, 28, 0], ![-2716, 0, 0]], ![![473, 11, 0], ![-1066, 0, 0]], ![![1095, 25, 0], ![-2468, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 97, 0], ![-91, 0, 97]], ![![0, 1, 0], ![-20, 43, 1], ![-25, -31, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![37, -43, 1]] ![![97, 0, 0], ![43, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4171, 97, 0]], ![![3589, -4171, 97], ![1746, -1843, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![43, 1, 0]]], ![![![37, -43, 1]], ![![18, -19, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![14, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![14, 1, 0]] 
 ![![101, 0, 0], ![14, 1, 0], ![6, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![14, 1, 0], ![0, 14, 1], ![155, -31, 14]]]
  hmulB := by decide  
  f := ![![![743, 53, 0], ![-5353, 0, 0]], ![![98, 7, 0], ![-706, 0, 0]], ![![30, 2, 0], ![-216, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 101, 0], ![-6, 0, 101]], ![![0, 1, 0], ![-2, 14, 1], ![5, -31, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![16, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![16, 1, 0]] 
 ![![101, 0, 0], ![16, 1, 0], ![47, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![16, 1, 0], ![0, 16, 1], ![155, -31, 16]]]
  hmulB := by decide  
  f := ![![![273, 17, 0], ![-1717, 0, 0]], ![![16, 1, 0], ![-100, 0, 0]], ![![115, 7, 0], ![-723, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 101, 0], ![-47, 0, 101]], ![![0, 1, 0], ![-3, 16, 1], ![-1, -31, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -3, 1]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-2, -3, 1]] 
 ![![101, 0, 0], ![71, 1, 0], ![9, 0, 1]] where
  M :=![![![-2, -3, 1], ![155, -33, -3], ![-465, 248, -33]]]
  hmulB := by decide  
  f := ![![![-1833, -149, -42]], ![![-1353, -110, -31]], ![![-392, -32, -9]]]
  g := ![![![2, -3, 1], ![25, -33, -3], ![-176, 248, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![14, 1, 0]] ![![101, 0, 0], ![16, 1, 0]]
  ![![1833, 149, 42]] where
 M := ![![![10201, 0, 0], ![1616, 101, 0]], ![![1414, 101, 0], ![224, 30, 1]]]
 hmul := by decide  
 g := ![![![![202, 303, -101]], ![![-123, 81, -13]]], ![![![-127, 75, -11]], ![![-37, 14, -1]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![1833, 149, 42]] ![![-2, -3, 1]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [85, 47, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 101, 49], [95, 1, 54], [0, 1]]
 g := ![![[51, 17, 52], [16, 92, 60], [78, 43, 76], [5, 61], [84, 83], [1]], ![[18, 11, 18, 14], [59, 36, 39, 61], [81, 20, 84, 41], [23, 33], [15, 32], [54, 5, 35, 23]], ![[66, 74, 15, 75], [32, 42, 19, 31], [57, 19, 48, 39], [80, 83], [74, 97], [66, 24, 75, 80]]]
 h' := ![![[94, 101, 49], [82, 82, 84], [65, 99, 67], [2, 48, 30], [85, 77, 79], [18, 56, 86], [0, 1]], ![[95, 1, 54], [80, 81, 85], [21, 6, 77], [83, 43, 13], [94, 85, 41], [37, 53, 49], [94, 101, 49]], ![[0, 1], [32, 43, 37], [58, 101, 62], [11, 12, 60], [61, 44, 86], [58, 97, 71], [95, 1, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 31], []]
 b := ![[], [12, 20, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [85, 47, 17, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-796705, 315695, -27295]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7735, 3065, -265]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [95, 99, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 73, 75], [38, 33, 32], [0, 1]]
 g := ![![[2, 37, 79], [105, 104, 41], [101, 100], [75, 83, 19], [68, 99], [1]], ![[40, 74, 20, 100], [87, 99, 95, 92], [37, 81], [18, 46, 53, 79], [76, 92], [54, 66, 84, 81]], ![[49, 54, 50, 26], [81, 74, 86, 60], [100, 40], [41, 78, 43, 24], [41, 19], [84, 29, 54, 26]]]
 h' := ![![[24, 73, 75], [83, 47, 20], [45, 82, 83], [44, 0, 97], [104, 105, 33], [12, 8, 62], [0, 1]], ![[38, 33, 32], [77, 0, 12], [14, 88, 8], [76, 57, 98], [36, 19, 83], [27, 38, 78], [24, 73, 75]], ![[0, 1], [60, 60, 75], [46, 44, 16], [39, 50, 19], [98, 90, 98], [26, 61, 74], [38, 33, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 65], []]
 b := ![[], [86, 25, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [95, 99, 45, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4280, 10379, -2782]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 97, -26]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [57, 35, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 31, 92], [78, 77, 17], [0, 1]]
 g := ![![[33, 38, 20], [54, 83], [10, 47, 34], [26, 38, 7], [74, 102], [1]], ![[69, 70, 23, 44], [30, 20], [17, 81, 57, 32], [10, 19, 73, 41], [7, 31], [17, 68, 99, 101]], ![[92, 4, 12, 77], [35, 4], [35, 50, 56, 39], [104, 55, 89, 8], [16, 22], [36, 93, 15, 8]]]
 h' := ![![[81, 31, 92], [54, 69, 42], [84, 106, 65], [44, 11, 19], [12, 55, 15], [52, 74, 50], [0, 1]], ![[78, 77, 17], [50, 72, 99], [105, 17, 42], [58, 21, 77], [17, 87, 2], [78, 98, 85], [81, 31, 92]], ![[0, 1], [56, 77, 77], [31, 95, 2], [98, 77, 13], [76, 76, 92], [94, 46, 83], [78, 77, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 64], []]
 b := ![[], [10, 9, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [57, 35, 59, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1178617, -60059, -3161]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10813, -551, -29]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [89, 28, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 90, 106], [108, 22, 7], [0, 1]]
 g := ![![[78, 20, 63], [37, 14], [66, 44], [82, 52], [72, 31, 91], [1]], ![[96, 66, 40, 69], [60, 87], [52, 22], [11, 72], [38, 66, 109, 32], [43, 47, 112, 109]], ![[102, 36, 36, 15], [11, 25], [46, 50], [28, 36], [85, 111, 75, 11], [48, 25, 80, 4]]]
 h' := ![![[64, 90, 106], [72, 94, 17], [38, 61, 63], [6, 24, 65], [33, 95, 39], [24, 85, 59], [0, 1]], ![[108, 22, 7], [1, 54, 55], [16, 109, 55], [24, 104, 19], [72, 107, 80], [112, 26, 25], [64, 90, 106]], ![[0, 1], [69, 78, 41], [101, 56, 108], [63, 98, 29], [71, 24, 107], [10, 2, 29], [108, 22, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 63], []]
 b := ![[], [49, 44, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [89, 28, 54, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-110401, 30397, 226]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-977, 269, 2]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![44, -34, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![44, -34, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![44, 93, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![44, -34, 1], ![155, 13, -34], ![-5270, 1209, 13]]]
  hmulB := by decide  
  f := ![![![-43, 34, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -93, 127]], ![![0, -1, 1], ![13, 25, -34], ![-46, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [112, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 126], [0, 1]]
 g := ![![[60, 16], [56, 115], [27, 25], [66, 120], [51, 81], [11, 1]], ![[109, 111], [51, 12], [48, 102], [116, 7], [53, 46], [22, 126]]]
 h' := ![![[11, 126], [78, 123], [24, 78], [101, 122], [3, 45], [38, 9], [0, 1]], ![[0, 1], [34, 4], [120, 49], [46, 5], [117, 82], [10, 118], [11, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [59, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [112, 116, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![732, 612, 109]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -75, 109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![34, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![34, 1, 0]] 
 ![![127, 0, 0], ![34, 1, 0], ![114, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![34, 1, 0], ![0, 34, 1], ![155, -31, 34]]]
  hmulB := by decide  
  f := ![![![1735, 51, 0], ![-6477, 0, 0]], ![![442, 13, 0], ![-1650, 0, 0]], ![![1506, 44, 0], ![-5622, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 127, 0], ![-114, 0, 127]], ![![0, 1, 0], ![-10, 34, 1], ![-21, -31, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![44, -34, 1]] ![![127, 0, 0], ![34, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![4318, 127, 0]], ![![5588, -4318, 127], ![1651, -1143, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![34, 1, 0]]], ![![![44, -34, 1]], ![![13, -9, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![9, -41, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![9, -41, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![9, 90, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![9, -41, 1], ![155, -22, -41], ![-6355, 1426, -22]]]
  hmulB := by decide  
  f := ![![![-8, 41, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -90, 131]], ![![0, -1, 1], ![4, 28, -41], ![-47, 26, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [73, 93, 1] where
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
 g := ![![[91, 65], [13, 89], [121], [20], [39], [3], [1]], ![[72, 66], [120, 42], [121], [20], [39], [3], [1]]]
 h' := ![![[38, 130], [99, 117], [116, 73], [98, 11], [36, 46], [1, 68], [58, 38], [0, 1]], ![[0, 1], [91, 14], [8, 58], [123, 120], [81, 85], [96, 63], [61, 93], [38, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [18, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [73, 93, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5937, 890, 170]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -110, 170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![41, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![41, 1, 0]] 
 ![![131, 0, 0], ![41, 1, 0], ![22, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![41, 1, 0], ![0, 41, 1], ![155, -31, 41]]]
  hmulB := by decide  
  f := ![![![575, 14, 0], ![-1834, 0, 0]], ![![123, 3, 0], ![-392, 0, 0]], ![![54, 1, 0], ![-172, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 131, 0], ![-22, 0, 131]], ![![0, 1, 0], ![-13, 41, 1], ![4, -31, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![9, -41, 1]] ![![131, 0, 0], ![41, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![5371, 131, 0]], ![![1179, -5371, 131], ![524, -1703, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![41, 1, 0]]], ![![![9, -41, 1]], ![![4, -13, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-28, -30, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-28, -30, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![109, 107, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-28, -30, 1], ![155, -59, -30], ![-4650, 1085, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -107, 137]], ![![-1, -1, 1], ![25, 23, -30], ![13, 54, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [103, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 136], [0, 1]]
 g := ![![[28, 4], [103], [120], [102, 50], [9], [49], [1]], ![[0, 133], [103], [120], [26, 87], [9], [49], [1]]]
 h' := ![![[130, 136], [14, 2], [38, 69], [43, 95], [43, 18], [82, 3], [34, 130], [0, 1]], ![[0, 1], [0, 135], [103, 68], [63, 42], [54, 119], [61, 134], [83, 7], [130, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [134, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [103, 7, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53, 184, 3]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -1, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![30, 1, 0]] 
 ![![137, 0, 0], ![30, 1, 0], ![59, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![30, 1, 0], ![0, 30, 1], ![155, -31, 30]]]
  hmulB := by decide  
  f := ![![![841, 28, 0], ![-3836, 0, 0]], ![![150, 5, 0], ![-684, 0, 0]], ![![367, 12, 0], ![-1674, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 137, 0], ![-59, 0, 137]], ![![0, 1, 0], ![-7, 30, 1], ![-5, -31, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-28, -30, 1]] ![![137, 0, 0], ![30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![4110, 137, 0]], ![![-3836, -4110, 137], ![-685, -959, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![30, 1, 0]]], ![![![-28, -30, 1]], ![![-5, -7, 0]]]]
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


lemma PB248I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB248I2 : PrimesBelowBoundCertificateInterval O 79 137 248 where
  m := 11
  g := ![1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB248I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
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
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
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
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
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
  β := ![I97N1, I101N0, I101N1, I101N2, I127N1, I131N1, I137N1]
  Il := ![[], [], [I97N1], [I101N0, I101N1, I101N2], [], [], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
