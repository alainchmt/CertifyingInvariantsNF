
import IdealArithmetic.Examples.NF3_1_343980_3.RI3_1_343980_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-62, 35, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-62, 35, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![21, 35, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-62, 35, 1], ![154, -20, 35], ![5390, 1624, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -35, 83]], ![![-1, 0, 1], ![-7, -15, 35], ![70, 28, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [59, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 82], [0, 1]]
 g := ![![[49, 38], [42, 23], [81], [7], [13, 30], [1]], ![[0, 45], [32, 60], [81], [7], [18, 53], [1]]]
 h' := ![![[14, 82], [12, 11], [38, 40], [70, 74], [63, 67], [24, 14], [0, 1]], ![[0, 1], [0, 72], [17, 43], [27, 9], [5, 16], [54, 69], [14, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [37, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [59, 69, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![367, 169, -26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 13, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-35, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-35, 1, 0]] 
 ![![83, 0, 0], ![48, 1, 0], ![20, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-35, 1, 0], ![0, -35, 1], ![154, 42, -35]]]
  hmulB := by decide  
  f := ![![![1086, -31, 0], ![2573, 0, 0]], ![![666, -19, 0], ![1578, 0, 0]], ![![260, -7, 0], ![616, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 83, 0], ![-20, 0, 83]], ![![-1, 1, 0], ![20, -35, 1], ![-14, 42, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-62, 35, 1]] ![![83, 0, 0], ![-35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2905, 83, 0]], ![![-5146, 2905, 83], ![2324, -1245, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-35, 1, 0]]], ![![![-62, 35, 1]], ![![28, -15, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [70, 1, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 60, 27], [34, 28, 62], [0, 1]]
 g := ![![[16, 81, 44], [27, 17], [36, 32], [25, 45, 64], [56, 71, 1], []], ![[48, 1, 86, 38], [30, 55], [9, 22], [87, 75, 28, 31], [82, 77, 73, 75], [86, 17]], ![[15, 55, 50, 86], [22, 47], [14, 36], [57, 6, 8, 28], [22, 55, 74, 77], [51, 17]]]
 h' := ![![[37, 60, 27], [36, 73, 20], [71, 68, 62], [30, 45, 78], [85, 47, 8], [0, 0, 1], [0, 1]], ![[34, 28, 62], [52, 20, 39], [4, 87, 12], [79, 25, 17], [38, 8, 69], [66, 49, 28], [37, 60, 27]], ![[0, 1], [73, 85, 30], [10, 23, 15], [79, 19, 83], [82, 34, 12], [78, 40, 60], [34, 28, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 77], []]
 b := ![[], [27, 59, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [70, 1, 18, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![262194, 272518, 46458]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2946, 3062, 522]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [14, 4, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 14, 65], [61, 82, 32], [0, 1]]
 g := ![![[31, 55, 25], [17, 31], [60, 25], [35, 81], [54, 31], [1]], ![[9, 79, 82, 50], [81, 22], [65, 11], [28, 47], [], [65, 90, 16, 18]], ![[40, 54, 38, 44], [47, 73], [34, 54], [66, 53], [62, 31], [59, 75, 16, 79]]]
 h' := ![![[51, 14, 65], [61, 65, 5], [69, 2, 82], [91, 80, 92], [22, 44, 88], [83, 93, 15], [0, 1]], ![[61, 82, 32], [91, 73, 76], [35, 17, 64], [84, 17, 37], [31, 8, 85], [15, 52], [51, 14, 65]], ![[0, 1], [54, 56, 16], [79, 78, 48], [19, 0, 65], [78, 45, 21], [48, 49, 82], [61, 82, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 61], []]
 b := ![[], [49, 66, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [14, 4, 82, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![103208, -13968, -7954]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1064, -144, -82]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-62, -9, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-62, -9, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![39, 92, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-62, -9, 1], ![154, -20, -9], ![-1386, -224, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -92, 101]], ![![-1, -1, 1], ![5, 8, -9], ![-6, 16, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [51, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 100], [0, 1]]
 g := ![![[97, 4], [9], [62, 45], [79], [88], [2, 1]], ![[4, 97], [9], [51, 56], [79], [88], [4, 100]]]
 h' := ![![[2, 100], [98, 2], [70, 98], [42, 67], [58, 68], [100, 54], [0, 1]], ![[0, 1], [1, 99], [64, 3], [75, 34], [93, 33], [6, 47], [2, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [1, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [51, 99, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-773, 1235, 76]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -57, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![9, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![9, 1, 0]] 
 ![![101, 0, 0], ![9, 1, 0], ![20, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![9, 1, 0], ![0, 9, 1], ![154, 42, 9]]]
  hmulB := by decide  
  f := ![![![370, 41, 0], ![-4141, 0, 0]], ![![18, 2, 0], ![-201, 0, 0]], ![![64, 7, 0], ![-716, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 101, 0], ![-20, 0, 101]], ![![0, 1, 0], ![-1, 9, 1], ![-4, 42, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-62, -9, 1]] ![![101, 0, 0], ![9, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![909, 101, 0]], ![![-6262, -909, 101], ![-404, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![9, 1, 0]]], ![![![-62, -9, 1]], ![![-4, -1, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-35, -25, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-35, -25, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![68, 78, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-35, -25, 1], ![154, 7, -25], ![-3850, -896, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -78, 103]], ![![-1, -1, 1], ![18, 19, -25], ![-42, -14, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [6, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 102], [0, 1]]
 g := ![![[17, 50], [5, 59], [42, 1], [15], [25], [1, 1]], ![[67, 53], [64, 44], [43, 102], [15], [25], [2, 102]]]
 h' := ![![[1, 102], [73, 16], [57, 70], [31, 102], [92, 85], [97, 98], [0, 1]], ![[0, 1], [89, 87], [24, 33], [30, 1], [74, 18], [92, 5], [1, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [94, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [6, 102, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314, 136, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, 46, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![25, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![25, 1, 0]] 
 ![![103, 0, 0], ![25, 1, 0], ![96, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![25, 1, 0], ![0, 25, 1], ![154, 42, 25]]]
  hmulB := by decide  
  f := ![![![676, 27, 0], ![-2781, 0, 0]], ![![150, 6, 0], ![-617, 0, 0]], ![![632, 25, 0], ![-2600, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 103, 0], ![-96, 0, 103]], ![![0, 1, 0], ![-7, 25, 1], ![-32, 42, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-35, -25, 1]] ![![103, 0, 0], ![25, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2575, 103, 0]], ![![-3605, -2575, 103], ![-721, -618, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![25, 1, 0]]], ![![![-35, -25, 1]], ![![-7, -6, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![30, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![30, 1, 0]] 
 ![![107, 0, 0], ![30, 1, 0], ![63, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![30, 1, 0], ![0, 30, 1], ![154, 42, 30]]]
  hmulB := by decide  
  f := ![![![631, 21, 0], ![-2247, 0, 0]], ![![150, 5, 0], ![-534, 0, 0]], ![![339, 11, 0], ![-1207, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 107, 0], ![-63, 0, 107]], ![![0, 1, 0], ![-9, 30, 1], ![-28, 42, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-18, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-18, 1, 0]] 
 ![![107, 0, 0], ![89, 1, 0], ![104, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-18, 1, 0], ![0, -18, 1], ![154, 42, -18]]]
  hmulB := by decide  
  f := ![![![145, -8, 0], ![856, 0, 0]], ![![127, -7, 0], ![750, 0, 0]], ![![148, -8, 0], ![874, 1, 0]]]
  g := ![![![1, 0, 0], ![-89, 107, 0], ![-104, 0, 107]], ![![-1, 1, 0], ![14, -18, 1], ![-16, 42, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-12, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-12, 1, 0]] 
 ![![107, 0, 0], ![95, 1, 0], ![70, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-12, 1, 0], ![0, -12, 1], ![154, 42, -12]]]
  hmulB := by decide  
  f := ![![![133, -11, 0], ![1177, 0, 0]], ![![121, -10, 0], ![1071, 0, 0]], ![![98, -8, 0], ![868, 1, 0]]]
  g := ![![![1, 0, 0], ![-95, 107, 0], ![-70, 0, 107]], ![![-1, 1, 0], ![10, -12, 1], ![-28, 42, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![30, 1, 0]] ![![107, 0, 0], ![-18, 1, 0]]
  ![![107, 0, 0], ![-5, 12, 1]] where
 M := ![![![11449, 0, 0], ![-1926, 107, 0]], ![![3210, 107, 0], ![-540, 12, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![-13, -11, -1], ![107, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![-5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-5, 12, 1]] ![![107, 0, 0], ![-12, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1284, 107, 0]], ![![-535, 1284, 107], ![214, -107, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-12, 1, 0]]], ![![![-5, 12, 1]], ![![2, -1, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-4, 16, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-4, 16, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![105, 16, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-4, 16, 1], ![154, 38, 16], ![2464, 826, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -16, 109]], ![![-1, 0, 1], ![-14, -2, 16], ![-14, 2, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [76, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 108], [0, 1]]
 g := ![![[55, 20], [4], [90, 74], [21, 83], [3], [71, 1]], ![[58, 89], [4], [3, 35], [28, 26], [3], [33, 108]]]
 h' := ![![[71, 108], [98, 67], [27, 107], [39, 40], [72, 44], [54, 60], [0, 1]], ![[0, 1], [59, 42], [103, 2], [45, 69], [35, 65], [63, 49], [71, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [69, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [76, 38, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5967, 2510, 443]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-372, -42, 443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-16, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-16, 1, 0]] 
 ![![109, 0, 0], ![93, 1, 0], ![71, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-16, 1, 0], ![0, -16, 1], ![154, 42, -16]]]
  hmulB := by decide  
  f := ![![![1329, -83, 0], ![9047, 0, 0]], ![![1121, -70, 0], ![7631, 0, 0]], ![![883, -55, 0], ![6011, 1, 0]]]
  g := ![![![1, 0, 0], ![-93, 109, 0], ![-71, 0, 109]], ![![-1, 1, 0], ![13, -16, 1], ![-24, 42, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-4, 16, 1]] ![![109, 0, 0], ![-16, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1744, 109, 0]], ![![-436, 1744, 109], ![218, -218, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-16, 1, 0]]], ![![![-4, 16, 1]], ![![2, -2, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![113, 0, 0], ![1, 1, 0], ![112, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![154, 42, 1]]]
  hmulB := by decide  
  f := ![![![-41, -1, 1]], ![![1, 0, 0]], ![![-42, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, 42, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![19, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![19, 1, 0]] 
 ![![113, 0, 0], ![19, 1, 0], ![91, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![19, 1, 0], ![0, 19, 1], ![154, 42, 19]]]
  hmulB := by decide  
  f := ![![![77, 4, 0], ![-452, 0, 0]], ![![-19, -1, 0], ![114, 0, 0]], ![![61, 3, 0], ![-358, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 113, 0], ![-91, 0, 113]], ![![0, 1, 0], ![-4, 19, 1], ![-21, 42, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-20, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-20, 1, 0]] 
 ![![113, 0, 0], ![93, 1, 0], ![52, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-20, 1, 0], ![0, -20, 1], ![154, 42, -20]]]
  hmulB := by decide  
  f := ![![![461, -23, 0], ![2599, 0, 0]], ![![401, -20, 0], ![2261, 0, 0]], ![![204, -10, 0], ![1150, 1, 0]]]
  g := ![![![1, 0, 0], ![-93, 113, 0], ![-52, 0, 113]], ![![-1, 1, 0], ![16, -20, 1], ![-24, 42, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![113, 0, 0], ![19, 1, 0]]
  ![![113, 0, 0], ![19, 20, 1]] where
 M := ![![![113, 113, 0], ![19, 20, 1]]]
 hmul := by decide  
 g := ![![![![-18, -19, -1], ![113, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![19, 20, 1]] ![![113, 0, 0], ![-20, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2260, 113, 0]], ![![2147, 2260, 113], ![-226, -339, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-20, 1, 0]]], ![![![19, 20, 1]], ![![-2, -3, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-85, 46, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-85, 46, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![42, 46, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-85, 46, 1], ![154, -43, 46], ![7084, 2086, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -46, 127]], ![![-1, 0, 1], ![-14, -17, 46], ![70, 32, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [76, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [114, 126], [0, 1]]
 g := ![![[62, 122], [81, 16], [121, 107], [92, 41], [84, 13], [114, 1]], ![[0, 5], [0, 111], [0, 20], [67, 86], [42, 114], [101, 126]]]
 h' := ![![[114, 126], [67, 54], [75, 123], [120, 19], [93, 101], [99, 93], [0, 1]], ![[0, 1], [0, 73], [0, 4], [0, 108], [50, 26], [33, 34], [114, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [81, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [76, 13, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-860, -65, 40]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -15, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-46, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-46, 1, 0]] 
 ![![127, 0, 0], ![81, 1, 0], ![43, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-46, 1, 0], ![0, -46, 1], ![154, 42, -46]]]
  hmulB := by decide  
  f := ![![![3681, -80, 0], ![10160, 0, 0]], ![![2347, -51, 0], ![6478, 0, 0]], ![![1305, -28, 0], ![3602, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 127, 0], ![-43, 0, 127]], ![![-1, 1, 0], ![29, -46, 1], ![-10, 42, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-85, 46, 1]] ![![127, 0, 0], ![-46, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-5842, 127, 0]], ![![-10795, 5842, 127], ![4064, -2159, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-46, 1, 0]]], ![![![-85, 46, 1]], ![![32, -17, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![35, -48, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![35, -48, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![35, 83, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![35, -48, 1], ![154, 77, -48], ![-7392, -1862, 77]]]
  hmulB := by decide  
  f := ![![![-34, 48, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -83, 131]], ![![0, -1, 1], ![14, 31, -48], ![-77, -63, 77]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [42, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 130], [0, 1]]
 g := ![![[11, 13], [69, 102], [20], [44], [63], [45], [1]], ![[31, 118], [105, 29], [20], [44], [63], [45], [1]]]
 h' := ![![[62, 130], [115, 119], [115, 44], [118, 46], [130, 31], [5, 71], [89, 62], [0, 1]], ![[0, 1], [26, 12], [92, 87], [88, 85], [87, 100], [84, 60], [3, 69], [62, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [106, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [42, 69, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![658, 853, 307]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -188, 307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![48, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![48, 1, 0]] 
 ![![131, 0, 0], ![48, 1, 0], ![54, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![48, 1, 0], ![0, 48, 1], ![154, 42, 48]]]
  hmulB := by decide  
  f := ![![![2353, 49, 0], ![-6419, 0, 0]], ![![816, 17, 0], ![-2226, 0, 0]], ![![978, 20, 0], ![-2668, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 131, 0], ![-54, 0, 131]], ![![0, 1, 0], ![-18, 48, 1], ![-34, 42, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![35, -48, 1]] ![![131, 0, 0], ![48, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![6288, 131, 0]], ![![4585, -6288, 131], ![1834, -2227, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![48, 1, 0]]], ![![![35, -48, 1]], ![![14, -17, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![32, -38, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![32, -38, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![32, 99, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![32, -38, 1], ![154, 74, -38], ![-5852, -1442, 74]]]
  hmulB := by decide  
  f := ![![![-31, 38, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -99, 137]], ![![0, -1, 1], ![10, 28, -38], ![-60, -64, 74]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [70, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 136], [0, 1]]
 g := ![![[9, 38], [14], [64], [48, 32], [19], [11], [1]], ![[44, 99], [14], [64], [27, 105], [19], [11], [1]]]
 h' := ![![[55, 136], [66, 60], [19, 39], [65, 8], [29, 13], [20, 29], [67, 55], [0, 1]], ![[0, 1], [78, 77], [109, 98], [94, 129], [59, 124], [108, 108], [78, 82], [55, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [11, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [70, 82, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5922, -1924, 440]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-146, -332, 440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![38, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![38, 1, 0]] 
 ![![137, 0, 0], ![38, 1, 0], ![63, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![38, 1, 0], ![0, 38, 1], ![154, 42, 38]]]
  hmulB := by decide  
  f := ![![![2471, 65, 0], ![-8905, 0, 0]], ![![646, 17, 0], ![-2328, 0, 0]], ![![1113, 29, 0], ![-4011, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 137, 0], ![-63, 0, 137]], ![![0, 1, 0], ![-11, 38, 1], ![-28, 42, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![32, -38, 1]] ![![137, 0, 0], ![38, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![5206, 137, 0]], ![![4384, -5206, 137], ![1370, -1370, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![38, 1, 0]]], ![![![32, -38, 1]], ![![10, -10, 0]]]]
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


lemma PB166I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB166I2 : PrimesBelowBoundCertificateInterval O 79 137 166 where
  m := 11
  g := ![2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB166I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N1, I113N0, I113N1, I113N2, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [], [], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
