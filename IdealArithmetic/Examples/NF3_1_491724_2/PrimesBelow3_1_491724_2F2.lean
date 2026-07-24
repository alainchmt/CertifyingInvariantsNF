
import IdealArithmetic.Examples.NF3_1_491724_2.RI3_1_491724_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [58, 65, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 13, 81], [3, 69, 2], [0, 1]]
 g := ![![[4, 34, 1], [20, 54, 38], [35, 30], [29, 70], [3, 20, 1], []], ![[4, 13, 19, 9], [67, 10, 26, 1], [57, 23], [17, 77], [6, 34, 81, 23], [28, 4]], ![[73, 35, 65, 47], [20, 47, 68, 24], [75, 11], [59, 16], [9, 63, 51, 6], [24, 4]]]
 h' := ![![[17, 13, 81], [2, 7, 1], [66, 17, 72], [42, 48, 14], [75, 56, 30], [0, 0, 1], [0, 1]], ![[3, 69, 2], [31, 58, 55], [17, 3, 37], [13, 79, 40], [70, 70, 49], [76, 50, 69], [17, 13, 81]], ![[0, 1], [51, 18, 27], [58, 63, 57], [80, 39, 29], [4, 40, 4], [28, 33, 13], [3, 69, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 49], []]
 b := ![[], [10, 4, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [58, 65, 63, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-841952, -245597, -17264]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10144, -2959, -208]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [7, 4, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 21, 33], [81, 67, 56], [0, 1]]
 g := ![![[69, 69, 85], [43, 85], [5, 69], [75, 55, 68], [65, 43, 1], []], ![[43, 71, 45, 35], [18, 49], [6, 79], [55, 59, 82, 63], [70, 22, 81, 41], [64, 21]], ![[23, 29, 65, 86], [52, 18], [21, 25], [40, 51, 30, 38], [30, 76, 24, 43], [41, 21]]]
 h' := ![![[51, 21, 33], [35, 43, 68], [46, 3, 21], [9, 38, 43], [79, 62, 35], [0, 0, 1], [0, 1]], ![[81, 67, 56], [2, 73, 12], [22, 3, 82], [8, 14, 41], [9, 45, 30], [17, 48, 67], [51, 21, 33]], ![[0, 1], [13, 62, 9], [56, 83, 75], [84, 37, 5], [55, 71, 24], [44, 41, 21], [81, 67, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 57], []]
 b := ![[], [71, 56, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [7, 4, 46, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8859060, 5345696, 681829]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99540, 60064, 7661]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [3, 23, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 27, 58], [54, 69, 39], [0, 1]]
 g := ![![[89, 20, 72], [72, 85], [15, 94], [49, 89], [29, 70], [1]], ![[78, 68, 74, 67], [89, 81], [88, 88], [69, 27], [84, 94], [16, 32, 29, 45]], ![[50, 80, 51, 71], [12, 35], [80, 48], [50, 22], [13, 85], [20, 1, 64, 52]]]
 h' := ![![[24, 27, 58], [0, 31, 13], [64, 47, 52], [20, 12, 71], [19, 37, 34], [94, 74, 78], [0, 1]], ![[54, 69, 39], [77, 87, 76], [76, 15, 9], [90, 78, 66], [43, 0, 30], [2, 20, 71], [24, 27, 58]], ![[0, 1], [34, 76, 8], [19, 35, 36], [68, 7, 57], [11, 60, 33], [70, 3, 45], [54, 69, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 47], []]
 b := ![[], [11, 77, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [3, 23, 19, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145403, -234837, -59558]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1499, -2421, -614]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![4, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![4, 1, 0]] 
 ![![101, 0, 0], ![4, 1, 0], ![85, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![4, 1, 0], ![0, 4, 1], ![762, 156, 4]]]
  hmulB := by decide  
  f := ![![![281, 70, 0], ![-7070, 0, 0]], ![![4, 1, 0], ![-100, 0, 0]], ![![241, 60, 0], ![-6064, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 101, 0], ![-85, 0, 101]], ![![0, 1, 0], ![-1, 4, 1], ![-2, 156, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![10, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![10, 1, 0]] 
 ![![101, 0, 0], ![10, 1, 0], ![1, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![10, 1, 0], ![0, 10, 1], ![762, 156, 10]]]
  hmulB := by decide  
  f := ![![![731, 73, 0], ![-7373, 0, 0]], ![![70, 7, 0], ![-706, 0, 0]], ![![-9, -1, 0], ![91, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 101, 0], ![-1, 0, 101]], ![![0, 1, 0], ![-1, 10, 1], ![-8, 156, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-14, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-14, 1, 0]] 
 ![![101, 0, 0], ![87, 1, 0], ![6, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-14, 1, 0], ![0, -14, 1], ![762, 156, -14]]]
  hmulB := by decide  
  f := ![![![1023, -73, 0], ![7373, 0, 0]], ![![869, -62, 0], ![6263, 0, 0]], ![![86, -6, 0], ![620, 1, 0]]]
  g := ![![![1, 0, 0], ![-87, 101, 0], ![-6, 0, 101]], ![![-1, 1, 0], ![12, -14, 1], ![-126, 156, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![4, 1, 0]] ![![101, 0, 0], ![10, 1, 0]]
  ![![101, 0, 0], ![-61, 14, 1]] where
 M := ![![![10201, 0, 0], ![1010, 101, 0]], ![![404, 101, 0], ![40, 14, 1]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![10, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-61, 14, 1]] ![![101, 0, 0], ![-14, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1414, 101, 0]], ![![-6161, 1414, 101], ![1616, -101, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-14, 1, 0]]], ![![![-61, 14, 1]], ![![16, -1, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-115, -12, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-115, -12, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![91, 91, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-115, -12, 1], ![762, 41, -12], ![-9144, -1110, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -91, 103]], ![![-2, -1, 1], ![18, 11, -12], ![-125, -47, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [92, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 102], [0, 1]]
 g := ![![[21, 28], [20, 61], [92, 68], [7], [15], [25, 1]], ![[0, 75], [0, 42], [41, 35], [7], [15], [50, 102]]]
 h' := ![![[25, 102], [14, 53], [85, 79], [92, 45], [85, 78], [69, 18], [0, 1]], ![[0, 1], [0, 50], [0, 24], [84, 58], [78, 25], [4, 85], [25, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [53, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [92, 78, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4401, 6002, 1165]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1072, -971, 1165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![12, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![12, 1, 0]] 
 ![![103, 0, 0], ![12, 1, 0], ![62, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![12, 1, 0], ![0, 12, 1], ![762, 156, 12]]]
  hmulB := by decide  
  f := ![![![445, 37, 0], ![-3811, 0, 0]], ![![36, 3, 0], ![-308, 0, 0]], ![![266, 22, 0], ![-2278, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 103, 0], ![-62, 0, 103]], ![![0, 1, 0], ![-2, 12, 1], ![-18, 156, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-115, -12, 1]] ![![103, 0, 0], ![12, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![1236, 103, 0]], ![![-11845, -1236, 103], ![-618, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![12, 1, 0]]], ![![![-115, -12, 1]], ![![-6, -1, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![3, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![3, 1, 0]] 
 ![![107, 0, 0], ![3, 1, 0], ![98, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![3, 1, 0], ![0, 3, 1], ![762, 156, 3]]]
  hmulB := by decide  
  f := ![![![103, 34, 0], ![-3638, 0, 0]], ![![-3, -1, 0], ![108, 0, 0]], ![![94, 31, 0], ![-3320, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 107, 0], ![-98, 0, 107]], ![![0, 1, 0], ![-1, 3, 1], ![0, 156, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![107, 0, 0], ![5, 1, 0], ![82, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 1], ![762, 156, 5]]]
  hmulB := by decide  
  f := ![![![-131, -5, 1]], ![![1, 0, 0]], ![![-136, -4, 1]]]
  g := ![![![0, 1, 0], ![-1, 5, 1], ![-4, 156, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-8, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-8, 1, 0]] 
 ![![107, 0, 0], ![99, 1, 0], ![43, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-8, 1, 0], ![0, -8, 1], ![762, 156, -8]]]
  hmulB := by decide  
  f := ![![![569, -71, 0], ![7597, 0, 0]], ![![529, -66, 0], ![7063, 0, 0]], ![![233, -29, 0], ![3111, 1, 0]]]
  g := ![![![1, 0, 0], ![-99, 107, 0], ![-43, 0, 107]], ![![-1, 1, 0], ![7, -8, 1], ![-134, 156, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![3, 1, 0]] ![![5, 1, 0]]
  ![![107, 0, 0], ![-92, 8, 1]] where
 M := ![![![535, 107, 0]], ![![15, 8, 1]]]
 hmul := by decide  
 g := ![![![![5, 1, 0], ![0, 0, 0]]], ![![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-92, 8, 1]] ![![107, 0, 0], ![-8, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-856, 107, 0]], ![![-9844, 856, 107], ![1498, 0, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-8, 1, 0]]], ![![![-92, 8, 1]], ![![14, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![949, 260, 18]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![949, 260, 18]] 
 ![![109, 0, 0], ![56, 1, 0], ![25, 0, 1]] where
  M :=![![![949, 260, 18], ![13716, 3757, 260], ![198120, 54276, 3757]]]
  hmulB := by decide  
  f := ![![![3289, 148, -26]], ![![1508, 69, -12]], ![![1789, 64, -13]]]
  g := ![![![-129, 260, 18], ![-1864, 3757, 260], ![-26929, 54276, 3757]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-51, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-51, 1, 0]] 
 ![![109, 0, 0], ![58, 1, 0], ![15, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-51, 1, 0], ![0, -51, 1], ![762, 156, -51]]]
  hmulB := by decide  
  f := ![![![4285, -84, 0], ![9156, 0, 0]], ![![2296, -45, 0], ![4906, 0, 0]], ![![585, -11, 0], ![1250, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 109, 0], ![-15, 0, 109]], ![![-1, 1, 0], ![27, -51, 1], ![-69, 156, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-5, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-5, 1, 0]] 
 ![![109, 0, 0], ![104, 1, 0], ![84, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-5, 1, 0], ![0, -5, 1], ![762, 156, -5]]]
  hmulB := by decide  
  f := ![![![121, -24, 0], ![2616, 0, 0]], ![![116, -23, 0], ![2508, 0, 0]], ![![96, -19, 0], ![2076, 1, 0]]]
  g := ![![![1, 0, 0], ![-104, 109, 0], ![-84, 0, 109]], ![![-1, 1, 0], ![4, -5, 1], ![-138, 156, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![949, 260, 18]] ![![109, 0, 0], ![-51, 1, 0]]
  ![![109, 0, 0], ![-131, 5, 1]] where
 M := ![![![103441, 28340, 1962], ![-34683, -9503, -658]]]
 hmul := by decide  
 g := ![![![![425, 280, 22], ![-436, 0, 0]], ![![-61, -97, -8], ![214, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-131, 5, 1]] ![![109, 0, 0], ![-5, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-545, 109, 0]], ![![-14279, 545, 109], ![1417, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-5, 1, 0]]], ![![![-131, 5, 1]], ![![13, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [25, 85, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 48, 90], [44, 64, 23], [0, 1]]
 g := ![![[73, 98, 52], [24, 81], [36, 16], [108, 16], [104, 64, 51], [1]], ![[77, 25, 16, 54], [28, 15], [10, 98], [33, 1], [10, 17, 95, 35], [6, 67, 109, 37]], ![[111, 102, 51, 90], [110, 97], [45, 83], [74, 25], [101, 100, 23, 54], [1, 72, 112, 76]]]
 h' := ![![[96, 48, 90], [62, 47, 39], [60, 87, 9], [13, 106, 109], [112, 16, 4], [88, 28, 27], [0, 1]], ![[44, 64, 23], [31, 80, 59], [36, 110, 44], [88, 90, 18], [110, 3, 1], [22, 107, 67], [96, 48, 90]], ![[0, 1], [111, 99, 15], [6, 29, 60], [112, 30, 99], [70, 94, 108], [70, 91, 19], [44, 64, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 112], []]
 b := ![[], [17, 57, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [25, 85, 86, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-806933, -220915, -13673]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7141, -1955, -121]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-156, 0, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-156, 0, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![98, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-156, 0, 1], ![762, 0, 0], ![0, 762, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, 0, 127]], ![![-2, 0, 1], ![6, 0, 0], ![0, 6, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [83, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 126], [0, 1]]
 g := ![![[36, 71], [72, 120], [78, 26], [6, 18], [21, 124], [60, 1]], ![[105, 56], [33, 7], [114, 101], [70, 109], [95, 3], [120, 126]]]
 h' := ![![[60, 126], [120, 84], [3, 82], [10, 91], [35, 79], [100, 88], [0, 1]], ![[0, 1], [80, 43], [97, 45], [9, 36], [76, 48], [46, 39], [60, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [58, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [83, 67, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29107, 8001, 586]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-223, 63, 586]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![0, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![0, 1, 0]] 
 ![![127, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![0, 1, 0], ![0, 0, 1], ![762, 156, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![0, 1, 0], ![0, 0, 1], ![6, 156, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-156, 0, 1]] ![![127, 0, 0], ![0, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![0, 127, 0]], ![![-19812, 0, 127], ![762, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![0, 1, 0]]], ![![![-156, 0, 1]], ![![6, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-155, 1, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-155, 1, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![107, 1, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-155, 1, 1], ![762, 1, 1], ![762, 918, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -1, 131]], ![![-2, 0, 1], ![5, 0, 1], ![5, 7, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [79, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 130], [0, 1]]
 g := ![![[4, 94], [57, 34], [15], [43], [94], [34], [1]], ![[37, 37], [55, 97], [15], [43], [94], [34], [1]]]
 h' := ![![[77, 130], [82, 15], [43, 54], [7, 43], [103, 49], [18, 15], [52, 77], [0, 1]], ![[0, 1], [58, 116], [9, 77], [43, 88], [77, 82], [125, 116], [86, 54], [77, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [42, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [79, 54, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4546, -18, 113]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-127, -1, 113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-1, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-1, 1, 0]] 
 ![![131, 0, 0], ![130, 1, 0], ![130, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-1, 1, 0], ![0, -1, 1], ![762, 156, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![393, 0, 0]], ![![2, -1, 0], ![132, 0, 0]], ![![2, -1, 0], ![132, 1, 0]]]
  g := ![![![1, 0, 0], ![-130, 131, 0], ![-130, 0, 131]], ![![-1, 1, 0], ![0, -1, 1], ![-148, 156, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-155, 1, 1]] ![![131, 0, 0], ![-1, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-131, 131, 0]], ![![-20305, 131, 131], ![917, 0, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-1, 1, 0]]], ![![![-155, 1, 1]], ![![7, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-93, 36, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-93, 36, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![44, 36, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-93, 36, 1], ![762, 63, 36], ![27432, 6378, 63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -36, 137]], ![![-1, 0, 1], ![-6, -9, 36], ![180, 30, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [99, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 136], [0, 1]]
 g := ![![[41, 18], [38], [107], [93, 19], [8], [135], [1]], ![[0, 119], [38], [107], [103, 118], [8], [135], [1]]]
 h' := ![![[51, 136], [85, 44], [55, 60], [109, 45], [34, 108], [135, 75], [38, 51], [0, 1]], ![[0, 1], [0, 93], [101, 77], [75, 92], [62, 29], [124, 62], [36, 86], [51, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [25, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [99, 86, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3147, 3758, 797]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-233, -182, 797]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-36, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-36, 1, 0]] 
 ![![137, 0, 0], ![101, 1, 0], ![74, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-36, 1, 0], ![0, -36, 1], ![762, 156, -36]]]
  hmulB := by decide  
  f := ![![![4609, -128, 0], ![17536, 0, 0]], ![![3349, -93, 0], ![12742, 0, 0]], ![![2458, -68, 0], ![9352, 1, 0]]]
  g := ![![![1, 0, 0], ![-101, 137, 0], ![-74, 0, 137]], ![![-1, 1, 0], ![26, -36, 1], ![-90, 156, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-93, 36, 1]] ![![137, 0, 0], ![-36, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4932, 137, 0]], ![![-12741, 4932, 137], ![4110, -1233, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-36, 1, 0]]], ![![![-93, 36, 1]], ![![30, -9, 0]]]]
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


lemma PB199I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB199I2 : PrimesBelowBoundCertificateInterval O 79 137 199 where
  m := 11
  g := ![1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB199I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
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
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![109, 109, 109]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
      exact NI109N2
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
  β := ![I101N0, I101N1, I101N2, I103N1, I107N0, I107N1, I107N2, I109N0, I109N1, I109N2, I127N1, I131N1, I137N1]
  Il := ![[], [], [], [I101N0, I101N1, I101N2], [I103N1], [I107N0, I107N1, I107N2], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
