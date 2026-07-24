
import IdealArithmetic.Examples.NF3_1_408807_1.RI3_1_408807_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [53, 23, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 30, 63], [6, 52, 20], [0, 1]]
 g := ![![[51, 35, 27], [1, 56, 27], [53, 1], [16, 78], [81, 42, 1], []], ![[55, 81, 31, 41], [15, 49, 48, 38], [17, 44], [32, 69], [24, 45, 1, 36], [79, 68]], ![[70, 22, 25, 2], [4, 74, 20, 71], [71, 12], [11, 4], [36, 71, 23, 72], [39, 68]]]
 h' := ![![[36, 30, 63], [30, 4, 39], [16, 33, 39], [13, 47, 1], [23, 61, 59], [0, 0, 1], [0, 1]], ![[6, 52, 20], [56, 14, 39], [7, 54, 40], [59, 58, 25], [57, 82, 22], [14, 59, 52], [36, 30, 63]], ![[0, 1], [27, 65, 5], [21, 79, 4], [7, 61, 57], [80, 23, 2], [44, 24, 30], [6, 52, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 53], []]
 b := ![[], [14, 47, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [53, 23, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11288, -415, -1328]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, -5, -16]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![7, 5, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![7, 5, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![7, 5, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![7, 5, 1], ![105, -14, 15], ![525, -70, -14]]]
  hmulB := by decide  
  f := ![![![-6, -5, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -5, 89]], ![![0, 0, 1], ![0, -1, 15], ![7, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [53, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 88], [0, 1]]
 g := ![![[38, 42], [69], [85], [], [43, 21], [1]], ![[0, 47], [69], [85], [], [24, 68], [1]]]
 h' := ![![[33, 88], [80, 65], [34, 46], [0, 68], [35], [36, 33], [0, 1]], ![[0, 1], [0, 24], [39, 43], [19, 21], [35], [57, 56], [33, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [18, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [53, 56, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1262, 459, -15]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 6, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-15, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-15, 1, 0]] 
 ![![89, 0, 0], ![74, 1, 0], ![14, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-15, 1, 0], ![0, -15, 3], ![105, -21, -15]]]
  hmulB := by decide  
  f := ![![![121, -8, 0], ![712, 0, 0]], ![![106, -7, 0], ![624, 0, 0]], ![![46, 2, -1], ![272, 30, 0]]]
  g := ![![![1, 0, 0], ![-74, 89, 0], ![-14, 0, 89]], ![![-1, 1, 0], ![12, -15, 3], ![21, -21, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![7, 5, 1]] ![![89, 0, 0], ![-15, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1335, 89, 0]], ![![623, 445, 89], ![0, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-15, 1, 0]]], ![![![7, 5, 1]], ![![0, -1, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [26, 68, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 54, 42], [90, 42, 55], [0, 1]]
 g := ![![[54, 10, 27], [12, 24], [11, 86], [14, 22], [48, 93], [1]], ![[95, 11, 44, 45], [5, 54], [79, 91], [24, 75], [20, 86], [23, 73, 96, 77]], ![[49, 87, 20, 41], [6, 53], [71, 61], [12, 95], [86, 36], [40, 64, 44, 20]]]
 h' := ![![[51, 54, 42], [94, 94, 67], [55, 21, 86], [27, 79, 59], [10, 85, 64], [71, 29, 44], [0, 1]], ![[90, 42, 55], [65, 34, 69], [1, 16, 32], [55, 7, 73], [0, 72, 50], [36, 24, 59], [51, 54, 42]], ![[0, 1], [20, 66, 58], [51, 60, 76], [65, 11, 62], [38, 37, 80], [72, 44, 91], [90, 42, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 56], []]
 b := ![[], [92, 87, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [26, 68, 53, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30167, -2716, -3007]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-311, -28, -31]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![33, -2, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![33, -2, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![33, 99, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![33, -2, 1], ![105, 12, -6], ![-210, 77, 12]]]
  hmulB := by decide  
  f := ![![![-32, 2, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -99, 101]], ![![0, -1, 1], ![3, 6, -6], ![-6, -11, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [82, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 100], [0, 1]]
 g := ![![[94, 85], [6], [75, 82], [45], [79], [69, 1]], ![[0, 16], [6], [77, 19], [45], [79], [37, 100]]]
 h' := ![![[69, 100], [33, 61], [11, 62], [46, 48], [91, 67], [99, 33], [0, 1]], ![[0, 1], [0, 40], [47, 39], [25, 53], [68, 34], [53, 68], [69, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [58, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [82, 32, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-515, 475, -288]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89, 287, -288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![6, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![6, 1, 0]] 
 ![![101, 0, 0], ![6, 1, 0], ![89, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![6, 1, 0], ![0, 6, 3], ![105, -21, 6]]]
  hmulB := by decide  
  f := ![![![91, 15, 0], ![-1515, 0, 0]], ![![-6, -1, 0], ![102, 0, 0]], ![![79, 11, -1], ![-1315, 34, 0]]]
  g := ![![![1, 0, 0], ![-6, 101, 0], ![-89, 0, 101]], ![![0, 1, 0], ![-3, 6, 3], ![-3, -21, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![33, -2, 1]] ![![101, 0, 0], ![6, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![606, 101, 0]], ![![3333, -202, 101], ![303, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![6, 1, 0]]], ![![![33, -2, 1]], ![![3, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![15, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![15, 1, 0]] 
 ![![103, 0, 0], ![15, 1, 0], ![28, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![15, 1, 0], ![0, 15, 3], ![105, -21, 15]]]
  hmulB := by decide  
  f := ![![![676, 45, 0], ![-4635, 0, 0]], ![![90, 6, 0], ![-617, 0, 0]], ![![166, 1, -2], ![-1138, 69, 0]]]
  g := ![![![1, 0, 0], ![-15, 103, 0], ![-28, 0, 103]], ![![0, 1, 0], ![-3, 15, 3], ![0, -21, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![44, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![44, 1, 0]] 
 ![![103, 0, 0], ![44, 1, 0], ![7, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![44, 1, 0], ![0, 44, 3], ![105, -21, 44]]]
  hmulB := by decide  
  f := ![![![1321, 30, 0], ![-3090, 0, 0]], ![![572, 13, 0], ![-1338, 0, 0]], ![![65, -28, -2], ![-152, 69, 0]]]
  g := ![![![1, 0, 0], ![-44, 103, 0], ![-7, 0, 103]], ![![0, 1, 0], ![-19, 44, 3], ![7, -21, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![15, 1, 0]] ![![103, 0, 0], ![44, 1, 0]]
  ![![103, 0, 0], ![14, -49, 1]] where
 M := ![![![10609, 0, 0], ![4532, 103, 0]], ![![1545, 103, 0], ![660, 59, 3]]]
 hmul := by decide  
 g := ![![![![89, 49, -1], ![103, 0, 0]], ![![30, 50, -1], ![103, 0, 0]]], ![![![1, 50, -1], ![103, 0, 0]], ![![6, 2, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![14, -49, 1]] ![![103, 0, 0], ![44, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![4532, 103, 0]], ![![1442, -5047, 103], ![721, -2163, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![44, 1, 0]]], ![![![14, -49, 1]], ![![7, -21, -1]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N1
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [96, 82, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 59, 4], [27, 47, 103], [0, 1]]
 g := ![![[50, 52, 56], [105, 58, 86], [82, 87], [98, 82, 13], [4, 52], [1]], ![[75, 61, 91, 19], [82, 49, 104, 101], [21, 56], [27, 12, 38, 79], [79, 76], [106, 86, 63, 64]], ![[95, 32, 94, 93], [84, 44, 86, 8], [74, 25], [2, 43, 84, 51], [32, 41], [94, 91, 103, 43]]]
 h' := ![![[15, 59, 4], [85, 62, 85], [3, 39, 34], [8, 82, 80], [58, 45, 21], [11, 25, 42], [0, 1]], ![[27, 47, 103], [92, 75, 70], [69, 76, 42], [42, 37, 22], [82, 88, 97], [47, 86, 41], [15, 59, 4]], ![[0, 1], [10, 77, 59], [14, 99, 31], [22, 95, 5], [0, 81, 96], [66, 103, 24], [27, 47, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 68], []]
 b := ![[], [15, 7, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [96, 82, 65, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16371, -642, -1819]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![153, -6, -17]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![48, 3, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![48, 3, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![48, 3, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![48, 3, 1], ![105, 27, 9], ![315, -28, 27]]]
  hmulB := by decide  
  f := ![![![-47, -3, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -3, 109]], ![![0, 0, 1], ![-3, 0, 9], ![-9, -1, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [61, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 108], [0, 1]]
 g := ![![[45, 84], [3], [6, 3], [41, 48], [35], [89, 1]], ![[0, 25], [3], [55, 106], [62, 61], [35], [69, 108]]]
 h' := ![![[89, 108], [30, 56], [70, 60], [6, 60], [50, 22], [21, 12], [0, 1]], ![[0, 1], [0, 53], [69, 49], [5, 49], [46, 87], [108, 97], [89, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [39, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [61, 20, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4072, -345, 1084]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-440, -33, 1084]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-9, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-9, 1, 0]] 
 ![![109, 0, 0], ![100, 1, 0], ![82, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-9, 1, 0], ![0, -9, 3], ![105, -21, -9]]]
  hmulB := by decide  
  f := ![![![892, -99, 0], ![10791, 0, 0]], ![![820, -91, 0], ![9920, 0, 0]], ![![676, -69, -2], ![8178, 73, 0]]]
  g := ![![![1, 0, 0], ![-100, 109, 0], ![-82, 0, 109]], ![![-1, 1, 0], ![6, -9, 3], ![27, -21, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![48, 3, 1]] ![![109, 0, 0], ![-9, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-981, 109, 0]], ![![5232, 327, 109], ![-327, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-9, 1, 0]]], ![![![48, 3, 1]], ![![-3, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![41, -46, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![41, -46, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![41, 67, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![41, -46, 1], ![105, 20, -138], ![-4830, 1001, 20]]]
  hmulB := by decide  
  f := ![![![-40, 46, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -67, 113]], ![![0, -1, 1], ![51, 82, -138], ![-50, -3, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [29, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 112], [0, 1]]
 g := ![![[46, 82], [1], [51], [83], [99, 9], [22, 1]], ![[42, 31], [1], [51], [83], [71, 104], [44, 112]]]
 h' := ![![[22, 112], [110, 67], [34, 112], [48, 86], [67, 14], [40, 3], [0, 1]], ![[0, 1], [2, 46], [12, 1], [19, 27], [36, 99], [106, 110], [22, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [67, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [29, 91, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-691, 428, -83]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 53, -83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![25, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![25, 1, 0]] 
 ![![113, 0, 0], ![25, 1, 0], ![93, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![25, 1, 0], ![0, 25, 3], ![105, -21, 25]]]
  hmulB := by decide  
  f := ![![![1551, 62, 0], ![-7006, 0, 0]], ![![325, 13, 0], ![-1468, 0, 0]], ![![1261, 42, -1], ![-5696, 38, 0]]]
  g := ![![![1, 0, 0], ![-25, 113, 0], ![-93, 0, 113]], ![![0, 1, 0], ![-8, 25, 3], ![-15, -21, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![41, -46, 1]] ![![113, 0, 0], ![25, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2825, 113, 0]], ![![4633, -5198, 113], ![1130, -1130, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![25, 1, 0]]], ![![![41, -46, 1]], ![![10, -10, -1]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![67, 10, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![67, 10, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![67, 10, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![67, 10, 1], ![105, 46, 30], ![1050, -175, 46]]]
  hmulB := by decide  
  f := ![![![-66, -10, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -10, 127]], ![![0, 0, 1], ![-15, -2, 30], ![-16, -5, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [40, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 126], [0, 1]]
 g := ![![[75, 113], [72, 88], [12, 71], [3, 18], [16, 103], [48, 1]], ![[38, 14], [105, 39], [118, 56], [105, 109], [7, 24], [96, 126]]]
 h' := ![![[48, 126], [41, 85], [28, 71], [7, 84], [122, 48], [112, 105], [0, 1]], ![[0, 1], [57, 42], [7, 56], [102, 43], [13, 79], [72, 22], [48, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [73, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [40, 79, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![460, 135, 77]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -5, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-30, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-30, 1, 0]] 
 ![![127, 0, 0], ![97, 1, 0], ![81, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-30, 1, 0], ![0, -30, 3], ![105, -21, -30]]]
  hmulB := by decide  
  f := ![![![2581, -86, 0], ![10922, 0, 0]], ![![2011, -67, 0], ![8510, 0, 0]], ![![1683, -36, -2], ![7122, 85, 0]]]
  g := ![![![1, 0, 0], ![-97, 127, 0], ![-81, 0, 127]], ![![-1, 1, 0], ![21, -30, 3], ![36, -21, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![67, 10, 1]] ![![127, 0, 0], ![-30, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3810, 127, 0]], ![![8509, 1270, 127], ![-1905, -254, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-30, 1, 0]]], ![![![67, 10, 1]], ![![-15, -2, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [84, 23, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 104, 24], [91, 26, 107], [0, 1]]
 g := ![![[41, 94, 46], [7, 79, 91], [59, 7], [104, 9], [46, 46], [53, 1], []], ![[20, 90, 123, 69], [86, 72, 109, 85], [123, 108], [48, 74], [65, 114], [92, 21], [19, 52]], ![[105, 30, 123, 34], [102, 62, 6, 113], [118, 65], [89, 114], [36, 33], [15, 74], [67, 52]]]
 h' := ![![[93, 104, 24], [67, 26, 96], [81, 47, 22], [94, 97, 20], [70, 84, 128], [2, 7, 35], [0, 0, 1], [0, 1]], ![[91, 26, 107], [76, 23, 107], [60, 128, 128], [49, 92, 97], [85, 96, 104], [49, 3, 30], [110, 129, 26], [93, 104, 24]], ![[0, 1], [99, 82, 59], [106, 87, 112], [18, 73, 14], [17, 82, 30], [91, 121, 66], [33, 2, 104], [91, 26, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 111], []]
 b := ![[], [97, 26, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [84, 23, 78, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-373350, 140170, -28034]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2850, 1070, -214]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [86, 97, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 110, 109], [62, 26, 28], [0, 1]]
 g := ![![[82, 60, 69], [17, 74], [82, 119], [96, 84, 50], [9, 72], [134, 1], []], ![[9, 6, 135, 93], [46, 118], [18, 72], [80, 25, 0, 78], [122, 11], [80, 128], [119, 99]], ![[17, 33, 92, 109], [38, 88], [119, 115], [107, 30, 64, 129], [98, 130], [118, 44], [63, 99]]]
 h' := ![![[72, 110, 109], [49, 97, 84], [135, 96, 99], [101, 119, 121], [30, 75, 18], [121, 68, 49], [0, 0, 1], [0, 1]], ![[62, 26, 28], [135, 38, 16], [23, 104, 23], [8, 6, 88], [18, 22, 12], [57, 45, 55], [19, 30, 26], [72, 110, 109]], ![[0, 1], [24, 2, 37], [2, 74, 15], [57, 12, 65], [49, 40, 107], [95, 24, 33], [70, 107, 110], [62, 26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 105], []]
 b := ![[], [21, 43, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [86, 97, 3, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5206, 137, -137]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 1, -1]
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



lemma PB181I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB181I2 : PrimesBelowBoundCertificateInterval O 79 137 181 where
  m := 11
  g := ![1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB181I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI103N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I101N1, I103N0, I103N1, I109N1, I113N1, I127N1]
  Il := ![[], [I89N1], [], [I101N1], [I103N0, I103N1, I103N1], [], [I109N1], [I113N1], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
