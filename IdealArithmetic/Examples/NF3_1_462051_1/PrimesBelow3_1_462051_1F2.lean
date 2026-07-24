
import IdealArithmetic.Examples.NF3_1_462051_1.RI3_1_462051_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [8, 48, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 49, 54], [56, 33, 29], [0, 1]]
 g := ![![[16, 26, 61], [75, 20, 78], [22, 44], [80, 75], [73, 11, 1], []], ![[55, 64, 40, 71], [44, 41, 41, 15], [63, 16], [36, 7], [6, 49, 40, 42], [18, 11]], ![[61, 51, 39, 51], [75, 0, 68, 69], [10, 11], [57, 77], [3, 55, 50, 75], [43, 11]]]
 h' := ![![[38, 49, 54], [64, 58, 71], [0, 14, 59], [33, 14, 25], [80, 60, 18], [0, 0, 1], [0, 1]], ![[56, 33, 29], [31, 39, 80], [42, 60, 47], [31, 17, 4], [30, 48, 16], [55, 33, 33], [38, 49, 54]], ![[0, 1], [20, 69, 15], [10, 9, 60], [67, 52, 54], [78, 58, 49], [53, 50, 49], [56, 33, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 58], []]
 b := ![[], [51, 37, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [8, 48, 72, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18592, 747, 747]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-224, 9, 9]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![3, 22, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![3, 22, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![3, 22, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![3, 22, 1], ![155, 39, 22], ![3410, 947, 39]]]
  hmulB := by decide  
  f := ![![![-2, -22, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -22, 89]], ![![0, 0, 1], ![1, -5, 22], ![37, 1, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [80, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 88], [0, 1]]
 g := ![![[75, 79], [84], [68], [51, 5], [34, 34], [1]], ![[0, 10], [84], [68], [44, 84], [22, 55], [1]]]
 h' := ![![[52, 88], [4, 41], [7, 66], [14, 35], [39, 19], [9, 52], [0, 1]], ![[0, 1], [0, 48], [57, 23], [54, 54], [48, 70], [43, 37], [52, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [16, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [80, 37, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1816, 893, 433]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -97, 433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-22, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-22, 1, 0]] 
 ![![89, 0, 0], ![67, 1, 0], ![50, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-22, 1, 0], ![0, -22, 1], ![155, 36, -22]]]
  hmulB := by decide  
  f := ![![![1915, -87, 0], ![7743, 0, 0]], ![![1453, -66, 0], ![5875, 0, 0]], ![![1106, -50, 0], ![4472, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 89, 0], ![-50, 0, 89]], ![![-1, 1, 0], ![16, -22, 1], ![-13, 36, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![3, 22, 1]] ![![89, 0, 0], ![-22, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1958, 89, 0]], ![![267, 1958, 89], ![89, -445, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-22, 1, 0]]], ![![![3, 22, 1]], ![![1, -5, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-33, 10, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-33, 10, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![64, 10, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-33, 10, 1], ![155, 3, 10], ![1550, 515, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -10, 97]], ![![-1, 0, 1], ![-5, -1, 10], ![14, 5, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [81, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 96], [0, 1]]
 g := ![![[78, 6], [8], [62], [43], [81], [84, 1]], ![[0, 91], [8], [62], [43], [81], [71, 96]]]
 h' := ![![[84, 96], [23, 54], [34, 28], [20, 16], [37, 72], [83, 88], [0, 1]], ![[0, 1], [0, 43], [58, 69], [6, 81], [71, 25], [6, 9], [84, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [32, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [81, 13, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3035, -32, 152]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69, -16, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-10, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-10, 1, 0]] 
 ![![97, 0, 0], ![87, 1, 0], ![94, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-10, 1, 0], ![0, -10, 1], ![155, 36, -10]]]
  hmulB := by decide  
  f := ![![![741, -74, 0], ![7178, 0, 0]], ![![651, -65, 0], ![6306, 0, 0]], ![![702, -70, 0], ![6800, 1, 0]]]
  g := ![![![1, 0, 0], ![-87, 97, 0], ![-94, 0, 97]], ![![-1, 1, 0], ![8, -10, 1], ![-21, 36, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-33, 10, 1]] ![![97, 0, 0], ![-10, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-970, 97, 0]], ![![-3201, 970, 97], ![485, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-10, 1, 0]]], ![![![-33, 10, 1]], ![![5, -1, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [41, 70, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 16, 90], [71, 84, 11], [0, 1]]
 g := ![![[2, 81, 76], [33, 33], [83, 57, 80], [71, 21], [7, 20], [1]], ![[2, 39, 9, 55], [64, 87], [9, 48, 14, 39], [41, 5], [3, 82], [64, 0, 47, 83]], ![[41, 0, 48, 73], [10, 96], [84, 40, 9, 55], [13, 30], [0, 56], [88, 79, 95, 18]]]
 h' := ![![[19, 16, 90], [12, 93, 50], [31, 28, 72], [14, 82, 79], [81, 87, 83], [60, 31, 90], [0, 1]], ![[71, 84, 11], [23, 57, 46], [18, 68, 84], [58, 59, 78], [27, 73, 56], [94, 21, 48], [19, 16, 90]], ![[0, 1], [48, 52, 5], [85, 5, 46], [92, 61, 45], [25, 42, 63], [96, 49, 64], [71, 84, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 12], []]
 b := ![[], [93, 35, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [41, 70, 11, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-510757, -251086, -26866]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5057, -2486, -266]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [60, 74, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 91, 50], [91, 11, 53], [0, 1]]
 g := ![![[1, 79, 91], [7, 40, 76], [10, 46, 49], [52, 1], [71, 34], [1]], ![[62, 83, 62, 58], [84, 5, 62, 46], [77, 94, 96, 25], [52, 29], [84, 55], [37, 73, 59, 61]], ![[19, 25, 37, 84], [16, 56, 35, 62], [71, 71, 53, 10], [90, 72], [17, 97], [4, 81, 63, 42]]]
 h' := ![![[43, 91, 50], [95, 84, 83], [18, 85, 30], [86, 64, 7], [61, 41, 102], [43, 29, 31], [0, 1]], ![[91, 11, 53], [0, 34, 66], [15, 95, 48], [0, 93, 84], [37, 3, 82], [37, 66, 40], [43, 91, 50]], ![[0, 1], [27, 88, 57], [60, 26, 25], [19, 49, 12], [28, 59, 22], [92, 8, 32], [91, 11, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 74], []]
 b := ![[], [65, 24, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [60, 74, 72, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18540, 721, 721]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-180, 7, 7]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-33, 18, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-33, 18, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![74, 18, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-33, 18, 1], ![155, 3, 18], ![2790, 803, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -18, 107]], ![![-1, 0, 1], ![-11, -3, 18], ![24, 7, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [83, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 106], [0, 1]]
 g := ![![[11, 49], [77, 23], [41], [18, 34], [10], [50, 1]], ![[0, 58], [50, 84], [41], [6, 73], [10], [100, 106]]]
 h' := ![![[50, 106], [29, 100], [37, 39], [4, 83], [20, 81], [23, 63], [0, 1]], ![[0, 1], [0, 7], [61, 68], [88, 24], [4, 26], [70, 44], [50, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [40, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [83, 57, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6031, 2644, 456]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-259, -52, 456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-18, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-18, 1, 0]] 
 ![![107, 0, 0], ![89, 1, 0], ![104, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-18, 1, 0], ![0, -18, 1], ![155, 36, -18]]]
  hmulB := by decide  
  f := ![![![145, -8, 0], ![856, 0, 0]], ![![127, -7, 0], ![750, 0, 0]], ![![148, -8, 0], ![874, 1, 0]]]
  g := ![![![1, 0, 0], ![-89, 107, 0], ![-104, 0, 107]], ![![-1, 1, 0], ![14, -18, 1], ![-11, 36, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-33, 18, 1]] ![![107, 0, 0], ![-18, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1926, 107, 0]], ![![-3531, 1926, 107], ![749, -321, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-18, 1, 0]]], ![![![-33, 18, 1]], ![![7, -3, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![11, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![11, 1, 0]] 
 ![![109, 0, 0], ![11, 1, 0], ![97, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![11, 1, 0], ![0, 11, 1], ![155, 36, 11]]]
  hmulB := by decide  
  f := ![![![89, 8, 0], ![-872, 0, 0]], ![![-11, -1, 0], ![110, 0, 0]], ![![79, 7, 0], ![-774, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 109, 0], ![-97, 0, 109]], ![![0, 1, 0], ![-2, 11, 1], ![-12, 36, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-22, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-22, 1, 0]] 
 ![![109, 0, 0], ![87, 1, 0], ![61, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-22, 1, 0], ![0, -22, 1], ![155, 36, -22]]]
  hmulB := by decide  
  f := ![![![155, -7, 0], ![763, 0, 0]], ![![133, -6, 0], ![655, 0, 0]], ![![115, -5, 0], ![567, 1, 0]]]
  g := ![![![1, 0, 0], ![-87, 109, 0], ![-61, 0, 109]], ![![-1, 1, 0], ![17, -22, 1], ![-15, 36, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![11, 1, 0]] ![![109, 0, 0], ![11, 1, 0]]
  ![![109, 0, 0], ![12, 22, 1]] where
 M := ![![![11881, 0, 0], ![1199, 109, 0]], ![![1199, 109, 0], ![121, 22, 1]]]
 hmul := by decide  
 g := ![![![![97, -22, -1], ![109, 0, 0]], ![![-1, -21, -1], ![109, 0, 0]]], ![![![-1, -21, -1], ![109, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![12, 22, 1]] ![![109, 0, 0], ![-22, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2398, 109, 0]], ![![1308, 2398, 109], ![-109, -436, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-22, 1, 0]]], ![![![12, 22, 1]], ![![-1, -4, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-18, -40, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-18, -40, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![95, 73, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-18, -40, 1], ![155, 18, -40], ![-6200, -1285, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -73, 113]], ![![-1, -1, 1], ![35, 26, -40], ![-70, -23, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [110, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 112], [0, 1]]
 g := ![![[59, 109], [25], [95], [25], [71, 57], [64, 1]], ![[29, 4], [25], [95], [25], [103, 56], [15, 112]]]
 h' := ![![[64, 112], [90, 30], [44, 108], [18, 35], [100, 108], [79, 31], [0, 1]], ![[0, 1], [89, 83], [63, 5], [111, 78], [6, 5], [29, 82], [64, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [92, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [110, 49, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-868, 80, -2]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 2, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![40, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![40, 1, 0]] 
 ![![113, 0, 0], ![40, 1, 0], ![95, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![40, 1, 0], ![0, 40, 1], ![155, 36, 40]]]
  hmulB := by decide  
  f := ![![![1641, 41, 0], ![-4633, 0, 0]], ![![520, 13, 0], ![-1468, 0, 0]], ![![1335, 33, 0], ![-3769, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 113, 0], ![-95, 0, 113]], ![![0, 1, 0], ![-15, 40, 1], ![-45, 36, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-18, -40, 1]] ![![113, 0, 0], ![40, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4520, 113, 0]], ![![-2034, -4520, 113], ![-565, -1582, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![40, 1, 0]]], ![![![-18, -40, 1]], ![![-5, -14, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![8, -60, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![8, -60, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![8, 67, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![8, -60, 1], ![155, 44, -60], ![-9300, -2005, 44]]]
  hmulB := by decide  
  f := ![![![-7, 60, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -67, 127]], ![![0, -1, 1], ![5, 32, -60], ![-76, -39, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [81, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 126], [0, 1]]
 g := ![![[124, 69], [85, 103], [57, 32], [27, 69], [86, 76], [116, 1]], ![[0, 58], [95, 24], [86, 95], [30, 58], [12, 51], [105, 126]]]
 h' := ![![[116, 126], [100, 113], [82, 105], [99, 63], [19, 14], [2, 40], [0, 1]], ![[0, 1], [0, 14], [70, 22], [41, 64], [119, 113], [70, 87], [116, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [72, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [81, 11, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![701, 775, 167]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -82, 167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![60, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![60, 1, 0]] 
 ![![127, 0, 0], ![60, 1, 0], ![83, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![60, 1, 0], ![0, 60, 1], ![155, 36, 60]]]
  hmulB := by decide  
  f := ![![![1681, 28, 0], ![-3556, 0, 0]], ![![780, 13, 0], ![-1650, 0, 0]], ![![989, 16, 0], ![-2092, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 127, 0], ![-83, 0, 127]], ![![0, 1, 0], ![-29, 60, 1], ![-55, 36, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![8, -60, 1]] ![![127, 0, 0], ![60, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![7620, 127, 0]], ![![1016, -7620, 127], ![635, -3556, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![60, 1, 0]]], ![![![8, -60, 1]], ![![5, -28, 0]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [77, 75, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 87, 33], [90, 43, 98], [0, 1]]
 g := ![![[103, 113, 80], [78, 40, 35], [125, 64], [105, 21], [25, 52], [19, 1], []], ![[100, 7, 125, 44], [63, 1, 94, 107], [39, 35], [3, 109], [109, 35], [32, 15], [102, 41]], ![[76, 0, 39, 97], [123, 23, 112, 96], [27, 123], [80, 94], [21, 28], [34, 102], [37, 41]]]
 h' := ![![[60, 87, 33], [20, 118, 39], [128, 121, 64], [37, 71, 8], [0, 80, 26], [109, 70, 24], [0, 0, 1], [0, 1]], ![[90, 43, 98], [97, 14, 69], [14, 8, 64], [2, 97, 67], [44, 38, 90], [70, 33, 67], [69, 26, 43], [60, 87, 33]], ![[0, 1], [65, 130, 23], [63, 2, 3], [96, 94, 56], [19, 13, 15], [123, 28, 40], [11, 105, 87], [90, 43, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 109], []]
 b := ![[], [87, 7, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [77, 75, 112, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1363317, -111350, 43230]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10407, -850, 330]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [68, 131, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 113, 133], [4, 23, 4], [0, 1]]
 g := ![![[77, 80, 7], [6, 118], [66, 4], [97, 93, 22], [14, 9], [111, 1], []], ![[47, 23, 5, 73], [66, 39], [113, 32], [61, 3, 97, 74], [122, 25], [72, 118], [50, 16]], ![[103, 109, 55, 65], [94, 2], [109, 88], [127, 64, 126, 135], [76, 4], [17, 28], [42, 16]]]
 h' := ![![[107, 113, 133], [76, 69, 125], [22, 43, 23], [117, 26, 135], [39, 90, 76], [124, 50, 134], [0, 0, 1], [0, 1]], ![[4, 23, 4], [58, 110, 133], [5, 127, 83], [90, 127, 124], [98, 127, 18], [96, 132, 5], [103, 104, 23], [107, 113, 133]], ![[0, 1], [45, 95, 16], [86, 104, 31], [10, 121, 15], [60, 57, 43], [76, 92, 135], [37, 33, 113], [4, 23, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 120], []]
 b := ![[], [63, 58, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [68, 131, 26, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4658, 11782, 4658]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, 86, 34]
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



lemma PB193I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB193I2 : PrimesBelowBoundCertificateInterval O 79 137 193 where
  m := 11
  g := ![1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB193I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N0, I109N1]
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
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
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
      exact NI97N1
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
  β := ![I89N1, I97N1, I107N1, I109N0, I109N1, I113N1, I127N1]
  Il := ![[], [I89N1], [I97N1], [], [], [I107N1], [I109N0, I109N0, I109N1], [I113N1], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
