
import IdealArithmetic.Examples.NF3_1_547575_2.RI3_1_547575_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [27, 30, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 80, 17], [80, 2, 66], [0, 1]]
 g := ![![[80, 49, 31], [53, 41, 7], [30, 28], [72, 75], [78, 78, 1], []], ![[70, 82, 78, 25], [24, 79, 54, 27], [13, 64], [46, 25], [54, 32, 35, 68], [30, 40]], ![[6, 15, 21, 53], [3, 5, 40, 73], [61, 23], [38, 31], [34, 22, 78, 13], [64, 40]]]
 h' := ![![[81, 80, 17], [63, 73, 23], [23, 75, 16], [13, 57, 51], [52, 36, 65], [0, 0, 1], [0, 1]], ![[80, 2, 66], [54, 1, 42], [8, 76, 62], [44, 57, 75], [46, 41, 78], [24, 24, 2], [81, 80, 17]], ![[0, 1], [64, 9, 18], [16, 15, 5], [70, 52, 40], [10, 6, 23], [24, 59, 80], [80, 2, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 8], []]
 b := ![[], [15, 3, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [27, 30, 5, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32619, -64906, -45318]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![393, -782, -546]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [13, 52, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 33, 78], [75, 55, 11], [0, 1]]
 g := ![![[38, 21, 49], [39, 87], [10, 45], [71, 65, 16], [1, 26, 1], []], ![[63, 26, 41, 57], [62, 22], [18, 45], [8, 84, 53, 72], [72, 23, 77, 11], [17, 32]], ![[42, 22, 12, 10], [28, 45], [], [27, 37, 33, 80], [47, 42, 60, 53], [84, 32]]]
 h' := ![![[40, 33, 78], [71, 44, 7], [69, 69, 40], [56, 82, 32], [76, 55, 85], [0, 0, 1], [0, 1]], ![[75, 55, 11], [3, 63, 79], [50, 74, 17], [27, 18, 57], [53, 15, 65], [44, 5, 55], [40, 33, 78]], ![[0, 1], [36, 71, 3], [20, 35, 32], [51, 78], [42, 19, 28], [83, 84, 33], [75, 55, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 64], []]
 b := ![[], [37, 53, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [13, 52, 63, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2759, 9256, 67462]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, 104, 758]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![57, -10, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![57, -10, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![57, 87, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![57, -10, 1], ![24, 6, -20], ![-252, 422, 16]]]
  hmulB := by decide  
  f := ![![![-56, 10, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -87, 97]], ![![0, -1, 1], ![12, 18, -20], ![-12, -10, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [18, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 96], [0, 1]]
 g := ![![[34, 27], [36], [25], [31], [81], [67, 1]], ![[0, 70], [36], [25], [31], [81], [37, 96]]]
 h' := ![![[67, 96], [27, 30], [53, 91], [55, 5], [15, 15], [55, 9], [0, 1]], ![[0, 1], [0, 67], [39, 6], [2, 92], [50, 82], [76, 88], [67, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [33, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [18, 30, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2182, 12, 57]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -51, 57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![20, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![20, 1, 0]] 
 ![![97, 0, 0], ![20, 1, 0], ![81, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![20, 1, 0], ![0, 21, 2], ![24, -41, 20]]]
  hmulB := by decide  
  f := ![![![561, 28, 0], ![-2716, 0, 0]], ![![100, 5, 0], ![-484, 0, 0]], ![![473, 13, -1], ![-2290, 49, 0]]]
  g := ![![![1, 0, 0], ![-20, 97, 0], ![-81, 0, 97]], ![![0, 1, 0], ![-6, 21, 2], ![-8, -41, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![57, -10, 1]] ![![97, 0, 0], ![20, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1940, 97, 0]], ![![5529, -970, 97], ![1164, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![20, 1, 0]]], ![![![57, -10, 1]], ![![12, -2, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [73, 23, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 79, 97], [84, 21, 4], [0, 1]]
 g := ![![[73, 9, 68], [20, 23], [92, 22, 82], [42, 47], [21, 49], [1]], ![[6, 31, 86, 65], [84, 76], [72, 3, 61, 54], [92, 88], [77, 56], [46, 24, 11, 37]], ![[93, 84, 78, 14], [66, 13], [42, 35, 20, 56], [80, 25], [98, 17], [62, 66, 42, 64]]]
 h' := ![![[24, 79, 97], [30, 17, 13], [51, 35, 86], [11, 31, 53], [59, 5, 42], [28, 78, 7], [0, 1]], ![[84, 21, 4], [42, 45, 3], [66, 44, 50], [34, 24, 80], [65, 55, 54], [63, 79, 37], [24, 79, 97]], ![[0, 1], [75, 39, 85], [34, 22, 66], [61, 46, 69], [12, 41, 5], [55, 45, 57], [84, 21, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 37], []]
 b := ![[], [80, 2, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [73, 23, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67367, -177962, -307040]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![667, -1762, -3040]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [74, 55, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 45, 34], [58, 57, 69], [0, 1]]
 g := ![![[81, 18, 34], [50, 83, 66], [100, 44, 49], [20, 33], [16, 2], [1]], ![[71, 51, 1, 46], [45, 36, 102, 15], [58, 21, 101, 46], [53, 16], [58, 66], [93, 9, 67, 61]], ![[99, 76, 70, 37], [13, 89, 5, 95], [64, 98, 10, 43], [36, 68], [17, 7], [91, 82, 70, 42]]]
 h' := ![![[83, 45, 34], [8, 16, 31], [16, 18, 90], [88, 32, 7], [69, 5, 62], [29, 48, 38], [0, 1]], ![[58, 57, 69], [95, 95, 45], [100, 72, 77], [25, 23, 45], [62, 5, 99], [53, 15, 90], [83, 45, 34]], ![[0, 1], [65, 95, 27], [63, 13, 39], [96, 48, 51], [59, 93, 45], [94, 40, 78], [58, 57, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 89], []]
 b := ![[], [20, 95, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [74, 55, 65, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43466, -87756, -67053]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![422, -852, -651]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-5, 19, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-5, 19, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![102, 19, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-5, 19, 1], ![24, -27, 38], ![444, -767, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -19, 107]], ![![-1, 0, 1], ![-36, -7, 38], ![48, 1, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [60, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 106], [0, 1]]
 g := ![![[57, 87], [106, 75], [35], [36, 34], [10], [4, 1]], ![[84, 20], [85, 32], [35], [65, 73], [10], [8, 106]]]
 h' := ![![[4, 106], [60, 27], [12, 90], [87, 28], [76, 81], [81, 63], [0, 1]], ![[0, 1], [61, 80], [51, 17], [92, 79], [79, 26], [12, 44], [4, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [21, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [60, 103, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15032, -26648, -15076]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14512, 2428, -15076]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-38, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-38, 1, 0]] 
 ![![107, 0, 0], ![69, 1, 0], ![46, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-38, 1, 0], ![0, -37, 2], ![24, -41, -38]]]
  hmulB := by decide  
  f := ![![![2547, -67, 0], ![7169, 0, 0]], ![![1673, -44, 0], ![4709, 0, 0]], ![![1090, -10, -1], ![3068, 54, 0]]]
  g := ![![![1, 0, 0], ![-69, 107, 0], ![-46, 0, 107]], ![![-1, 1, 0], ![23, -37, 2], ![43, -41, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-5, 19, 1]] ![![107, 0, 0], ![-38, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4066, 107, 0]], ![![-535, 2033, 107], ![214, -749, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-38, 1, 0]]], ![![![-5, 19, 1]], ![![2, -7, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-18, -37, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-18, -37, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![91, 72, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-18, -37, 1], ![24, -96, -74], ![-900, 1529, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -72, 109]], ![![-1, -1, 1], ![62, 48, -74], ![41, 53, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [54, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 108], [0, 1]]
 g := ![![[32, 9], [84], [22, 74], [89, 80], [38], [16, 1]], ![[67, 100], [84], [7, 35], [61, 29], [38], [32, 108]]]
 h' := ![![[16, 108], [54, 3], [11, 53], [99, 69], [83, 25], [8, 93], [0, 1]], ![[0, 1], [102, 106], [96, 56], [4, 40], [47, 84], [79, 16], [16, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [44, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [54, 93, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46, 34, 58]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -38, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-35, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-35, 1, 0]] 
 ![![109, 0, 0], ![74, 1, 0], ![59, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-35, 1, 0], ![0, -34, 2], ![24, -41, -35]]]
  hmulB := by decide  
  f := ![![![3326, -95, 0], ![10355, 0, 0]], ![![2276, -65, 0], ![7086, 0, 0]], ![![1826, -35, -1], ![5685, 55, 0]]]
  g := ![![![1, 0, 0], ![-74, 109, 0], ![-59, 0, 109]], ![![-1, 1, 0], ![22, -34, 2], ![47, -41, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-18, -37, 1]] ![![109, 0, 0], ![-35, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3815, 109, 0]], ![![-1962, -4033, 109], ![654, 1199, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-35, 1, 0]]], ![![![-18, -37, 1]], ![![6, 11, -1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33823694160403, 242888050574, 827414201888]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![33823694160403, 242888050574, 827414201888]] 
 ![![113, 0, 0], ![0, 113, 0], ![27, 13, 1]] where
  M :=![![![33823694160403, 242888050574, 827414201888], ![19857940845312, 142599933569, 485776101148], ![-4099657208880, -29439650878, -100288117005]]]
  hmulB := by decide  
  f := ![![![316523, -522538, 80360]], ![![1928640, -3500775, -1045076]], ![![177993, -329471, -127385]]]
  g := ![![![101623988579, -93039792690, 827414201888], ![59663593932, -54623799835, 485776101148], ![-12317504865, 11277043099, -100288117005]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [53, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 112], [0, 1]]
 g := ![![[59, 32], [51], [25], [44], [24, 18], [37, 1]], ![[0, 81], [51], [25], [44], [12, 95], [74, 112]]]
 h' := ![![[37, 112], [23, 91], [63, 27], [91, 5], [84, 65], [73, 73], [0, 1]], ![[0, 1], [0, 22], [45, 86], [50, 108], [3, 48], [62, 40], [37, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [106, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [53, 76, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![473, -693, -627]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154, 66, -627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![316523, -522538, 80360]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![316523, -522538, 80360]] 
 ![![113, 0, 0], ![87, 1, 0], ![14, 0, 1]] where
  M :=![![![316523, -522538, 80360], ![1928640, -3500775, -1045076], ![-13505232, 22388378, -2978237]]]
  hmulB := by decide  
  f := ![![![33823694160403, 242888050574, 827414201888]], ![![26216985246021, 188264250739, 641334616508]], ![![4154266026874, 29831796966, 101623988579]]]
  g := ![![![395153, -522538, 80360], ![2841833, -3500775, -1045076], ![-16987600, 22388378, -2978237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![33823694160403, 242888050574, 827414201888]] ![![316523, -522538, 80360]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [91, 109, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 8, 4], [39, 118, 123], [0, 1]]
 g := ![![[9, 97, 99], [72, 20, 100], [118, 96, 49], [44, 32, 107], [88, 124, 70], [1]], ![[46, 64, 45, 37], [40, 120, 85, 76], [57, 6, 19, 74], [35, 116, 6, 100], [47, 49, 19, 76], [63, 54, 121, 64]], ![[18, 23, 6, 126], [4, 105, 79, 83], [113, 41, 85, 56], [0, 89, 81, 105], [116, 116, 54, 66], [8, 123, 85, 63]]]
 h' := ![![[70, 8, 4], [52, 58, 37], [57, 36, 117], [60, 88, 7], [120, 105, 19], [36, 18, 109], [0, 1]], ![[39, 118, 123], [74, 11, 26], [54, 26, 107], [74, 100, 35], [59, 17, 122], [82, 28, 107], [70, 8, 4]], ![[0, 1], [114, 58, 64], [3, 65, 30], [93, 66, 85], [51, 5, 113], [44, 81, 38], [39, 118, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 5], []]
 b := ![[], [69, 22, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [91, 109, 18, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![702437, -1262888, -321310]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5531, -9944, -2530]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [74, 68, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 15, 79], [107, 115, 52], [0, 1]]
 g := ![![[87, 19, 12], [23, 10, 3], [113, 84], [117, 21], [112, 58], [88, 1], []], ![[15, 115, 129, 88], [111, 40, 112, 31], [85, 81], [19, 25], [98, 5], [19, 125], [68, 84]], ![[129, 47, 119, 80], [22, 120, 51, 94], [117, 15], [87, 44], [67, 114], [16, 94], [95, 84]]]
 h' := ![![[112, 15, 79], [1, 118, 55], [8, 7, 38], [95, 27, 52], [99, 70, 26], [38, 99, 78], [0, 0, 1], [0, 1]], ![[107, 115, 52], [103, 7, 58], [13, 4, 76], [88, 122, 122], [70, 57, 5], [95, 78, 23], [45, 118, 115], [112, 15, 79]], ![[0, 1], [91, 6, 18], [82, 120, 17], [116, 113, 88], [129, 4, 100], [41, 85, 30], [96, 13, 15], [107, 115, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 103], []]
 b := ![[], [9, 101, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [74, 68, 43, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10218, 0, 0]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 0, 0]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [77, 31, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 77, 44], [48, 59, 93], [0, 1]]
 g := ![![[85, 111, 112], [55, 11], [70, 17], [76, 52, 76], [39, 107], [79, 1], []], ![[30, 14, 51, 120], [30, 88], [6, 76], [47, 89, 77, 119], [124, 88], [115, 56], [115, 18]], ![[114, 95, 26, 72], [73, 105], [41, 65], [116, 1, 117, 69], [0, 38], [120, 38], [66, 18]]]
 h' := ![![[31, 77, 44], [5, 101, 89], [104, 20, 55], [39, 15, 90], [22, 29, 58], [82, 77, 45], [0, 0, 1], [0, 1]], ![[48, 59, 93], [92, 107, 105], [22, 25, 15], [115, 21, 79], [101, 50, 40], [14, 19, 15], [52, 97, 59], [31, 77, 44]], ![[0, 1], [101, 66, 80], [70, 92, 67], [79, 101, 105], [32, 58, 39], [13, 41, 77], [99, 40, 77], [48, 59, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 2], []]
 b := ![[], [21, 13, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [77, 31, 58, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![418535, -800354, -424700]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3055, -5842, -3100]
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



lemma PB210I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB210I2 : PrimesBelowBoundCertificateInterval O 79 137 210 where
  m := 11
  g := ![1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB210I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
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
    · exact ![571787]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I97N1, I107N1, I109N1, I113N1]
  Il := ![[], [], [I97N1], [], [], [I107N1], [I109N1], [I113N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
