
import IdealArithmetic.Examples.NF3_1_197127_1.RI3_1_197127_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [66, 58, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 39, 45], [76, 43, 38], [0, 1]]
 g := ![![[37, 81, 63], [53, 12, 30], [4, 36], [79, 31], [46, 41, 1], []], ![[81, 30, 61, 20], [17, 55, 36, 22], [82, 10], [49, 44], [67, 33, 54, 39], [49, 33]], ![[65, 19, 62, 75], [2, 74, 40, 78], [34, 65], [1, 63], [30, 47, 70, 30], [56, 33]]]
 h' := ![![[48, 39, 45], [71, 52, 35], [10, 2, 69], [78, 71, 6], [35, 21, 23], [0, 0, 1], [0, 1]], ![[76, 43, 38], [63, 30, 27], [12, 14, 69], [64, 10, 50], [71, 23, 25], [66, 52, 43], [48, 39, 45]], ![[0, 1], [48, 1, 21], [9, 67, 28], [26, 2, 27], [3, 39, 35], [5, 31, 39], [76, 43, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 4], []]
 b := ![[], [78, 40, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [66, 58, 42, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61420, 0, -1245]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-740, 0, -15]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [44, 39, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 77, 34], [78, 11, 55], [0, 1]]
 g := ![![[66, 15, 55], [77, 73], [17, 67], [9, 56, 55], [0, 22, 1], []], ![[36, 27, 82, 10], [70, 5], [11, 16], [67, 67, 23, 68], [31, 45, 67, 20], [52, 88]], ![[11, 59, 61, 18], [36, 72], [13, 79], [82, 10, 74, 1], [62, 41, 37, 88], [31, 88]]]
 h' := ![![[33, 77, 34], [14, 9, 77], [51, 68, 47], [49, 33, 44], [0, 11, 77], [0, 0, 1], [0, 1]], ![[78, 11, 55], [14, 7, 85], [54, 76, 70], [2, 13, 4], [66, 72, 64], [47, 72, 11], [33, 77, 34]], ![[0, 1], [57, 73, 16], [67, 34, 61], [85, 43, 41], [21, 6, 37], [3, 17, 77], [78, 11, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 21], []]
 b := ![[], [79, 60, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [44, 39, 67, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![778750, 293077, 19758]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8750, 3293, 222]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![7, 8, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![7, 8, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![7, 8, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![7, 8, 1], ![78, 6, 25], ![743, 87, 23]]]
  hmulB := by decide  
  f := ![![![-6, -8, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -8, 97]], ![![0, 0, 1], ![-1, -2, 25], ![6, -1, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [30, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 96], [0, 1]]
 g := ![![[29, 27], [27], [16], [86], [53], [3, 1]], ![[13, 70], [27], [16], [86], [53], [6, 96]]]
 h' := ![![[3, 96], [72, 67], [94, 67], [63, 4], [11, 59], [7, 76], [0, 1]], ![[0, 1], [79, 30], [4, 30], [75, 93], [91, 38], [41, 21], [3, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [76, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [30, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![223968, 137471, 29224]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![200, -993, 29224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-25, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-25, 1, 0]] 
 ![![97, 0, 0], ![72, 1, 0], ![74, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-25, 1, 0], ![-1, -26, 3], ![86, 7, -24]]]
  hmulB := by decide  
  f := ![![![-1208, -31434, 3627], ![0, -117273, 0]], ![![-896, -23322, 2691], ![1, -87009, 0]], ![![-911, -23981, 2767], ![41, -89466, 0]]]
  g := ![![![1, 0, 0], ![-72, 97, 0], ![-74, 0, 97]], ![![-1, 1, 0], ![17, -26, 3], ![14, 7, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![7, 8, 1]] ![![97, 0, 0], ![-25, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2425, 97, 0]], ![![679, 776, 97], ![-97, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-25, 1, 0]]], ![![![7, 8, 1]], ![![-1, -2, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [90, 30, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 93, 51], [94, 7, 50], [0, 1]]
 g := ![![[64, 48, 68], [4, 80], [10, 31, 45], [0, 56], [4, 100], [1]], ![[2, 41, 38, 8], [61, 92], [15, 18, 86, 61], [27, 4], [89, 54], [35, 11, 18, 38]], ![[96, 7, 78, 7], [35, 78], [8, 12, 9, 62], [83, 13], [84, 36], [65, 62, 57, 63]]]
 h' := ![![[98, 93, 51], [24, 73, 88], [9, 46, 79], [56, 65, 34], [64, 17, 64], [11, 71, 91], [0, 1]], ![[94, 7, 50], [28, 90, 97], [93, 19, 71], [78, 48, 18], [65, 42, 2], [55, 67, 16], [98, 93, 51]], ![[0, 1], [83, 39, 17], [100, 36, 52], [37, 89, 49], [29, 42, 35], [69, 64, 95], [94, 7, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 85], []]
 b := ![[], [82, 87, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [90, 30, 10, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1137159, -178972, 808]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11259, -1772, 8]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [101, 55, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 41, 79], [71, 61, 24], [0, 1]]
 g := ![![[98, 87, 15], [102, 47, 100], [67, 1, 30], [66, 56], [57, 13], [1]], ![[53, 32, 23, 7], [2, 101, 1, 38], [93, 48, 15, 26], [27, 56], [34, 36], [34, 68, 84, 81]], ![[0, 52, 11, 21], [19, 69, 93, 45], [25, 88, 74, 77], [], [87, 38], [62, 37, 42, 22]]]
 h' := ![![[93, 41, 79], [101, 80, 18], [31, 63, 10], [48, 24, 37], [15, 70, 57], [2, 48, 61], [0, 1]], ![[71, 61, 24], [40, 66, 2], [29, 65, 25], [51, 31, 33], [93, 74, 46], [98, 60, 97], [93, 41, 79]], ![[0, 1], [0, 60, 83], [22, 78, 68], [83, 48, 33], [17, 62], [7, 98, 48], [71, 61, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 53], []]
 b := ![[], [61, 93, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [101, 55, 42, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61388, 0, -1236]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-596, 0, -12]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-18, -6, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-18, -6, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![89, 101, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-18, -6, 1], ![92, -5, -17], ![-461, -11, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-89, -101, 107]], ![![-1, -1, 1], ![15, 16, -17], ![9, 15, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [14, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 106], [0, 1]]
 g := ![![[0, 23], [], [27], [], [89], [0, 1]], ![[0, 84], [], [27], [], [89], [0, 106]]]
 h' := ![![[0, 106], [0, 39], [50], [0, 53], [38], [0, 93], [0, 1]], ![[0, 1], [0, 68], [50], [0, 54], [38], [0, 14], [0, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [0, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [14, 0, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12955, 1144, 1236]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-907, -1156, 1236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![17, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![17, 1, 0]] 
 ![![107, 0, 0], ![17, 1, 0], ![16, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![17, 1, 0], ![-1, 16, 3], ![86, 7, 18]]]
  hmulB := by decide  
  f := ![![![-2645, 42336, 7938], ![0, -283122, 0]], ![![-420, 6720, 1260], ![1, -44940, 0]], ![![-406, 6330, 1187], ![66, -42336, 0]]]
  g := ![![![1, 0, 0], ![-17, 107, 0], ![-16, 0, 107]], ![![0, 1, 0], ![-3, 16, 3], ![-3, 7, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-18, -6, 1]] ![![107, 0, 0], ![17, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![1819, 107, 0]], ![![-1926, -642, 107], ![-214, -107, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![17, 1, 0]]], ![![![-18, -6, 1]], ![![-2, -1, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-55, 45, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-55, 45, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![54, 45, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-55, 45, 1], ![41, -93, 136], ![3925, 346, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -45, 109]], ![![-1, 0, 1], ![-67, -57, 136], ![37, 4, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [31, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 108], [0, 1]]
 g := ![![[90, 102], [35], [44, 71], [25, 100], [88], [44, 1]], ![[0, 7], [35], [7, 38], [65, 9], [88], [88, 108]]]
 h' := ![![[44, 108], [89, 50], [53, 97], [97, 92], [81, 10], [53, 52], [0, 1]], ![[0, 1], [0, 59], [70, 12], [3, 17], [85, 99], [52, 57], [44, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [84, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [31, 65, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1791, 524, -124]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45, 56, -124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-27, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-27, 1, 0]] 
 ![![109, 0, 0], ![82, 1, 0], ![2, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-27, 1, 0], ![-1, -28, 3], ![86, 7, -26]]]
  hmulB := by decide  
  f := ![![![228, 5599, -600], ![109, 21800, 0]], ![![178, 4199, -450], ![110, 16350, 0]], ![![24, 102, -11], ![82, 400, 0]]]
  g := ![![![1, 0, 0], ![-82, 109, 0], ![-2, 0, 109]], ![![-1, 1, 0], ![21, -28, 3], ![-4, 7, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-55, 45, 1]] ![![109, 0, 0], ![-27, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2943, 109, 0]], ![![-5995, 4905, 109], ![1526, -1308, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-27, 1, 0]]], ![![![-55, 45, 1]], ![![14, -12, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-8, -9, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-8, -9, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![105, 104, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-8, -9, 1], ![95, 8, -26], ![-719, -32, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -104, 113]], ![![-1, -1, 1], ![25, 24, -26], ![2, 8, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [106, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 112], [0, 1]]
 g := ![![[97, 16], [105], [32], [25], [63, 64], [1, 1]], ![[0, 97], [105], [32], [25], [14, 49], [2, 112]]]
 h' := ![![[1, 112], [109, 4], [39, 61], [70, 22], [102, 108], [7, 8], [0, 1]], ![[0, 1], [0, 109], [100, 52], [92, 91], [97, 5], [15, 105], [1, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [39, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [106, 112, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![833, 923, 927]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-854, -845, 927]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![26, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![26, 1, 0]] 
 ![![113, 0, 0], ![26, 1, 0], ![9, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![26, 1, 0], ![-1, 25, 3], ![86, 7, 27]]]
  hmulB := by decide  
  f := ![![![4675, -117501, -14100], ![113, 531100, 0]], ![![1055, -27026, -3243], ![114, 122153, 0]], ![![359, -9359, -1123], ![67, 42300, 0]]]
  g := ![![![1, 0, 0], ![-26, 113, 0], ![-9, 0, 113]], ![![0, 1, 0], ![-6, 25, 3], ![-3, 7, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-8, -9, 1]] ![![113, 0, 0], ![26, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2938, 113, 0]], ![![-904, -1017, 113], ![-113, -226, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![26, 1, 0]]], ![![![-8, -9, 1]], ![![-1, -2, 0]]]]
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


lemma PB126I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 125 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 125 (by omega)

def PB126I2 : PrimesBelowBoundCertificateInterval O 79 125 126 where
  m := 8
  g := ![1, 1, 2, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB126I2_primes
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
  β := ![I97N1, I107N1, I109N1, I113N1]
  Il := ![[], [], [I97N1], [], [], [I107N1], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
