
import IdealArithmetic.Examples.NF3_3_455700_1.RI3_3_455700_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [50, 65, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 7, 7], [78, 75, 76], [0, 1]]
 g := ![![[38, 78, 63], [56, 51, 75], [75, 11], [55, 64], [34, 4, 1], []], ![[31, 55, 8, 27], [45, 14, 16, 68], [73, 25], [11, 23], [28, 47, 81, 33], [45, 49]], ![[73, 35, 70, 8], [67, 57, 78, 5], [60, 77], [61, 63], [32, 7, 11, 72], [59, 49]]]
 h' := ![![[9, 7, 7], [22, 76, 48], [46, 0, 18], [12, 22, 29], [43, 80, 75], [0, 0, 1], [0, 1]], ![[78, 75, 76], [12, 70, 65], [14, 55, 22], [57, 72, 5], [21, 56, 43], [72, 63, 75], [9, 7, 7]], ![[0, 1], [10, 20, 53], [18, 28, 43], [69, 72, 49], [52, 30, 48], [63, 20, 7], [78, 75, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 29], []]
 b := ![[], [37, 54, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [50, 65, 79, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141017, 96695, -34860]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1699, 1165, -420]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [24, 34, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 19, 40], [8, 69, 49], [0, 1]]
 g := ![![[28, 86, 47], [57, 42], [86, 11], [7, 43, 10], [45, 48, 1], []], ![[8, 14, 42, 22], [43, 85], [8, 78], [73, 17, 5, 81], [84, 63, 75, 69], [0, 87]], ![[30, 70, 62, 72], [28, 9], [76, 36], [41, 66, 7, 49], [40, 11, 30, 67], [80, 87]]]
 h' := ![![[40, 19, 40], [3, 13, 74], [83, 13, 65], [10, 31, 79], [77, 77, 59], [0, 0, 1], [0, 1]], ![[8, 69, 49], [19, 45, 19], [28, 84, 21], [24, 39, 16], [13, 80, 31], [87, 55, 69], [40, 19, 40]], ![[0, 1], [1, 31, 85], [53, 81, 3], [39, 19, 83], [36, 21, 88], [13, 34, 19], [8, 69, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 68], []]
 b := ![[], [76, 61, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [24, 34, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8671982, -3524222, 1135996]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![97438, -39598, 12764]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [52, 43, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 16, 33], [33, 80, 64], [0, 1]]
 g := ![![[47, 13, 96], [55, 11], [90, 73], [4, 18], [85, 2], [1]], ![[55, 63, 23, 2], [17, 35], [5, 22], [67, 12], [36, 64], [23, 87, 65, 47]], ![[90, 75, 90, 61], [43, 91], [49, 31], [33, 61], [51, 36], [65, 41, 63, 50]]]
 h' := ![![[78, 16, 33], [26, 91, 22], [48, 76, 37], [13, 59, 48], [30, 34, 42], [45, 54, 14], [0, 1]], ![[33, 80, 64], [54, 13, 10], [29, 81, 36], [80, 9, 64], [84, 29, 20], [93, 78, 89], [78, 16, 33]], ![[0, 1], [6, 90, 65], [60, 37, 24], [38, 29, 82], [28, 34, 35], [62, 62, 91], [33, 80, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 5], []]
 b := ![[], [47, 95, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [52, 43, 83, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29962422053, 16299637791, -6370176240]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-308890949, 168037503, -65671920]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-24, -37, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-24, -37, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![77, 64, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-24, -37, 1], ![-289, 30, -110], ![9258, -2064, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -64, 101]], ![![-1, -1, 1], ![81, 70, -110], ![97, -16, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [10, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 100], [0, 1]]
 g := ![![[90, 64], [78], [77, 25], [45], [92], [9, 1]], ![[60, 37], [78], [100, 76], [45], [92], [18, 100]]]
 h' := ![![[9, 100], [58, 8], [38, 52], [35, 96], [9, 67], [11, 71], [0, 1]], ![[0, 1], [29, 93], [1, 49], [91, 5], [6, 34], [44, 30], [9, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [15, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [10, 92, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125, -3902, 2019]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1538, -1318, 2019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![9, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![9, 1, 0]] 
 ![![101, 0, 0], ![9, 1, 0], ![7, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![9, 1, 0], ![1, 9, 3], ![-252, 54, 10]]]
  hmulB := by decide  
  f := ![![![-3860, -35229, -11745], ![-606, 395415, 0]], ![![-348, -3132, -1044], ![1, 35148, 0]], ![![-271, -2442, -814], ![-3, 27405, 0]]]
  g := ![![![1, 0, 0], ![-9, 101, 0], ![-7, 0, 101]], ![![0, 1, 0], ![-1, 9, 3], ![-8, 54, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-24, -37, 1]] ![![101, 0, 0], ![9, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![909, 101, 0]], ![![-2424, -3737, 101], ![-505, -303, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![9, 1, 0]]], ![![![-24, -37, 1]], ![![-5, -3, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [88, 55, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 36, 83], [43, 66, 20], [0, 1]]
 g := ![![[92, 9, 82], [50, 30, 34], [80, 73, 41], [2, 72], [72, 52], [1]], ![[98, 0, 21, 32], [55, 95, 1, 13], [97, 15, 30, 38], [75, 61], [14, 26], [18, 82, 15, 34]], ![[25, 23, 53, 95], [47, 8, 41, 71], [96, 46, 80, 75], [66, 56], [40, 59], [65, 75, 21, 69]]]
 h' := ![![[41, 36, 83], [29, 26, 44], [67, 19, 72], [53, 16, 91], [69, 11, 81], [15, 48, 84], [0, 1]], ![[43, 66, 20], [53, 37, 15], [96, 65, 46], [10, 44, 21], [11, 73, 79], [78, 96, 52], [41, 36, 83]], ![[0, 1], [49, 40, 44], [33, 19, 88], [76, 43, 94], [61, 19, 46], [39, 62, 70], [43, 66, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 94], []]
 b := ![[], [49, 91, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [88, 55, 19, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14729, 112785, -64890]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, 1095, -630]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-80, 46, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-80, 46, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![27, 46, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-80, 46, 1], ![-206, -26, 139], ![-11658, 2418, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -46, 107]], ![![-1, 0, 1], ![-37, -60, 139], ![-114, 14, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [69, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 106], [0, 1]]
 g := ![![[106, 76], [66, 13], [13], [26, 49], [42], [69, 1]], ![[0, 31], [0, 94], [13], [90, 58], [42], [31, 106]]]
 h' := ![![[69, 106], [47, 66], [49, 21], [25, 21], [18, 100], [54, 91], [0, 1]], ![[0, 1], [0, 41], [0, 86], [83, 86], [70, 7], [20, 16], [69, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [28, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [69, 38, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49020, 9408, 2833]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1173, -1130, 2833]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-32, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-32, 1, 0]] 
 ![![107, 0, 0], ![75, 1, 0], ![87, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-32, 1, 0], ![1, -32, 3], ![-252, 54, -31]]]
  hmulB := by decide  
  f := ![![![-629, 25275, -2370], ![535, 84530, 0]], ![![-456, 17693, -1659], ![322, 59171, 0]], ![![-521, 20551, -1927], ![403, 68730, 0]]]
  g := ![![![1, 0, 0], ![-75, 107, 0], ![-87, 0, 107]], ![![-1, 1, 0], ![20, -32, 3], ![-15, 54, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-80, 46, 1]] ![![107, 0, 0], ![-32, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3424, 107, 0]], ![![-8560, 4922, 107], ![2354, -1498, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-32, 1, 0]]], ![![![-80, 46, 1]], ![![22, -14, 1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [72, 91, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 4, 88], [51, 104, 21], [0, 1]]
 g := ![![[90, 72, 26], [57, 108], [7, 13, 34], [87, 84, 102], [80, 4], [1]], ![[79, 12, 49, 27], [8, 102], [7, 47, 44, 89], [76, 90, 34, 71], [49, 15], [63, 100, 68, 4]], ![[34, 65, 38, 82], [34, 71], [61, 64, 23, 82], [84, 84, 21, 108], [30, 102], [64, 31, 26, 105]]]
 h' := ![![[60, 4, 88], [84, 47, 35], [41, 47, 76], [58, 76, 19], [78, 86, 50], [37, 18, 2], [0, 1]], ![[51, 104, 21], [49, 5, 37], [25, 46, 50], [94, 105, 53], [85, 67, 15], [4, 74, 48], [60, 4, 88]], ![[0, 1], [87, 57, 37], [30, 16, 92], [62, 37, 37], [63, 65, 44], [77, 17, 59], [51, 104, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 84], []]
 b := ![[], [31, 102, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [72, 91, 107, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4105703, 1232136, -264652]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37667, 11304, -2428]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-724, 81, 28]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-724, 81, 28]] 
 ![![113, 0, 0], ![0, 113, 0], ![71, 15, 1]] where
  M :=![![![-724, 81, 28], ![-6975, 788, 271], ![-22260, 2526, 869]]]
  hmulB := by decide  
  f := ![![![-2, -3, 1]], ![![-255, 52, -8]], ![![-29, 3, 0]]]
  g := ![![![-24, -3, 28], ![-232, -29, 271], ![-743, -93, 869]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [109, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 112], [0, 1]]
 g := ![![[83, 28], [99], [56], [72], [82, 97], [106, 1]], ![[0, 85], [99], [56], [72], [81, 16], [99, 112]]]
 h' := ![![[106, 112], [109, 64], [39, 72], [70, 13], [102, 33], [85, 53], [0, 1]], ![[0, 1], [0, 49], [100, 41], [92, 100], [97, 80], [53, 60], [106, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [59, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [109, 7, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5272, -1717, 2025]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1319, -284, 2025]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 3, -1]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![2, 3, -1]] 
 ![![113, 0, 0], ![67, 1, 0], ![86, 0, 1]] where
  M :=![![![2, 3, -1], ![255, -52, 8], ![-690, 228, -49]]]
  hmulB := by decide  
  f := ![![![724, -81, -28]], ![![491, -55, -19]], ![![748, -84, -29]]]
  g := ![![![-1, 3, -1], ![27, -52, 8], ![-104, 228, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-724, 81, 28]] ![![2, 3, -1]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-83, 53, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-83, 53, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![44, 53, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-83, 53, 1], ![-199, -29, 160], ![-13422, 2796, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -53, 127]], ![![-1, 0, 1], ![-57, -67, 160], ![-114, 12, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [110, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 126], [0, 1]]
 g := ![![[77, 30], [68, 121], [25, 19], [49, 52], [46, 69], [39, 1]], ![[104, 97], [88, 6], [4, 108], [45, 75], [70, 58], [78, 126]]]
 h' := ![![[39, 126], [13, 41], [44, 116], [71, 20], [20, 68], [28, 14], [0, 1]], ![[0, 1], [88, 86], [123, 11], [89, 107], [5, 59], [66, 113], [39, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [26, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [110, 88, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6905, -6600, 4620]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1655, -1980, 4620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-33, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-33, 1, 0]] 
 ![![127, 0, 0], ![94, 1, 0], ![103, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-33, 1, 0], ![1, -33, 3], ![-252, 54, -32]]]
  hmulB := by decide  
  f := ![![![-4389, 166630, -15150], ![2540, 641350, 0]], ![![-3241, 123306, -11211], ![1906, 474599, 0]], ![![-3564, 135141, -12287], ![2043, 520150, 0]]]
  g := ![![![1, 0, 0], ![-94, 127, 0], ![-103, 0, 127]], ![![-1, 1, 0], ![22, -33, 3], ![-16, 54, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-83, 53, 1]] ![![127, 0, 0], ![-33, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4191, 127, 0]], ![![-10541, 6731, 127], ![2540, -1778, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-33, 1, 0]]], ![![![-83, 53, 1]], ![![20, -14, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-60, 51, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-60, 51, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![71, 51, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-60, 51, 1], ![-201, -6, 154], ![-12918, 2688, 45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -51, 131]], ![![-1, 0, 1], ![-85, -60, 154], ![-123, 3, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [1, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 130], [0, 1]]
 g := ![![[59, 1], [59, 1], [58], [43], [125], [75], [1]], ![[0, 130], [0, 130], [58], [43], [125], [75], [1]]]
 h' := ![![[72, 130], [72, 130], [59, 1], [95, 78], [111, 82], [57, 16], [130, 72], [0, 1]], ![[0, 1], [0, 1], [0, 130], [78, 53], [120, 49], [30, 115], [74, 59], [72, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [1, 59, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44153, -18070, 6170]
  a := ![4, -10, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3007, -2540, 6170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-23, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-23, 1, 0]] 
 ![![131, 0, 0], ![108, 1, 0], ![86, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-23, 1, 0], ![1, -23, 3], ![-252, 54, -22]]]
  hmulB := by decide  
  f := ![![![-7212, 176987, -23088], ![2751, 1008176, 0]], ![![-5952, 145895, -19032], ![2228, 831064, 0]], ![![-4736, 116190, -15157], ![1798, 661856, 0]]]
  g := ![![![1, 0, 0], ![-108, 131, 0], ![-86, 0, 131]], ![![-1, 1, 0], ![17, -23, 3], ![-32, 54, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-60, 51, 1]] ![![131, 0, 0], ![-23, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3013, 131, 0]], ![![-7860, 6681, 131], ![1179, -1179, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-23, 1, 0]]], ![![![-60, 51, 1]], ![![9, -9, 1]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [93, 18, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 6, 90], [27, 130, 47], [0, 1]]
 g := ![![[3, 45, 39], [131, 65], [85, 133], [101, 124, 130], [19, 11], [22, 1], []], ![[21, 83, 121, 5], [], [91, 133], [94, 35, 61, 53], [128, 49], [10, 49], [84, 17]], ![[54, 77, 130, 125], [23, 65], [], [34, 35, 115, 46], [42, 112], [131, 36], [127, 17]]]
 h' := ![![[132, 6, 90], [86, 57, 83], [79, 31, 105], [60, 59, 63], [95, 108, 33], [9, 59, 55], [0, 0, 1], [0, 1]], ![[27, 130, 47], [120, 39, 28], [42, 113], [55, 91, 74], [7, 34, 36], [102, 107, 130], [22, 135, 130], [132, 6, 90]], ![[0, 1], [130, 41, 26], [25, 130, 32], [132, 124], [81, 132, 68], [98, 108, 89], [15, 2, 6], [27, 130, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 91], []]
 b := ![[], [22, 135, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [93, 18, 115, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![346804540, -190262723, 75508783]
  a := ![14, -1, 29]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2531420, -1388779, 551159]
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



lemma PB151I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB151I2 : PrimesBelowBoundCertificateInterval O 79 137 151 where
  m := 11
  g := ![1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB151I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
      exact NI113N1
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
  β := ![I101N1, I107N1, I113N1, I127N1, I131N1]
  Il := ![[], [], [], [I101N1], [], [I107N1], [], [I113N1], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
