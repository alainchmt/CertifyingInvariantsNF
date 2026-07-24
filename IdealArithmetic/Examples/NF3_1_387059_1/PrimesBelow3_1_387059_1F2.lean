
import IdealArithmetic.Examples.NF3_1_387059_1.RI3_1_387059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![11, -28, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![11, -28, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![11, 55, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![11, -28, 1], ![-48, 9, -110], ![-233, 827, -74]]]
  hmulB := by decide  
  f := ![![![-10, 28, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -55, 83]], ![![0, -1, 1], ![14, 73, -110], ![7, 59, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [6, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 82], [0, 1]]
 g := ![![[39, 7], [60, 31], [61], [63], [41, 59], [1]], ![[61, 76], [27, 52], [61], [63], [13, 24], [1]]]
 h' := ![![[15, 82], [55, 16], [7, 60], [46, 71], [3, 48], [77, 15], [0, 1]], ![[0, 1], [46, 67], [77, 23], [32, 12], [59, 35], [53, 68], [15, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [36, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [6, 68, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-607, -47, -1436]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![183, 951, -1436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![27, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![27, 1, 0]] 
 ![![83, 0, 0], ![27, 1, 0], ![74, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![27, 1, 0], ![2, 26, 4], ![8, -30, 29]]]
  hmulB := by decide  
  f := ![![![-1383, -20792, -3200], ![-664, 66400, 0]], ![![-466, -6758, -1040], ![-165, 21580, 0]], ![![-1248, -18538, -2853], ![-546, 59200, 0]]]
  g := ![![![1, 0, 0], ![-27, 83, 0], ![-74, 0, 83]], ![![0, 1, 0], ![-12, 26, 4], ![-16, -30, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![11, -28, 1]] ![![83, 0, 0], ![27, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2241, 83, 0]], ![![913, -2324, 83], ![249, -747, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![27, 1, 0]]], ![![![11, -28, 1]], ![![3, -9, -1]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [50, 81, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 57, 72], [39, 31, 17], [0, 1]]
 g := ![![[73, 12, 87], [28, 85], [44, 81], [47, 59, 22], [28, 38, 1], []], ![[35, 9, 76, 21], [42, 36], [26, 44], [76, 49, 51, 4], [3, 21, 33, 39], [55, 22]], ![[10, 8, 80, 84], [47, 17], [7, 32], [70, 70, 40, 68], [38, 77, 33, 53], [21, 22]]]
 h' := ![![[88, 57, 72], [42, 10, 40], [75, 72, 68], [53, 49, 9], [24, 15, 72], [0, 0, 1], [0, 1]], ![[39, 31, 17], [76, 48, 2], [60, 66, 83], [5, 10, 69], [17, 40, 19], [10, 27, 31], [88, 57, 72]], ![[0, 1], [48, 31, 47], [23, 40, 27], [62, 30, 11], [78, 34, 87], [26, 62, 57], [39, 31, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 18], []]
 b := ![[], [51, 88, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [50, 81, 51, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![113742, -87754, 217694]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1278, -986, 2446]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![68, -17, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![68, -17, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![68, 80, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![68, -17, 1], ![-26, 55, -66], ![-145, 497, 5]]]
  hmulB := by decide  
  f := ![![![-67, 17, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -80, 97]], ![![0, -1, 1], ![46, 55, -66], ![-5, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 96], [0, 1]]
 g := ![![[51, 73], [8], [65], [49], [1], [87, 1]], ![[0, 24], [8], [65], [49], [1], [77, 96]]]
 h' := ![![[87, 96], [92, 48], [67, 69], [91, 29], [44, 7], [40, 96], [0, 1]], ![[0, 1], [0, 49], [56, 28], [92, 68], [71, 90], [50, 1], [87, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [53, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [4, 10, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36679, -52789, -118664]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![82809, 97323, -118664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-31, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-31, 1, 0]] 
 ![![97, 0, 0], ![66, 1, 0], ![92, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-31, 1, 0], ![2, -32, 4], ![8, -30, -29]]]
  hmulB := by decide  
  f := ![![![-3579, 67180, -8400], ![1940, 203700, 0]], ![![-2452, 45683, -5712], ![1262, 138516, 0]], ![![-3422, 63718, -7967], ![1754, 193200, 0]]]
  g := ![![![1, 0, 0], ![-66, 97, 0], ![-92, 0, 97]], ![![-1, 1, 0], ![18, -32, 4], ![48, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![68, -17, 1]] ![![97, 0, 0], ![-31, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3007, 97, 0]], ![![6596, -1649, 97], ![-2134, 582, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-31, 1, 0]]], ![![![68, -17, 1]], ![![-22, 6, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-24, -15, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-24, -15, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![77, 86, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-24, -15, 1], ![-22, -39, -58], ![-129, 437, -83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -86, 101]], ![![-1, -1, 1], ![44, 49, -58], ![62, 75, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [72, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 100], [0, 1]]
 g := ![![[75, 96], [49], [88, 84], [9], [54], [54, 1]], ![[7, 5], [49], [79, 17], [9], [54], [7, 100]]]
 h' := ![![[54, 100], [29, 46], [27, 94], [28, 36], [26, 3], [51, 16], [0, 1]], ![[0, 1], [89, 55], [53, 7], [53, 65], [87, 98], [6, 85], [54, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [27, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [72, 47, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1243, 675, -2772]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2101, 2367, -2772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-43, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-43, 1, 0]] 
 ![![101, 0, 0], ![58, 1, 0], ![83, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-43, 1, 0], ![2, -44, 4], ![8, -30, -41]]]
  hmulB := by decide  
  f := ![![![8242, -235167, 21384], ![-5757, -539946, 0]], ![![4720, -135003, 12276], ![-3332, -309969, 0]], ![![6771, -193256, 17573], ![-4736, -443718, 0]]]
  g := ![![![1, 0, 0], ![-58, 101, 0], ![-83, 0, 101]], ![![-1, 1, 0], ![22, -44, 4], ![51, -30, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-24, -15, 1]] ![![101, 0, 0], ![-43, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4343, 101, 0]], ![![-2424, -1515, 101], ![1010, 606, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-43, 1, 0]]], ![![![-24, -15, 1]], ![![10, 6, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![3, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![3, 1, 0]] 
 ![![103, 0, 0], ![3, 1, 0], ![102, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![3, 1, 0], ![2, 2, 4], ![8, -30, 5]]]
  hmulB := by decide  
  f := ![![![10750, 10759, 21528], ![515, -554346, 0]], ![![309, 311, 624], ![104, -16068, 0]], ![![10647, 10655, 21319], ![463, -548964, 0]]]
  g := ![![![1, 0, 0], ![-3, 103, 0], ![-102, 0, 103]], ![![0, 1, 0], ![-4, 2, 4], ![-4, -30, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -1]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1, 2, -1]] 
 ![![103, 0, 0], ![42, 1, 0], ![85, 0, 1]] where
  M :=![![![-1, 2, -1], ![-4, 27, 6], ![25, -47, 32]]]
  hmulB := by decide  
  f := ![![![-1146, 17, -39]], ![![-470, 7, -16]], ![![-941, 14, -32]]]
  g := ![![![0, 2, -1], ![-16, 27, 6], ![-7, -47, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-46, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-46, 1, 0]] 
 ![![103, 0, 0], ![57, 1, 0], ![78, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-46, 1, 0], ![2, -47, 4], ![8, -30, -44]]]
  hmulB := by decide  
  f := ![![![5919, -185513, 15792], ![-4429, -406644, 0]], ![![3311, -102625, 8736], ![-2368, -224952, 0]], ![![4502, -140486, 11959], ![-3310, -307944, 0]]]
  g := ![![![1, 0, 0], ![-57, 103, 0], ![-78, 0, 103]], ![![-1, 1, 0], ![23, -47, 4], ![50, -30, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![3, 1, 0]] ![![-1, 2, -1]]
  ![![103, 0, 0], ![32, 11, 1]] where
 M := ![![![-103, 206, -103]], ![![-7, 33, 3]]]
 hmul := by decide  
 g := ![![![![-1, 2, -1], ![0, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![32, 11, 1]] ![![103, 0, 0], ![-46, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4738, 103, 0]], ![![3296, 1133, 103], ![-1442, -515, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-46, 1, 0]]], ![![![32, 11, 1]], ![![-14, -5, 0]]]]
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
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![23, 40, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![23, 40, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![23, 40, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![23, 40, 1], ![88, -47, 162], ![311, -1213, 74]]]
  hmulB := by decide  
  f := ![![![-22, -40, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -40, 107]], ![![0, 0, 1], ![-34, -61, 162], ![-13, -39, 74]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [104, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 106], [0, 1]]
 g := ![![[32, 30], [55, 41], [1], [95, 13], [75], [96, 1]], ![[23, 77], [32, 66], [1], [59, 94], [75], [85, 106]]]
 h' := ![![[96, 106], [58, 64], [15, 24], [71, 1], [30, 86], [74, 17], [0, 1]], ![[0, 1], [103, 43], [72, 83], [60, 106], [47, 21], [101, 90], [96, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [86, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [104, 11, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-338, -104, -1094]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![232, 408, -1094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![52, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![52, 1, 0]] 
 ![![107, 0, 0], ![52, 1, 0], ![33, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![52, 1, 0], ![2, 51, 4], ![8, -30, 54]]]
  hmulB := by decide  
  f := ![![![-3143, -110647, -8680], ![-2461, 232190, 0]], ![![-1536, -53743, -4216], ![-1176, 112778, 0]], ![![-981, -34125, -2677], ![-735, 71610, 0]]]
  g := ![![![1, 0, 0], ![-52, 107, 0], ![-33, 0, 107]], ![![0, 1, 0], ![-26, 51, 4], ![-2, -30, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![23, 40, 1]] ![![107, 0, 0], ![52, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5564, 107, 0]], ![![2461, 4280, 107], ![1284, 2033, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![52, 1, 0]]], ![![![23, 40, 1]], ![![12, 19, 2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-47, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-47, 1, 0]] 
 ![![109, 0, 0], ![62, 1, 0], ![36, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-47, 1, 0], ![2, -48, 4], ![8, -30, -45]]]
  hmulB := by decide  
  f := ![![![7906, -247197, 20604], ![-5559, -561459, 0]], ![![4496, -140563, 11716], ![-3160, -319261, 0]], ![![2609, -81643, 6805], ![-1841, -185436, 0]]]
  g := ![![![1, 0, 0], ![-62, 109, 0], ![-36, 0, 109]], ![![-1, 1, 0], ![26, -48, 4], ![32, -30, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-16, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-16, 1, 0]] 
 ![![109, 0, 0], ![93, 1, 0], ![96, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-16, 1, 0], ![2, -17, 4], ![8, -30, -14]]]
  hmulB := by decide  
  f := ![![![-3867, 34093, -8024], ![981, 218654, 0]], ![![-3309, 29080, -6844], ![764, 186499, 0]], ![![-3408, 30027, -7067], ![849, 192576, 0]]]
  g := ![![![1, 0, 0], ![-93, 109, 0], ![-96, 0, 109]], ![![-1, 1, 0], ![11, -17, 4], ![38, -30, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-47, 1, 0]] ![![109, 0, 0], ![-47, 1, 0]]
  ![![109, 0, 0], ![35, -51, 1]] where
 M := ![![![11881, 0, 0], ![-5123, 109, 0]], ![![-5123, 109, 0], ![2211, -95, 4]]]
 hmul := by decide  
 g := ![![![![74, 51, -1], ![109, 0, 0]], ![![-47, 1, 0], ![0, 0, 0]]], ![![![-47, 1, 0], ![0, 0, 0]], ![![-16, 52, -1], ![113, 0, 0]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![35, -51, 1]] ![![109, 0, 0], ![-16, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1744, 109, 0]], ![![3815, -5559, 109], ![-654, 872, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-16, 1, 0]]], ![![![35, -51, 1]], ![![-6, 8, -2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-34, 6, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-34, 6, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![79, 6, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-34, 6, 1], ![20, -70, 26], ![39, -193, -51]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -6, 113]], ![![-1, 0, 1], ![-18, -2, 26], ![36, 1, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [65, 49, 1] where
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
 g := ![![[39, 77], [7], [2], [85], [69, 13], [64, 1]], ![[108, 36], [7], [2], [85], [110, 100], [15, 112]]]
 h' := ![![[64, 112], [19, 23], [19, 81], [107, 51], [35, 57], [21, 76], [0, 1]], ![[0, 1], [22, 90], [5, 32], [94, 62], [67, 56], [26, 37], [64, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [27, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [65, 49, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15700, -21551, -49790]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34670, 2453, -49790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-26, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-26, 1, 0]] 
 ![![113, 0, 0], ![87, 1, 0], ![51, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-26, 1, 0], ![2, -27, 4], ![8, -30, -24]]]
  hmulB := by decide  
  f := ![![![-753, 11229, -1664], ![339, 47008, 0]], ![![-587, 8638, -1280], ![227, 36160, 0]], ![![-341, 5068, -751], ![148, 21216, 0]]]
  g := ![![![1, 0, 0], ![-87, 113, 0], ![-51, 0, 113]], ![![-1, 1, 0], ![19, -27, 4], ![34, -30, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-34, 6, 1]] ![![113, 0, 0], ![-26, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2938, 113, 0]], ![![-3842, 678, 113], ![904, -226, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-26, 1, 0]]], ![![![-34, 6, 1]], ![![8, -2, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![58, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![58, 1, 0]] 
 ![![127, 0, 0], ![58, 1, 0], ![63, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![58, 1, 0], ![2, 57, 4], ![8, -30, 60]]]
  hmulB := by decide  
  f := ![![![-6695, -256916, -18032], ![-5080, 572516, 0]], ![![-3072, -117288, -8232], ![-2285, 261366, 0]], ![![-3349, -127447, -8945], ![-2459, 284004, 0]]]
  g := ![![![1, 0, 0], ![-58, 127, 0], ![-63, 0, 127]], ![![0, 1, 0], ![-28, 57, 4], ![-16, -30, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-49, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-49, 1, 0]] 
 ![![127, 0, 0], ![78, 1, 0], ![23, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-49, 1, 0], ![2, -50, 4], ![8, -30, -47]]]
  hmulB := by decide  
  f := ![![![2247, -68390, 5472], ![-1270, -173736, 0]], ![![1387, -41994, 3360], ![-761, -106680, 0]], ![![427, -12386, 991], ![-178, -31464, 0]]]
  g := ![![![1, 0, 0], ![-78, 127, 0], ![-23, 0, 127]], ![![-1, 1, 0], ![30, -50, 4], ![27, -30, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-10, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-10, 1, 0]] 
 ![![127, 0, 0], ![117, 1, 0], ![100, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-10, 1, 0], ![2, -11, 4], ![8, -30, -8]]]
  hmulB := by decide  
  f := ![![![-5487, 30508, -11096], ![762, 352298, 0]], ![![-5059, 28100, -10220], ![636, 324485, 0]], ![![-4320, 24022, -8737], ![606, 277400, 0]]]
  g := ![![![1, 0, 0], ![-117, 127, 0], ![-100, 0, 127]], ![![-1, 1, 0], ![7, -11, 4], ![34, -30, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![58, 1, 0]] ![![127, 0, 0], ![-49, 1, 0]]
  ![![127, 0, 0], ![52, 2, 1]] where
 M := ![![![16129, 0, 0], ![-6223, 127, 0]], ![![7366, 127, 0], ![-2840, 8, 4]]]
 hmul := by decide  
 g := ![![![![75, -2, -1], ![127, 0, 0]], ![![-49, 1, 0], ![0, 0, 0]]], ![![![6, -1, -1], ![127, 0, 0]], ![![-24, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![52, 2, 1]] ![![127, 0, 0], ![-10, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1270, 127, 0]], ![![6604, 254, 127], ![-508, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-10, 1, 0]]], ![![![52, 2, 1]], ![![-4, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [66, 38, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 110, 101], [19, 20, 30], [0, 1]]
 g := ![![[23, 108, 123], [22, 85, 16], [127, 107], [60, 121], [15, 112], [73, 1], []], ![[109, 79, 30, 7], [61, 103, 104, 105], [50, 107], [35, 52], [7, 91], [68, 7], [19, 114]], ![[35, 20, 63, 83], [77, 8, 73, 116], [], [39, 46], [113, 89], [111, 48], [90, 114]]]
 h' := ![![[54, 110, 101], [120, 64, 75], [109, 119, 127], [32, 30, 99], [113, 107, 120], [29, 42, 51], [0, 0, 1], [0, 1]], ![[19, 20, 30], [108, 36, 104], [18, 126, 18], [82, 65, 32], [54, 92, 107], [75, 4, 22], [90, 97, 20], [54, 110, 101]], ![[0, 1], [15, 31, 83], [58, 17, 117], [53, 36], [111, 63, 35], [44, 85, 58], [54, 34, 110], [19, 20, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121, 128], []]
 b := ![[], [102, 28, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [66, 38, 58, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-131, -1048, -1048]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -8, -8]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [47, 112, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 110, 55], [91, 26, 82], [0, 1]]
 g := ![![[90, 6, 126], [136, 128], [11, 36], [119, 70, 126], [42, 18], [108, 1], []], ![[80, 120, 13, 58], [117, 72], [74, 112], [114, 59, 20, 131], [117, 76], [102, 128], [136, 11]], ![[22, 64, 128, 104], [100, 118], [11, 39], [29, 43, 0, 12], [39, 129], [29, 44], [109, 11]]]
 h' := ![![[17, 110, 55], [103, 23, 20], [59, 63, 111], [24, 8, 6], [130, 52, 20], [130, 50, 44], [0, 0, 1], [0, 1]], ![[91, 26, 82], [90, 45, 4], [66, 91, 49], [121, 66, 48], [62, 84, 92], [9, 33, 58], [62, 47, 26], [17, 110, 55]], ![[0, 1], [7, 69, 113], [130, 120, 114], [109, 63, 83], [70, 1, 25], [56, 54, 35], [7, 90, 110], [91, 26, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 53], []]
 b := ![[], [36, 79, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [47, 112, 29, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254409, 235366, 732402]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1857, 1718, 5346]
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



lemma PB177I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB177I2 : PrimesBelowBoundCertificateInterval O 79 137 177 where
  m := 11
  g := ![2, 1, 2, 2, 3, 2, 3, 2, 3, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB177I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
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
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N1, I109N0, I109N1, I113N1, I127N0, I127N1, I127N2]
  Il := ![[I83N1], [], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N0, I109N0, I109N1], [I113N1], [I127N0, I127N1, I127N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
