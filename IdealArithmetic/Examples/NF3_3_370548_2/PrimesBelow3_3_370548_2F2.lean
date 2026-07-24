
import IdealArithmetic.Examples.NF3_3_370548_2.RI3_3_370548_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [20, 51, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 79, 76], [46, 3, 7], [0, 1]]
 g := ![![[32, 5, 3], [1, 59, 63], [43, 29], [63, 69], [35, 70, 1], []], ![[29, 48, 34, 50], [60, 69, 13, 34], [8, 7], [24, 77], [33, 73, 41, 20], [0, 49]], ![[9, 28, 74, 16], [22, 66, 31, 37], [73, 9], [37, 65], [73, 21, 24, 29], [69, 49]]]
 h' := ![![[24, 79, 76], [63, 40, 13], [21, 41, 35], [36, 46, 19], [47, 52, 22], [0, 0, 1], [0, 1]], ![[46, 3, 7], [45, 42, 8], [0, 67, 67], [49, 41, 67], [23, 70, 34], [78, 73, 3], [24, 79, 76]], ![[0, 1], [17, 1, 62], [28, 58, 64], [34, 79, 80], [39, 44, 27], [72, 10, 79], [46, 3, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 33], []]
 b := ![[], [2, 68, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [20, 51, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26062, -11952, -2407]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-314, -144, -29]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-505, -26, 10]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-505, -26, 10]] 
 ![![89, 0, 0], ![0, 89, 0], ![83, 33, 1]] where
  M :=![![![-505, -26, 10], ![1380, -25, -52], ![-3588, -558, -25]]]
  hmulB := by decide  
  f := ![![![319, 70, -18]], ![![-2484, -545, 140]], ![![-515, -113, 29]]]
  g := ![![![-15, -4, 10], ![64, 19, -52], ![-17, 3, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [10, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 88], [0, 1]]
 g := ![![[42, 9], [5], [4], [23, 67], [84, 2], [1]], ![[0, 80], [5], [4], [7, 22], [45, 87], [1]]]
 h' := ![![[25, 88], [75, 86], [83, 70], [37, 2], [50, 44], [79, 25], [0, 1]], ![[0, 1], [0, 3], [53, 19], [87, 87], [82, 45], [81, 64], [25, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [86, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [10, 64, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1709, -79, 626]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-603, -233, 626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![319, 70, -18]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![319, 70, -18]] 
 ![![89, 0, 0], ![23, 1, 0], ![47, 0, 1]] where
  M :=![![![319, 70, -18], ![-2484, -545, 140], ![9660, 2118, -545]]]
  hmulB := by decide  
  f := ![![![-505, -26, 10]], ![![-115, -7, 2]], ![![-307, -20, 5]]]
  g := ![![![-5, 70, -18], ![39, -545, 140], ![-151, 2118, -545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-505, -26, 10]] ![![319, 70, -18]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [85, 38, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 50, 3], [82, 46, 94], [0, 1]]
 g := ![![[50, 67, 16], [24, 32], [32, 44], [74, 24], [90, 9], [1]], ![[87, 76, 5, 93], [49, 86], [52, 2], [46, 2], [25, 91], [35, 63, 73, 27]], ![[15, 2, 1, 25], [64, 33], [66, 11], [64, 9], [50, 50], [27, 95, 94, 70]]]
 h' := ![![[18, 50, 3], [46, 63, 4], [90, 34, 56], [26, 40, 23], [60, 44, 86], [12, 59, 3], [0, 1]], ![[82, 46, 94], [33, 72, 82], [67, 27, 59], [92, 64, 14], [5, 43, 14], [44, 11, 24], [18, 50, 3]], ![[0, 1], [77, 59, 11], [52, 36, 79], [91, 90, 60], [14, 10, 94], [53, 27, 70], [82, 46, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 5], []]
 b := ![[], [80, 65, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [85, 38, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158207, 2910, -7372]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1631, 30, -76]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![343, 13, -8]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![343, 13, -8]] 
 ![![101, 0, 0], ![49, 1, 0], ![62, 0, 1]] where
  M :=![![![343, 13, -8], ![-1104, -41, 26], ![1794, 72, -41]]]
  hmulB := by decide  
  f := ![![![191, 43, -10]], ![![79, 18, -4]], ![![176, 40, -9]]]
  g := ![![![2, 13, -8], ![-7, -41, 26], ![8, 72, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 5, -3]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![127, 5, -3]] 
 ![![101, 0, 0], ![73, 1, 0], ![12, 0, 1]] where
  M :=![![![127, 5, -3], ![-414, -17, 10], ![690, 33, -17]]]
  hmulB := by decide  
  f := ![![![41, 14, 1]], ![![31, 11, 1]], ![![24, 9, 1]]]
  g := ![![![-2, 5, -3], ![7, -17, 10], ![-15, 33, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 21, -13]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![557, 21, -13]] 
 ![![101, 0, 0], ![80, 1, 0], ![32, 0, 1]] where
  M :=![![![557, 21, -13], ![-1794, -67, 42], ![2898, 111, -67]]]
  hmulB := by decide  
  f := ![![![-173, -36, 11]], ![![-122, -25, 8]], ![![-104, -21, 7]]]
  g := ![![![-7, 21, -13], ![22, -67, 42], ![-38, 111, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![343, 13, -8]] ![![127, 5, -3]]
  ![![32659, 1230, -763]] where
 M := ![![![32659, 1230, -763]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![32659, 1230, -763]] ![![557, 21, -13]]
  ![![101, 0, 0]] where
 M := ![![![13773269, 518736, -321786]]]
 hmul := by decide  
 g := ![![![![136369, 5136, -3186]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-47, -19, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-47, -19, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![56, 84, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-47, -19, 1], ![138, 1, -38], ![-2622, -843, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -84, 103]], ![![-1, -1, 1], ![22, 31, -38], ![-26, -9, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [76, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 102], [0, 1]]
 g := ![![[10, 61], [34, 82], [68, 72], [58], [9], [64, 1]], ![[0, 42], [29, 21], [41, 31], [58], [9], [25, 102]]]
 h' := ![![[64, 102], [94, 79], [85, 59], [47, 81], [51, 26], [80, 3], [0, 1]], ![[0, 1], [0, 24], [50, 44], [81, 22], [67, 77], [66, 100], [64, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [40, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [76, 39, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-712, 374, 311]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-176, -250, 311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![38, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![38, 1, 0]] 
 ![![103, 0, 0], ![38, 1, 0], ![102, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![38, 1, 0], ![0, 38, 2], ![138, 48, 38]]]
  hmulB := by decide  
  f := ![![![571, 15, 0], ![-1545, 0, 0]], ![![190, 5, 0], ![-514, 0, 0]], ![![578, -4, -1], ![-1564, 52, 0]]]
  g := ![![![1, 0, 0], ![-38, 103, 0], ![-102, 0, 103]], ![![0, 1, 0], ![-16, 38, 2], ![-54, 48, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-47, -19, 1]] ![![103, 0, 0], ![38, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3914, 103, 0]], ![![-4841, -1957, 103], ![-1648, -721, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![38, 1, 0]]], ![![![-47, -19, 1]], ![![-16, -7, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1367, -52, 32]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-1367, -52, 32]] 
 ![![107, 0, 0], ![0, 107, 0], ![81, 92, 1]] where
  M :=![![![-1367, -52, 32], ![4416, 169, -104], ![-7176, -288, 169]]]
  hmulB := by decide  
  f := ![![![-13, -4, 0]], ![![0, -13, -8]], ![![-15, -16, -7]]]
  g := ![![![-37, -28, 32], ![120, 91, -104], ![-195, -148, 169]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [58, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 106], [0, 1]]
 g := ![![[35, 83], [0, 39], [19], [0, 86], [47], [3, 1]], ![[70, 24], [10, 68], [19], [44, 21], [47], [6, 106]]]
 h' := ![![[3, 106], [0, 46], [75, 57], [0, 74], [51, 73], [40, 58], [0, 1]], ![[0, 1], [31, 61], [32, 50], [8, 33], [56, 34], [0, 49], [3, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [71, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [58, 104, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![334, 61, -54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, 47, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-13, -4, 0]] 
 ![![107, 0, 0], ![30, 1, 0], ![85, 0, 1]] where
  M :=![![![-13, -4, 0], ![0, -13, -8], ![-552, -192, -13]]]
  hmulB := by decide  
  f := ![![![-1367, -52, 32]], ![![-342, -13, 8]], ![![-1153, -44, 27]]]
  g := ![![![1, -4, 0], ![10, -13, -8], ![59, -192, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-1367, -52, 32]] ![![-13, -4, 0]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![9, 44, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![9, 44, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![9, 44, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![9, 44, 1], ![138, 57, 88], ![6072, 2181, 57]]]
  hmulB := by decide  
  f := ![![![-8, -44, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -44, 109]], ![![0, 0, 1], ![-6, -35, 88], ![51, -3, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [36, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 108], [0, 1]]
 g := ![![[12, 106], [84], [9, 31], [95, 88], [73], [4, 1]], ![[0, 3], [84], [24, 78], [11, 21], [73], [8, 108]]]
 h' := ![![[4, 108], [37, 18], [3, 56], [68, 24], [14, 57], [74, 89], [0, 1]], ![[0, 1], [0, 91], [9, 53], [55, 85], [24, 52], [103, 20], [4, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [17, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [36, 105, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5386, 3926, 877]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -318, 877]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![21, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![21, 1, 0]] 
 ![![109, 0, 0], ![21, 1, 0], ![52, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![21, 1, 0], ![0, 21, 2], ![138, 48, 21]]]
  hmulB := by decide  
  f := ![![![463, 22, 0], ![-2398, 0, 0]], ![![63, 3, 0], ![-326, 0, 0]], ![![202, -1, -1], ![-1046, 55, 0]]]
  g := ![![![1, 0, 0], ![-21, 109, 0], ![-52, 0, 109]], ![![0, 1, 0], ![-5, 21, 2], ![-18, 48, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![9, 44, 1]] ![![109, 0, 0], ![21, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![2289, 109, 0]], ![![981, 4796, 109], ![327, 981, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![21, 1, 0]]], ![![![9, 44, 1]], ![![3, 9, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-37, 47, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-37, 47, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![76, 47, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-37, 47, 1], ![138, 11, 94], ![6486, 2325, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -47, 113]], ![![-1, 0, 1], ![-62, -39, 94], ![50, 16, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [16, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 112], [0, 1]]
 g := ![![[16, 106], [104], [32], [87], [101, 61], [83, 1]], ![[0, 7], [104], [32], [87], [79, 52], [53, 112]]]
 h' := ![![[83, 112], [49, 28], [40, 45], [103, 91], [79, 55], [28, 93], [0, 1]], ![[0, 1], [0, 85], [46, 68], [85, 22], [11, 58], [63, 20], [83, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [37, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [16, 30, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-841, -135, 38]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -17, 38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![19, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![19, 1, 0]] 
 ![![113, 0, 0], ![19, 1, 0], ![102, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![19, 1, 0], ![0, 19, 2], ![138, 48, 19]]]
  hmulB := by decide  
  f := ![![![77, 4, 0], ![-452, 0, 0]], ![![-19, -1, 0], ![114, 0, 0]], ![![88, -5, -1], ![-518, 57, 0]]]
  g := ![![![1, 0, 0], ![-19, 113, 0], ![-102, 0, 113]], ![![0, 1, 0], ![-5, 19, 2], ![-24, 48, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-37, 47, 1]] ![![113, 0, 0], ![19, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2147, 113, 0]], ![![-4181, 5311, 113], ![-565, 904, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![19, 1, 0]]], ![![![-37, 47, 1]], ![![-5, 8, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1121, 246, -63]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![1121, 246, -63]] 
 ![![127, 0, 0], ![0, 127, 0], ![83, 111, 1]] where
  M :=![![![1121, 246, -63], ![-8694, -1903, 492], ![33948, 7461, -1903]]]
  hmulB := by decide  
  f := ![![![389, 15, -9]], ![![-1242, -43, 30]], ![![-815, -27, 20]]]
  g := ![![![50, 57, -63], ![-390, -445, 492], ![1511, 1722, -1903]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [14, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 126], [0, 1]]
 g := ![![[39, 47], [83, 82], [43, 81], [27, 74], [80, 73], [89, 1]], ![[31, 80], [15, 45], [13, 46], [9, 53], [100, 54], [51, 126]]]
 h' := ![![[89, 126], [108, 89], [33, 35], [3, 118], [23, 70], [24, 33], [0, 1]], ![[0, 1], [28, 38], [100, 92], [91, 9], [30, 57], [40, 94], [89, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [103, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [14, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![566, 506, 270]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-172, -232, 270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 15, -9]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![389, 15, -9]] 
 ![![127, 0, 0], ![32, 1, 0], ![123, 0, 1]] where
  M :=![![![389, 15, -9], ![-1242, -43, 30], ![2070, 99, -43]]]
  hmulB := by decide  
  f := ![![![1121, 246, -63]], ![![214, 47, -12]], ![![1353, 297, -76]]]
  g := ![![![8, 15, -9], ![-28, -43, 30], ![33, 99, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![1121, 246, -63]] ![![389, 15, -9]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [40, 30, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 112, 30], [69, 18, 101], [0, 1]]
 g := ![![[59, 51, 94], [80, 117, 123], [50, 58], [101, 74], [39, 25], [67, 1], []], ![[111, 34, 110, 111], [43, 54, 43, 42], [37, 55], [17, 55], [25, 55], [22, 62], [79, 114]], ![[41, 117, 8, 129], [46, 69, 34, 27], [7, 43], [31, 4], [56, 108], [59, 99], [8, 114]]]
 h' := ![![[129, 112, 30], [75, 3, 116], [3, 7, 56], [13, 122, 53], [75, 39, 104], [71, 46, 5], [0, 0, 1], [0, 1]], ![[69, 18, 101], [118, 49, 82], [103, 4, 39], [50, 41, 29], [59, 0, 29], [50, 95, 29], [119, 89, 18], [129, 112, 30]], ![[0, 1], [84, 79, 64], [20, 120, 36], [13, 99, 49], [104, 92, 129], [36, 121, 97], [118, 42, 112], [69, 18, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 115], []]
 b := ![[], [37, 75, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [40, 30, 64, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1380740, -354748, 87508]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10540, -2708, 668]
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



lemma PB136I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 135 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 135 (by omega)

def PB136I2 : PrimesBelowBoundCertificateInterval O 79 135 136 where
  m := 10
  g := ![1, 2, 1, 3, 2, 2, 2, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB136I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
  β := ![I89N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1, I113N1, I127N1]
  Il := ![[], [I89N1], [], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], [I113N1], [I127N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
