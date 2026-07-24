
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [77, 55, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 38, 33], [8, 44, 50], [0, 1]]
 g := ![![[13, 76, 48], [19, 42, 49], [3, 77], [16, 63], [37, 3, 1], []], ![[66, 40, 68, 4], [2, 40, 18, 44], [28, 38], [73, 28], [68, 56, 19, 61], [48, 10]], ![[66, 46, 31, 53], [2, 36, 13, 19], [56, 31], [57, 9], [22, 33, 17, 73], [31, 10]]]
 h' := ![![[78, 38, 33], [31, 60, 52], [43, 34, 7], [78, 18, 49], [56, 58, 35], [0, 0, 1], [0, 1]], ![[8, 44, 50], [71, 1, 35], [72, 77, 19], [53, 64, 11], [14, 30, 51], [64, 28, 44], [78, 38, 33]], ![[0, 1], [65, 22, 79], [73, 55, 57], [22, 1, 23], [57, 78, 80], [1, 55, 38], [8, 44, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 63], []]
 b := ![[], [50, 3, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [77, 55, 80, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4464736, 941967, -189738]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53792, 11349, -2286]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38952134615647870782, -7833471691297173893, 2802628234964853280]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![38952134615647870782, -7833471691297173893, 2802628234964853280]] 
 ![![89, 0, 0], ![0, 89, 0], ![58, 81, 1]] where
  M :=![![![38952134615647870782, -7833471691297173893, 2802628234964853280], ![-536381382072459671919, 107869014462574430888, -38592945442888483518], ![1032749481907408803379, -207691155068908222847, 74306912476018267983]]]
  hmulB := by decide  
  f := ![![![-12365549178, 648612131, 803261606]], ![![-145051037505, 1599197074, 6301457604]], ![![-142695486740, 1827074195, 6330966517]]]
  g := ![![![-1388767449576557522, -2638723131724160557, 2802628234964853280], ![19123701726012049125, 36335928037489231414, -38592945442888483518], ![-36820802715748884715, -69961247928386381230, 74306912476018267983]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [14, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 88], [0, 1]]
 g := ![![[36, 8], [47], [57], [76, 68], [83, 10], [1]], ![[9, 81], [47], [57], [69, 21], [27, 79], [1]]]
 h' := ![![[30, 88], [59, 39], [19, 74], [4, 18], [84, 54], [75, 30], [0, 1]], ![[0, 1], [72, 50], [14, 15], [10, 71], [13, 35], [85, 59], [30, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [69, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [14, 59, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![906, -2040, 1412]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-910, -1308, 1412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12365549178, -648612131, -803261606]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![12365549178, -648612131, -803261606]] 
 ![![89, 0, 0], ![45, 1, 0], ![34, 0, 1]] where
  M :=![![![12365549178, -648612131, -803261606], ![145051037505, -1599197074, -6301457604], ![233562429631, 4544863237, -6448780941]]]
  hmulB := by decide  
  f := ![![![-38952134615647870782, 7833471691297173893, -2802628234964853280]], ![![-13668142422828028239, 2748732715121330273, -983430619444156338]], ![![-26484517515049847303, 5326170703067552081, -1905576095110373927]]]
  g := ![![![773752693, -648612131, -803261606], ![4845668139, -1599197074, -6301457604], ![2789911640, 4544863237, -6448780941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![38952134615647870782, -7833471691297173893, 2802628234964853280]] ![![12365549178, -648612131, -803261606]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [85, 30, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 55, 83], [24, 41, 14], [0, 1]]
 g := ![![[52, 54, 12], [62, 93], [96, 6], [45, 12], [5, 88], [1]], ![[78, 89, 61, 34], [13, 11], [66, 54], [93, 65], [80, 96], [27, 58, 34, 69]], ![[53, 50, 30, 60], [45, 62], [84, 96], [9, 73], [68, 81], [10, 45, 57, 28]]]
 h' := ![![[42, 55, 83], [71, 64, 20], [54, 47, 53], [58, 89, 43], [10, 89, 77], [12, 67, 66], [0, 1]], ![[24, 41, 14], [43, 9, 21], [88, 66, 60], [13, 9, 32], [62, 64, 68], [13, 43, 22], [42, 55, 83]], ![[0, 1], [33, 24, 56], [47, 81, 81], [3, 96, 22], [34, 41, 49], [73, 84, 9], [24, 41, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 34], []]
 b := ![[], [38, 68, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [85, 30, 31, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33625963255, 9214378036, -2750582246]
  a := ![-129, 65, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-346659415, 94993588, -28356518]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-8, 15, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-8, 15, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![93, 15, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-8, 15, 1], ![-138, -19, 93], ![-2888, 264, 58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -15, 101]], ![![-1, 0, 1], ![-87, -14, 93], ![-82, -6, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [22, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 100], [0, 1]]
 g := ![![[100, 23], [9], [59, 23], [68], [31], [22, 1]], ![[0, 78], [9], [60, 78], [68], [31], [44, 100]]]
 h' := ![![[22, 100], [27, 86], [15, 3], [25, 86], [62, 88], [21, 58], [0, 1]], ![[0, 1], [0, 15], [81, 98], [99, 15], [79, 13], [85, 43], [22, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [73, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [22, 79, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1499, -3969, 1614]
  a := ![-5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1501, -279, 1614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![8, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![8, 1, 0]] 
 ![![101, 0, 0], ![8, 1, 0], ![43, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![8, 1, 0], ![3, 6, 6], ![-183, 19, 11]]]
  hmulB := by decide  
  f := ![![![8145, 16408, 16416], ![808, -276336, 0]], ![![640, 1295, 1296], ![102, -21816, 0]], ![![3463, 6985, 6989], ![403, -117648, 0]]]
  g := ![![![1, 0, 0], ![-8, 101, 0], ![-43, 0, 101]], ![![0, 1, 0], ![-3, 6, 6], ![-8, 19, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-8, 15, 1]] ![![101, 0, 0], ![8, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![808, 101, 0]], ![![-808, 1515, 101], ![-202, 101, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![8, 1, 0]]], ![![![-8, 15, 1]], ![![-2, 1, 1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [98, 86, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 4, 31], [8, 98, 72], [0, 1]]
 g := ![![[19, 39, 34], [41, 93, 56], [15, 56, 18], [101, 91], [], [1]], ![[95, 70, 64, 67], [4, 16, 49, 85], [80, 10, 95, 85], [62, 93], [87, 41], [35, 50, 99, 24]], ![[46, 48, 2, 59], [34, 98, 41, 17], [16, 23, 46, 46], [67, 36], [83, 41], [70, 40, 5, 79]]]
 h' := ![![[95, 4, 31], [102, 92, 31], [75, 29, 46], [100, 63, 92], [25, 67, 83], [5, 17], [0, 1]], ![[8, 98, 72], [32, 38, 19], [87, 35, 51], [84, 90, 51], [86, 39, 14], [75, 68, 12], [95, 4, 31]], ![[0, 1], [93, 76, 53], [82, 39, 6], [51, 53, 63], [5, 100, 6], [38, 18, 91], [8, 98, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 8], []]
 b := ![[], [38, 23, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [98, 86, 0, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4203430, 1205100, -355968]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40810, 11700, -3456]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [70, 69, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 17, 41], [56, 89, 66], [0, 1]]
 g := ![![[47, 75, 40], [71, 46, 36], [51, 3], [105, 38, 105], [81, 41], [1]], ![[30, 41, 103, 85], [52, 19, 79, 75], [67, 23], [102, 18, 30, 57], [74, 30], [32, 103, 33, 13]], ![[88, 69, 13, 55], [67, 98, 94, 80], [66, 39], [45, 25, 46, 80], [45, 102], [51, 86, 60, 94]]]
 h' := ![![[27, 17, 41], [59, 92, 19], [87, 58, 6], [33, 59, 89], [86, 24, 31], [37, 38, 83], [0, 1]], ![[56, 89, 66], [8, 49, 6], [19, 12, 23], [1, 73, 68], [67, 48, 105], [2, 48, 64], [27, 17, 41]], ![[0, 1], [18, 73, 82], [0, 37, 78], [74, 82, 57], [53, 35, 78], [97, 21, 67], [56, 89, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 41], []]
 b := ![[], [87, 30, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [70, 69, 24, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2276463413, -713898757, 212072074]
  a := ![43, -22, 85]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21275359, -6671951, 1981982]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![22, -7, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![22, -7, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![22, 102, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![22, -7, 1], ![-204, 55, -39], ![1138, -154, 22]]]
  hmulB := by decide  
  f := ![![![-21, 7, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -102, 109]], ![![0, -1, 1], ![6, 37, -39], ![6, -22, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [83, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 108], [0, 1]]
 g := ![![[86, 88], [97], [25, 80], [80, 80], [1], [56, 1]], ![[0, 21], [97], [36, 29], [91, 29], [1], [3, 108]]]
 h' := ![![[56, 108], [31, 52], [105, 73], [9, 25], [21, 25], [39, 1], [0, 1]], ![[0, 1], [0, 57], [51, 36], [101, 84], [4, 84], [95, 108], [56, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [49, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [83, 53, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1150, -189, 354]
  a := ![1, 0, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82, -333, 354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![39, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![39, 1, 0]] 
 ![![109, 0, 0], ![39, 1, 0], ![87, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![39, 1, 0], ![3, 37, 6], ![-183, 19, 42]]]
  hmulB := by decide  
  f := ![![![-806, -11393, -1848], ![-327, 33572, 0]], ![![-291, -4069, -660], ![-108, 11990, 0]], ![![-663, -9094, -1475], ![-206, 26796, 0]]]
  g := ![![![1, 0, 0], ![-39, 109, 0], ![-87, 0, 109]], ![![0, 1, 0], ![-18, 37, 6], ![-42, 19, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![22, -7, 1]] ![![109, 0, 0], ![39, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![4251, 109, 0]], ![![2398, -763, 109], ![654, -218, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![39, 1, 0]]], ![![![22, -7, 1]], ![![6, -2, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [86, 49, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 64, 4], [8, 48, 109], [0, 1]]
 g := ![![[112, 82, 99], [10, 102], [37, 95], [110, 83], [94, 88, 22], [1]], ![[73, 1, 86, 91], [4, 69], [110, 30], [86, 81], [100, 108, 28, 15], [43, 77, 48, 64]], ![[71, 85, 93, 36], [36, 14], [95, 2], [31, 77], [8, 34, 58, 77], [79, 70, 17, 49]]]
 h' := ![![[86, 64, 4], [93, 108, 41], [106, 41, 21], [24, 77, 78], [52, 81, 99], [27, 64, 94], [0, 1]], ![[8, 48, 109], [21, 111, 27], [34, 17, 42], [62, 7, 97], [0, 29, 104], [10, 46, 22], [86, 64, 4]], ![[0, 1], [82, 7, 45], [63, 55, 50], [53, 29, 51], [81, 3, 23], [46, 3, 110], [8, 48, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 22], []]
 b := ![[], [100, 38, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [86, 49, 19, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17677607, -5163648, 1577028]
  a := ![8, -5, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![156439, -45696, 13956]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-67, 31, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-67, 31, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![60, 31, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-67, 31, 1], ![-90, -110, 189], ![-5816, 568, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -31, 127]], ![![-1, 0, 1], ![-90, -47, 189], ![-68, -7, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [48, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 126], [0, 1]]
 g := ![![[121, 84], [94, 73], [69, 87], [11, 21], [61, 82], [34, 1]], ![[56, 43], [36, 54], [106, 40], [90, 106], [55, 45], [68, 126]]]
 h' := ![![[34, 126], [60, 46], [117, 94], [107, 50], [120, 23], [19, 92], [0, 1]], ![[0, 1], [100, 81], [11, 33], [29, 77], [13, 104], [99, 35], [34, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [14, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [48, 93, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5432, -7260, 3330]
  a := ![-10, 5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1616, -870, 3330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-62, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-62, 1, 0]] 
 ![![127, 0, 0], ![65, 1, 0], ![80, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-62, 1, 0], ![3, -64, 6], ![-183, 19, -59]]]
  hmulB := by decide  
  f := ![![![2420, -68787, 6450], ![-1651, -136525, 0]], ![![1279, -35194, 3300], ![-761, -69850, 0]], ![![1562, -43331, 4063], ![-963, -86000, 0]]]
  g := ![![![1, 0, 0], ![-65, 127, 0], ![-80, 0, 127]], ![![-1, 1, 0], ![29, -64, 6], ![26, 19, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-67, 31, 1]] ![![127, 0, 0], ![-62, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-7874, 127, 0]], ![![-8509, 3937, 127], ![4064, -2032, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-62, 1, 0]]], ![![![-67, 31, 1]], ![![32, -16, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2412095805353, 122336477452, 154515003072]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-2412095805353, 122336477452, 154515003072]] 
 ![![131, 0, 0], ![5, 1, 0], ![129, 0, 1]] where
  M :=![![![-2412095805353, 122336477452, 154515003072], ![-27909236129820, 279016298111, 1197563873928], ![-44483220813012, -920421992924, 1199728691515]]]
  hmulB := by decide  
  f := ![![![1437007985738664840313637, -288989589082230483482308, 103393541700363309874464]], ![![-96205702058930175235921, 19347454280907452499859, -6922054968629591006856]], ![![1705907240451786179890635, -343066592060135427959888, 122740995981270762374323]]]
  g := ![![![-175238271671, 122336477452, 154515003072], ![-1402977537077, 279016298111, 1197563873928], ![-1485848183617, -920421992924, 1199728691515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![41, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![41, 1, 0]] 
 ![![131, 0, 0], ![41, 1, 0], ![127, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![41, 1, 0], ![3, 39, 6], ![-183, 19, 44]]]
  hmulB := by decide  
  f := ![![![-4321, -63634, -9792], ![-1834, 213792, 0]], ![![-1366, -19886, -3060], ![-523, 66810, 0]], ![![-4190, -61691, -9493], ![-1775, 207264, 0]]]
  g := ![![![1, 0, 0], ![-41, 131, 0], ![-127, 0, 131]], ![![0, 1, 0], ![-18, 39, 6], ![-50, 19, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-47, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-47, 1, 0]] 
 ![![131, 0, 0], ![84, 1, 0], ![97, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-47, 1, 0], ![3, -49, 6], ![-183, 19, -44]]]
  hmulB := by decide  
  f := ![![![11505, -221632, 27144], ![-5764, -592644, 0]], ![![7385, -142072, 17400], ![-3667, -379900, 0]], ![![8510, -164109, 20099], ![-4293, -438828, 0]]]
  g := ![![![1, 0, 0], ![-84, 131, 0], ![-97, 0, 131]], ![![-1, 1, 0], ![27, -49, 6], ![19, 19, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-2412095805353, 122336477452, 154515003072]] ![![131, 0, 0], ![41, 1, 0]]
  ![![131, 0, 0], ![-9, 51, 1]] where
 M := ![![![-315984550501243, 16026078546212, 20241465402432], ![-126805164149293, 5294811873643, 7532678999880]]]
 hmul := by decide  
 g := ![![![![-2399350248083, 50111652922, 153098830042], ![185518666930, 0, 0]], ![![-963066247385, 12583150151, 56955576978], ![71498415762, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-9, 51, 1]] ![![131, 0, 0], ![-47, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-6157, 131, 0]], ![![-1179, 6681, 131], ![393, -2489, 262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-47, 1, 0]]], ![![![-9, 51, 1]], ![![3, -19, 2]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [118, 4, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 47, 94], [37, 89, 43], [0, 1]]
 g := ![![[109, 110, 123], [68, 38], [108, 73], [88, 123, 112], [48, 115], [53, 1], []], ![[76, 45, 109, 96], [97, 14], [36, 98], [35, 28, 50, 45], [96, 44], [56, 112], [110, 68]], ![[135, 36, 78, 117], [76, 74], [49, 76], [60, 79, 116, 54], [7, 74], [7, 17], [24, 68]]]
 h' := ![![[16, 47, 94], [96, 49, 73], [96, 50, 60], [28, 45, 115], [65, 42, 89], [48, 81, 65], [0, 0, 1], [0, 1]], ![[37, 89, 43], [66, 27, 6], [135, 134, 39], [100, 14, 80], [58, 130, 87], [120, 82, 110], [17, 27, 89], [16, 47, 94]], ![[0, 1], [52, 61, 58], [65, 90, 38], [40, 78, 79], [55, 102, 98], [14, 111, 99], [44, 110, 47], [37, 89, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 76], []]
 b := ![[], [93, 71, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [118, 4, 84, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33169618, 10119368, -2441888]
  a := ![-10, 4, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-242114, 73864, -17824]
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



lemma PB228I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB228I2 : PrimesBelowBoundCertificateInterval O 79 137 228 where
  m := 11
  g := ![1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB228I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I101N1, I109N1, I127N1, I131N0, I131N1, I131N2]
  Il := ![[], [I89N1], [], [I101N1], [], [], [I109N1], [], [I127N1], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
