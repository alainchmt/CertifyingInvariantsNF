
import IdealArithmetic.Examples.NF3_1_278343_2.RI3_1_278343_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-24, -5, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-24, -5, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![59, 78, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-24, -5, 1], ![71, -44, -41], ![-429, 87, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -78, 83]], ![![-1, -1, 1], ![30, 38, -41], ![19, 33, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [66, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 82], [0, 1]]
 g := ![![[75, 27], [6, 11], [25], [27], [49, 70], [1]], ![[55, 56], [4, 72], [25], [27], [74, 13], [1]]]
 h' := ![![[30, 82], [19, 44], [80, 54], [53, 78], [3, 44], [17, 30], [0, 1]], ![[0, 1], [11, 39], [40, 29], [69, 5], [78, 39], [4, 53], [30, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [76, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [66, 53, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![356, 918, -2740]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1952, 2586, -2740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![41, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![41, 1, 0]] 
 ![![83, 0, 0], ![41, 1, 0], ![34, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![41, 1, 0], ![2, 42, 8], ![81, -15, 40]]]
  hmulB := by decide  
  f := ![![![8422, 251661, 47952], ![7221, -497502, 0]], ![![4157, 124277, 23680], ![3570, -245680, 0]], ![![3448, 103090, 19643], ![2962, -203796, 0]]]
  g := ![![![1, 0, 0], ![-41, 83, 0], ![-34, 0, 83]], ![![0, 1, 0], ![-24, 42, 8], ![-8, -15, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-24, -5, 1]] ![![83, 0, 0], ![41, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3403, 83, 0]], ![![-1992, -415, 83], ![-913, -249, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![41, 1, 0]]], ![![![-24, -5, 1]], ![![-11, -3, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [6, 48, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 81, 33], [16, 7, 56], [0, 1]]
 g := ![![[17, 10, 84], [88, 22], [56, 53], [47], [50, 3, 1], []], ![[7, 58, 32, 33], [44, 1], [6, 39], [11, 81, 66, 86], [22, 65, 12, 15], [69, 21]], ![[0, 74, 17, 48], [28, 78], [43, 16], [83, 44, 88, 3], [59, 72, 8, 24], [46, 21]]]
 h' := ![![[76, 81, 33], [45, 76, 23], [67, 53, 17], [74, 79, 63], [56, 74], [0, 0, 1], [0, 1]], ![[16, 7, 56], [8, 40, 88], [19, 24, 88], [77, 44, 22], [73, 31, 39], [22, 63, 7], [76, 81, 33]], ![[0, 1], [0, 62, 67], [41, 12, 73], [78, 55, 4], [83, 73, 50], [69, 26, 81], [16, 7, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 56], []]
 b := ![[], [27, 80, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [6, 48, 86, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![792634, -173016, 29637]
  a := ![2, 0, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8906, -1944, 333]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [20, 66, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 55, 53], [31, 41, 44], [0, 1]]
 g := ![![[51, 46, 70], [80, 16], [30, 11], [68, 35], [14, 70], [1]], ![[50, 5, 5, 4], [7, 64], [74, 27], [6, 47], [74, 81], [50, 22, 70, 79]], ![[76, 20, 14, 16], [69, 16], [38, 27], [1, 91], [37, 8], [80, 80, 39, 18]]]
 h' := ![![[47, 55, 53], [49, 26, 19], [0, 48, 4], [42, 36, 37], [23, 25, 36], [77, 31, 78], [0, 1]], ![[31, 41, 44], [86, 29, 23], [41, 63, 89], [39, 89, 30], [81, 7, 85], [3, 2, 88], [47, 55, 53]], ![[0, 1], [86, 42, 55], [60, 83, 4], [74, 69, 30], [71, 65, 73], [61, 64, 28], [31, 41, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 18], []]
 b := ![[], [83, 80, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [20, 66, 19, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75764371612, 23882678848, -20029850876]
  a := ![-129, -64, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-781075996, 246213184, -206493308]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [5, 85, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 94, 78], [13, 6, 23], [0, 1]]
 g := ![![[88, 58, 82], [59, 65], [10, 5, 1], [42, 64], [25, 24], [1]], ![[89, 52, 99, 78], [84, 88], [88, 98, 28, 52], [1, 97], [85, 1], [57, 2, 72, 54]], ![[54, 29, 45, 4], [74, 36], [56, 25, 21, 80], [79, 43], [90, 71], [30, 10, 58, 47]]]
 h' := ![![[65, 94, 78], [84, 96, 48], [51, 83, 41], [94, 87, 100], [1, 19, 93], [96, 16, 78], [0, 1]], ![[13, 6, 23], [7, 94, 100], [86, 27, 54], [71, 61, 13], [50, 76, 20], [24, 47, 100], [65, 94, 78]], ![[0, 1], [35, 12, 54], [100, 92, 6], [80, 54, 89], [77, 6, 89], [27, 38, 24], [13, 6, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 9], []]
 b := ![[], [67, 99, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [5, 85, 23, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2346230, 702859, -502273]
  a := ![-3, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23230, 6959, -4973]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [50, 12, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 0, 40], [53, 102, 63], [0, 1]]
 g := ![![[27, 89, 33], [99, 56, 93], [83, 16, 79], [37, 17], [53, 13], [1]], ![[9, 76, 102, 85], [49, 32, 78, 78], [78, 87, 58, 90], [36, 41], [23, 49], [101, 76, 9, 37]], ![[31, 64, 57, 58], [91, 51, 66, 19], [27, 23, 57, 1], [51, 33], [15, 92], [82, 10, 32, 66]]]
 h' := ![![[92, 0, 40], [97, 2, 62], [73, 86, 89], [50, 95, 39], [56, 17, 74], [53, 91, 42], [0, 1]], ![[53, 102, 63], [30, 86, 18], [11, 57, 55], [15, 84, 53], [8, 96, 91], [5, 35, 96], [92, 0, 40]], ![[0, 1], [81, 15, 23], [90, 63, 62], [41, 27, 11], [4, 93, 41], [62, 80, 68], [53, 102, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 44], []]
 b := ![[], [45, 88, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [50, 12, 61, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1238472, 480598, -514588]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12024, 4666, -4996]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![32, -48, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![32, -48, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![32, 59, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![32, -48, 1], ![-15, -31, -385], ![-3912, 732, 65]]]
  hmulB := by decide  
  f := ![![![-31, 48, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -59, 107]], ![![0, -1, 1], ![115, 212, -385], ![-56, -29, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [53, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 106], [0, 1]]
 g := ![![[42, 105], [89, 62], [27], [90, 3], [102], [21, 1]], ![[0, 2], [0, 45], [27], [46, 104], [102], [42, 106]]]
 h' := ![![[21, 106], [98, 31], [59, 94], [45, 53], [81, 18], [64, 67], [0, 1]], ![[0, 1], [0, 76], [0, 13], [88, 54], [31, 89], [80, 40], [21, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [87, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [53, 86, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![114280, 45255, -112497]
  a := ![23, 21, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34712, 62454, -112497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-43, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-43, 1, 0]] 
 ![![107, 0, 0], ![64, 1, 0], ![42, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-43, 1, 0], ![2, -42, 8], ![81, -15, -44]]]
  hmulB := by decide  
  f := ![![![1654, -42831, 8160], ![-963, -109140, 0]], ![![1006, -25615, 4880], ![-534, -65270, 0]], ![![642, -16812, 3203], ![-396, -42840, 0]]]
  g := ![![![1, 0, 0], ![-64, 107, 0], ![-42, 0, 107]], ![![-1, 1, 0], ![22, -42, 8], ![27, -15, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![32, -48, 1]] ![![107, 0, 0], ![-43, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4601, 107, 0]], ![![3424, -5136, 107], ![-1391, 2033, -428]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-43, 1, 0]]], ![![![32, -48, 1]], ![![-13, 19, -4]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [19, 56, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 103, 51], [104, 5, 58], [0, 1]]
 g := ![![[64, 63, 27], [93, 36], [76, 67, 22], [45, 68, 83], [100, 48], [1]], ![[87, 3, 70, 101], [57, 94], [35, 101, 74, 42], [62, 7, 87, 10], [88, 93], [104, 22, 96, 107]], ![[2, 8, 59, 57], [10, 63], [70, 87, 38, 23], [47, 65, 105, 40], [76, 63], [102, 26, 58, 2]]]
 h' := ![![[92, 103, 51], [52, 99, 38], [82, 101, 6], [17, 63, 26], [96, 85, 65], [90, 53, 87], [0, 1]], ![[104, 5, 58], [78, 54, 7], [92, 70, 58], [35, 8, 73], [11, 19, 82], [87, 1, 86], [92, 103, 51]], ![[0, 1], [103, 65, 64], [82, 47, 45], [1, 38, 10], [37, 5, 71], [8, 55, 45], [104, 5, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 17], []]
 b := ![[], [9, 97, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [19, 56, 22, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79788, 18421, -3379]
  a := ![-1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-732, 169, -31]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![13, 12, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![13, 12, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![13, 12, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![13, 12, 1], ![105, 10, 95], ![948, -168, -14]]]
  hmulB := by decide  
  f := ![![![-12, -12, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -12, 113]], ![![0, 0, 1], ![-10, -10, 95], ![10, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [54, 30, 1] where
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
 g := ![![[101, 53], [64], [52], [15], [101, 87], [83, 1]], ![[93, 60], [64], [52], [15], [90, 26], [53, 112]]]
 h' := ![![[83, 112], [69, 36], [94, 8], [90, 74], [83, 44], [38, 55], [0, 1]], ![[0, 1], [6, 77], [80, 105], [17, 39], [6, 69], [83, 58], [83, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [108, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [54, 30, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![367, 3129, -5248]
  a := ![5, 3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![607, 585, -5248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![18, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![18, 1, 0]] 
 ![![113, 0, 0], ![18, 1, 0], ![14, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![18, 1, 0], ![2, 19, 8], ![81, -15, 17]]]
  hmulB := by decide  
  f := ![![![-8053, -79403, -33440], ![-1921, 472340, 0]], ![![-1294, -12633, -5320], ![-225, 75145, 0]], ![![-1006, -9838, -4143], ![-186, 58520, 0]]]
  g := ![![![1, 0, 0], ![-18, 113, 0], ![-14, 0, 113]], ![![0, 1, 0], ![-4, 19, 8], ![1, -15, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![13, 12, 1]] ![![113, 0, 0], ![18, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2034, 113, 0]], ![![1469, 1356, 113], ![339, 226, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![18, 1, 0]]], ![![![13, 12, 1]], ![![3, 2, 1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [99, 48, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 14, 3], [26, 112, 124], [0, 1]]
 g := ![![[99, 98, 21], [78, 25, 16], [42, 89, 15], [40, 121, 122], [99, 61, 16], [1]], ![[56, 55, 94, 29], [12, 98, 85, 28], [37, 85, 45, 67], [121, 15, 21, 33], [22, 58, 107, 7], [61, 40, 105, 27]], ![[19, 7, 107, 21], [123, 101, 16, 64], [70, 124, 69, 88], [94, 62, 72, 41], [94, 35, 82, 15], [20, 80, 122, 100]]]
 h' := ![![[105, 14, 3], [25, 77, 104], [33, 116, 123], [104, 47, 53], [105, 26, 54], [28, 79, 4], [0, 1]], ![[26, 112, 124], [89, 71, 68], [12, 85, 27], [110, 63, 108], [99, 122, 30], [77, 105, 50], [105, 14, 3]], ![[0, 1], [77, 106, 82], [76, 53, 104], [110, 17, 93], [86, 106, 43], [102, 70, 73], [26, 112, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 41], []]
 b := ![[], [18, 104, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [99, 48, 123, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35096831, 12214860, -11479530]
  a := ![-10, -5, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-276353, 96180, -90390]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![5, -46, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![5, -46, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![5, 85, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![5, -46, 1], ![-11, -56, -369], ![-3750, 702, 36]]]
  hmulB := by decide  
  f := ![![![-4, 46, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -85, 131]], ![![0, -1, 1], ![14, 239, -369], ![-30, -18, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [47, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 130], [0, 1]]
 g := ![![[22, 27], [77, 9], [81], [16], [38], [65], [1]], ![[7, 104], [72, 122], [81], [16], [38], [65], [1]]]
 h' := ![![[14, 130], [49, 114], [101, 3], [41, 122], [111, 127], [71, 118], [84, 14], [0, 1]], ![[0, 1], [73, 17], [12, 128], [46, 9], [55, 4], [20, 13], [18, 117], [14, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [100, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [47, 117, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7209, -1242, -2462]
  a := ![-2, -6, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![149, 1588, -2462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-24, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-24, 1, 0]] 
 ![![131, 0, 0], ![107, 1, 0], ![95, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-24, 1, 0], ![2, -23, 8], ![81, -15, -25]]]
  hmulB := by decide  
  f := ![![![13729, -165572, 57600], ![-3668, -943200, 0]], ![![11209, -135217, 47040], ![-3012, -770280, 0]], ![![9949, -120071, 41771], ![-2699, -684000, 0]]]
  g := ![![![1, 0, 0], ![-107, 131, 0], ![-95, 0, 131]], ![![-1, 1, 0], ![13, -23, 8], ![31, -15, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![5, -46, 1]] ![![131, 0, 0], ![-24, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3144, 131, 0]], ![![655, -6026, 131], ![-131, 1048, -393]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-24, 1, 0]]], ![![![5, -46, 1]], ![![-1, 8, -3]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-41, 58, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-41, 58, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![96, 58, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-41, 58, 1], ![197, 2, 463], ![4674, -858, -114]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -58, 137]], ![![-1, 0, 1], ![-323, -196, 463], ![114, 42, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [106, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 136], [0, 1]]
 g := ![![[65, 101], [81], [56], [21, 60], [129], [93], [1]], ![[135, 36], [81], [56], [87, 77], [129], [93], [1]]]
 h' := ![![[97, 136], [133, 52], [15, 128], [103, 78], [90, 34], [8, 102], [31, 97], [0, 1]], ![[0, 1], [108, 85], [101, 9], [134, 59], [100, 103], [38, 35], [124, 40], [97, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [68, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [106, 40, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14277, 72641, -127563]
  a := ![27, 13, 95]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89283, 54535, -127563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-52, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-52, 1, 0]] 
 ![![137, 0, 0], ![85, 1, 0], ![114, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-52, 1, 0], ![2, -51, 8], ![81, -15, -53]]]
  hmulB := by decide  
  f := ![![![17217, -539708, 84672], ![-10412, -1450008, 0]], ![![10689, -334819, 52528], ![-6438, -899542, 0]], ![![14322, -449100, 70457], ![-8676, -1206576, 0]]]
  g := ![![![1, 0, 0], ![-85, 137, 0], ![-114, 0, 137]], ![![-1, 1, 0], ![25, -51, 8], ![54, -15, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-41, 58, 1]] ![![137, 0, 0], ![-52, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-7124, 137, 0]], ![![-5617, 7946, 137], ![2329, -3014, 411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-52, 1, 0]]], ![![![-41, 58, 1]], ![![17, -22, 3]]]]
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


lemma PB150I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB150I2 : PrimesBelowBoundCertificateInterval O 79 137 150 where
  m := 11
  g := ![2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB150I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I107N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [], [], [], [], [I107N1], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
