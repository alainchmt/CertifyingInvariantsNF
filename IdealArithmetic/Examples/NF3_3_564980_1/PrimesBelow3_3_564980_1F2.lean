
import IdealArithmetic.Examples.NF3_3_564980_1.RI3_3_564980_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5731, 7158, 1579]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![5731, 7158, 1579]] 
 ![![83, 0, 0], ![0, 83, 0], ![2, 10, 1]] where
  M :=![![![5731, 7158, 1579], ![57686, 72049, 15895], ![287479, 359059, 79207]]]
  hmulB := by decide  
  f := ![![![-5514, -115, 133]], ![![4141, 72, -97]], ![![381, 7, -9]]]
  g := ![![![31, -104, 1579], ![312, -1047, 15895], ![1555, -5217, 79207]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [35, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 82], [0, 1]]
 g := ![![[51, 65], [59, 3], [33], [21], [66, 21], [1]], ![[60, 18], [16, 80], [33], [21], [14, 62], [1]]]
 h' := ![![[41, 82], [10, 27], [28, 70], [42, 45], [14, 42], [48, 41], [0, 1]], ![[0, 1], [38, 56], [76, 13], [61, 38], [76, 41], [69, 42], [41, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [15, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [35, 42, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![271, 276, 94]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -8, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5514, -115, 133]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-5514, -115, 133]] 
 ![![83, 0, 0], ![62, 1, 0], ![29, 0, 1]] where
  M :=![![![-5514, -115, 133], ![4141, 72, -97], ![1241, 91, -43]]]
  hmulB := by decide  
  f := ![![![5731, 7158, 1579]], ![![4976, 6215, 1371]], ![![5466, 6827, 1506]]]
  g := ![![![-27, -115, 133], ![30, 72, -97], ![-38, 91, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![5731, 7158, 1579]] ![![-5514, -115, 133]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [47, 29, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 71, 36], [80, 17, 53], [0, 1]]
 g := ![![[76, 19, 22], [88, 5], [57, 9], [28, 5, 81], [56, 68, 1], []], ![[27, 10, 84, 32], [54, 18], [17, 18], [73, 83, 41, 10], [26, 82, 35, 80], [57, 50]], ![[68, 57, 12, 85], [68, 21], [83, 22], [22, 25, 4, 64], [56, 37, 22, 84], [40, 50]]]
 h' := ![![[77, 71, 36], [63, 22, 17], [85, 16, 70], [19, 41, 3], [38, 75, 9], [0, 0, 1], [0, 1]], ![[80, 17, 53], [47, 40, 13], [87, 10, 75], [21, 30, 14], [86, 64, 5], [46, 78, 17], [77, 71, 36]], ![[0, 1], [76, 27, 59], [35, 63, 33], [38, 18, 72], [82, 39, 75], [70, 11, 71], [80, 17, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 79], []]
 b := ![[], [79, 7, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [47, 29, 21, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147028, 124155, 246085]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1652, 1395, 2765]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61644, -1361, 1502]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-61644, -1361, 1502]] 
 ![![97, 0, 0], ![0, 97, 0], ![65, 2, 1]] where
  M :=![![![-61644, -1361, 1502], ![46703, 1440, -1220], ![12022, -1588, 79]]]
  hmulB := by decide  
  f := ![![![-18800, -23481, -5180]], ![![-189241, -236360, -52142]], ![![-26222, -32751, -7225]]]
  g := ![![![-1642, -45, 1502], ![1299, 40, -1220], ![71, -18, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [43, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 96], [0, 1]]
 g := ![![[64, 88], [91], [89], [81], [64], [61, 1]], ![[0, 9], [91], [89], [81], [64], [25, 96]]]
 h' := ![![[61, 96], [48, 66], [9, 24], [21, 63], [77, 88], [93, 89], [0, 1]], ![[0, 1], [0, 31], [18, 73], [81, 34], [13, 9], [90, 8], [61, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [30, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [43, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158877, 155534, 189026]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125029, -2294, 189026]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18800, -23481, -5180]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-18800, -23481, -5180]] 
 ![![97, 0, 0], ![92, 1, 0], ![85, 0, 1]] where
  M :=![![![-18800, -23481, -5180], ![-189241, -236360, -52142], ![-943052, -1177862, -259841]]]
  hmulB := by decide  
  f := ![![![-61644, -1361, 1502]], ![![-57985, -1276, 1412]], ![![-53894, -1209, 1317]]]
  g := ![![![26616, -23481, -5180], ![267917, -236360, -52142], ![1335121, -1177862, -259841]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-61644, -1361, 1502]] ![![-18800, -23481, -5180]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 10, -2]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![7, 10, -2]] 
 ![![101, 0, 0], ![24, 1, 0], ![66, 0, 1]] where
  M :=![![![7, 10, -2], ![-54, -77, 18], ![246, 346, -67]]]
  hmulB := by decide  
  f := ![![![-1069, -22, 26]], ![![-246, -5, 6]], ![![-696, -14, 17]]]
  g := ![![![-1, 10, -2], ![6, -77, 18], ![-36, 346, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11078, 235, -268]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![11078, 235, -268]] 
 ![![101, 0, 0], ![27, 1, 0], ![40, 0, 1]] where
  M :=![![![11078, 235, -268], ![-8341, -178, 202], ![-2396, -46, 57]]]
  hmulB := by decide  
  f := ![![![854, 1067, 234]], ![![313, 391, 86]], ![![762, 952, 209]]]
  g := ![![![153, 235, -268], ![-115, -178, 202], ![-34, -46, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-116, -145, -32]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-116, -145, -32]] 
 ![![101, 0, 0], ![49, 1, 0], ![12, 0, 1]] where
  M :=![![![-116, -145, -32], ![-1169, -1460, -322], ![-5824, -7274, -1605]]]
  hmulB := by decide  
  f := ![![![1072, 43, -30]], ![![511, 19, -14]], ![![130, 12, -5]]]
  g := ![![![73, -145, -32], ![735, -1460, -322], ![3662, -7274, -1605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![7, 10, -2]] ![![11078, 235, -268]]
  ![![-1072, -43, 30]] where
 M := ![![![-1072, -43, 30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-1072, -43, 30]] ![![-116, -145, -32]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [71, 47, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 66, 24], [65, 36, 79], [0, 1]]
 g := ![![[4, 1, 23], [13, 55, 13], [100, 14, 13], [83, 97], [55, 66], [1]], ![[30, 5, 6, 10], [11, 62, 9, 95], [71, 42, 84, 37], [48, 64], [33, 26], [55, 4, 50, 22]], ![[14, 2, 78, 1], [97, 98, 45, 30], [81, 26, 62, 14], [9, 55], [40, 79], [13, 102, 76, 81]]]
 h' := ![![[25, 66, 24], [4, 65, 34], [7, 37, 42], [90, 50, 42], [3, 21, 32], [32, 56, 90], [0, 1]], ![[65, 36, 79], [52, 24, 3], [20, 32, 31], [16, 66, 34], [98, 55, 8], [81, 62, 52], [25, 66, 24]], ![[0, 1], [13, 14, 66], [88, 34, 30], [89, 90, 27], [78, 27, 63], [31, 88, 64], [65, 36, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 21], []]
 b := ![[], [66, 15, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [71, 47, 13, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-235458, -250908, -215064]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2286, -2436, -2088]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -26, 6]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-17, -26, 6]] 
 ![![107, 0, 0], ![0, 107, 0], ![15, 67, 1]] where
  M :=![![![-17, -26, 6], ![166, 235, -46], ![-610, -870, 209]]]
  hmulB := by decide  
  f := ![![![85, 2, -2]], ![![-62, 1, 2]], ![![-27, 1, 1]]]
  g := ![![![-1, -4, 6], ![8, 31, -46], ![-35, -139, 209]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [87, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 106], [0, 1]]
 g := ![![[32, 16], [21, 64], [41], [30, 105], [41], [105, 1]], ![[0, 91], [0, 43], [41], [34, 2], [41], [103, 106]]]
 h' := ![![[105, 106], [99, 103], [16, 8], [65, 83], [66, 31], [67, 24], [0, 1]], ![[0, 1], [0, 4], [0, 99], [6, 24], [4, 76], [19, 83], [105, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [28, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [87, 2, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363, 316, 174]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -106, 174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -2, 2]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-85, -2, 2]] 
 ![![107, 0, 0], ![79, 1, 0], ![90, 0, 1]] where
  M :=![![![-85, -2, 2], ![62, -1, -2], ![10, -10, -3]]]
  hmulB := by decide  
  f := ![![![17, 26, -6]], ![![11, 17, -4]], ![![20, 30, -7]]]
  g := ![![![-1, -2, 2], ![3, -1, -2], ![10, -10, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-17, -26, 6]] ![![-85, -2, 2]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2456, -55, 60]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2456, -55, 60]] 
 ![![109, 0, 0], ![0, 109, 0], ![39, 99, 1]] where
  M :=![![![-2456, -55, 60], ![1865, 64, -50], ![460, -90, 9]]]
  hmulB := by decide  
  f := ![![![36, 45, 10]], ![![365, 456, 100]], ![![361, 451, 99]]]
  g := ![![![-44, -55, 60], ![35, 46, -50], ![1, -9, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [55, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 108], [0, 1]]
 g := ![![[26, 81], [108], [72, 80], [75, 20], [25], [96, 1]], ![[63, 28], [108], [13, 29], [33, 89], [25], [83, 108]]]
 h' := ![![[96, 108], [43, 100], [73, 76], [17, 84], [57, 67], [61, 5], [0, 1]], ![[0, 1], [51, 9], [66, 33], [15, 25], [58, 42], [105, 104], [96, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [43, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [55, 13, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4427, 5444, 1265]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-412, -1099, 1265]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, -45, -10]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-36, -45, -10]] 
 ![![109, 0, 0], ![19, 1, 0], ![38, 0, 1]] where
  M :=![![![-36, -45, -10], ![-365, -456, -100], ![-1810, -2260, -501]]]
  hmulB := by decide  
  f := ![![![2456, 55, -60]], ![![411, 9, -10]], ![![852, 20, -21]]]
  g := ![![![11, -45, -10], ![111, -456, -100], ![552, -2260, -501]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2456, -55, 60]] ![![-36, -45, -10]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1779, 202, -76]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1779, 202, -76]] 
 ![![113, 0, 0], ![0, 113, 0], ![100, 36, 1]] where
  M :=![![![1779, 202, -76], ![-2230, -1413, 328], ![3652, 5672, -1211]]]
  hmulB := by decide  
  f := ![![![-1321, -1650, -364]], ![![-13298, -16609, -3664]], ![![-5992, -7484, -1651]]]
  g := ![![![83, 26, -76], ![-310, -117, 328], ![1104, 436, -1211]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [76, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 112], [0, 1]]
 g := ![![[20, 52], [11], [28], [50], [0, 52], [62, 1]], ![[80, 61], [11], [28], [50], [60, 61], [11, 112]]]
 h' := ![![[62, 112], [15, 74], [88, 89], [42, 49], [0, 29], [34, 39], [0, 1]], ![[0, 1], [83, 39], [69, 24], [29, 64], [103, 84], [79, 74], [62, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [20, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [76, 51, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-256, -282, 237]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-212, -78, 237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1321, 1650, 364]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1321, 1650, 364]] 
 ![![113, 0, 0], ![40, 1, 0], ![48, 0, 1]] where
  M :=![![![1321, 1650, 364], ![13298, 16609, 3664], ![66268, 82768, 18259]]]
  hmulB := by decide  
  f := ![![![-1779, -202, 76]], ![![-610, -59, 24]], ![![-788, -136, 43]]]
  g := ![![![-727, 1650, 364], ![-7318, 16609, 3664], ![-36468, 82768, 18259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1779, 202, -76]] ![![1321, 1650, 364]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [20, 77, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 19, 28], [90, 107, 99], [0, 1]]
 g := ![![[108, 51, 104], [15], [91, 4, 124], [121, 90, 87], [71, 2, 47], [1]], ![[67, 93, 120, 109], [18, 16, 49, 96], [25, 24, 73, 7], [107, 55, 124, 90], [1, 66, 85, 28], [98, 67, 71, 108]], ![[31, 83, 52, 120], [49, 47, 104, 31], [54, 41, 75, 26], [10, 16, 110, 9], [79, 96, 100, 22], [57, 86, 117, 19]]]
 h' := ![![[126, 19, 28], [81, 101, 72], [85, 74], [120, 80, 39], [104, 100, 50], [107, 50, 89], [0, 1]], ![[90, 107, 99], [27, 14, 118], [11, 9, 40], [39, 123, 63], [19, 122, 22], [71, 61, 1], [126, 19, 28]], ![[0, 1], [23, 12, 64], [14, 44, 87], [100, 51, 25], [56, 32, 55], [23, 16, 37], [90, 107, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 122], []]
 b := ![[], [95, 100, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [20, 77, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![280162, 327406, 155194]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2206, 2578, 1222]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -9, 2]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-10, -9, 2]] 
 ![![131, 0, 0], ![53, 1, 0], ![37, 0, 1]] where
  M :=![![![-10, -9, 2], ![55, 74, -16], ![-214, -304, 65]]]
  hmulB := by decide  
  f := ![![![-54, -23, -4]], ![![-23, -11, -2]], ![![-22, -15, -3]]]
  g := ![![![3, -9, 2], ![-25, 74, -16], ![103, -304, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 42, -9]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![29, 42, -9]] 
 ![![131, 0, 0], ![83, 1, 0], ![93, 0, 1]] where
  M :=![![![29, 42, -9], ![-246, -349, 75], ![1011, 1431, -307]]]
  hmulB := by decide  
  f := ![![![-182, 15, 9]], ![![-113, 11, 6]], ![![-123, 18, 8]]]
  g := ![![![-20, 42, -9], ![166, -349, 75], ![-681, 1431, -307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 70, 17]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![3, 70, 17]] 
 ![![131, 0, 0], ![125, 1, 0], ![48, 0, 1]] where
  M :=![![![3, 70, 17], ![614, 717, 157], ![2869, 3569, 787]]]
  hmulB := by decide  
  f := ![![![-3946, -5583, 1199]], ![![-3515, -4973, 1068]], ![![-2471, -3497, 751]]]
  g := ![![![-73, 70, 17], ![-737, 717, 157], ![-3672, 3569, 787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-10, -9, 2]] ![![29, 42, -9]]
  ![![3946, 5583, -1199]] where
 M := ![![![3946, 5583, -1199]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![3946, 5583, -1199]] ![![3, 70, 17]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [128, 82, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 80, 78], [55, 56, 59], [0, 1]]
 g := ![![[113, 30, 98], [45, 2], [98, 121], [35, 45, 76], [90, 39], [113, 1], []], ![[44, 11, 132, 22], [113, 115], [123, 32], [75, 28, 131, 32], [63, 109], [110, 122], [39, 56]], ![[131, 72, 6, 37], [43, 60], [96, 28], [71, 87, 107, 38], [53, 15], [21, 98], [58, 56]]]
 h' := ![![[58, 80, 78], [87, 44, 80], [97, 70, 31], [41, 124, 11], [64, 89, 79], [58, 59, 83], [0, 0, 1], [0, 1]], ![[55, 56, 59], [83, 73, 103], [132, 19, 72], [11, 29, 13], [51, 101, 132], [13, 70, 71], [16, 10, 56], [58, 80, 78]], ![[0, 1], [74, 20, 91], [57, 48, 34], [120, 121, 113], [75, 84, 63], [3, 8, 120], [122, 127, 80], [55, 56, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 58], []]
 b := ![[], [122, 124, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [128, 82, 24, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-333732, -380175, -219885]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2436, -2775, -1605]
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



lemma PB168I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB168I2 : PrimesBelowBoundCertificateInterval O 79 137 168 where
  m := 11
  g := ![2, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB168I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI101N2
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
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I97N1, I101N0, I101N1, I101N2, I107N1, I109N1, I113N1, I131N0, I131N1, I131N2]
  Il := ![[I83N1], [], [I97N1], [I101N0, I101N1, I101N2], [], [I107N1], [I109N1], [I113N1], [], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
