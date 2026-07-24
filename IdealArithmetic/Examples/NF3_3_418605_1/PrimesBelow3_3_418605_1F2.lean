
import IdealArithmetic.Examples.NF3_3_418605_1.RI3_3_418605_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [49, 32, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 27, 19], [60, 55, 64], [0, 1]]
 g := ![![[70, 21, 21], [2, 79, 69], [15, 21], [78, 25], [61, 33, 1], []], ![[11, 71], [17, 63, 57, 18], [14, 48], [32, 12], [13, 82, 24, 39], [74, 29]], ![[47, 73, 51, 16], [7, 64, 45, 41], [68, 38], [71, 48], [34, 30, 45, 10], [29, 29]]]
 h' := ![![[56, 27, 19], [68, 75, 42], [21, 67, 22], [80, 14, 41], [82, 0, 78], [0, 0, 1], [0, 1]], ![[60, 55, 64], [39, 24], [48, 2, 76], [30, 55, 31], [42, 7, 57], [8, 65, 55], [56, 27, 19]], ![[0, 1], [55, 67, 41], [21, 14, 68], [38, 14, 11], [60, 76, 31], [21, 18, 27], [60, 55, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 43], []]
 b := ![[], [62, 11, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [49, 32, 50, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88644, -53784, -21663]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1068, -648, -261]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28871, -846, 826]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-28871, -846, 826]] 
 ![![89, 0, 0], ![0, 89, 0], ![52, 16, 1]] where
  M :=![![![-28871, -846, 826], ![60318, 1711, -1712], ![-31176, -720, 845]]]
  hmulB := by decide  
  f := ![![![-2395, -1350, -394]], ![![-27018, -15229, -4444]], ![![-7508, -4232, -1235]]]
  g := ![![![-807, -158, 826], ![1678, 327, -1712], ![-844, -160, 845]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [56, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 88], [0, 1]]
 g := ![![[75, 47], [36], [79], [54, 80], [17, 22], [1]], ![[77, 42], [36], [79], [29, 9], [88, 67], [1]]]
 h' := ![![[72, 88], [41, 15], [30, 6], [2, 48], [27, 13], [33, 72], [0, 1]], ![[0, 1], [53, 74], [17, 83], [76, 41], [73, 76], [55, 17], [72, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [86, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [56, 17, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3467, -656, 2451]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1471, -448, 2451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2395, 1350, 394]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![2395, 1350, 394]] 
 ![![89, 0, 0], ![40, 1, 0], ![73, 0, 1]] where
  M :=![![![2395, 1350, 394], ![27018, 15229, 4444], ![111384, 62784, 18323]]]
  hmulB := by decide  
  f := ![![![28871, 846, -826]], ![![12298, 361, -352]], ![![24031, 702, -687]]]
  g := ![![![-903, 1350, 394], ![-10186, 15229, 4444], ![-41995, 62784, 18323]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-28871, -846, 826]] ![![2395, 1350, 394]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [81, 67, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 86, 60], [27, 10, 37], [0, 1]]
 g := ![![[2, 26, 81], [49, 12], [84, 61], [56, 53], [78, 86], [1]], ![[57, 95, 85, 30], [72, 35], [37, 27], [58, 12], [50, 61], [30, 88, 68, 78]], ![[53, 59, 61, 51], [94, 32], [22, 25], [3, 1], [47, 91], [77, 6, 93, 19]]]
 h' := ![![[32, 86, 60], [80, 0, 88], [84, 49, 20], [96, 26, 35], [49, 20, 76], [16, 30, 59], [0, 1]], ![[27, 10, 37], [91, 70, 7], [54, 6, 36], [23, 13, 67], [68, 8, 20], [74, 41, 62], [32, 86, 60]], ![[0, 1], [16, 27, 2], [8, 42, 41], [23, 58, 92], [84, 69, 1], [60, 26, 73], [27, 10, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 10], []]
 b := ![[], [75, 46, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [81, 67, 38, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1103604017, -748355776, -422792154]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11377361, -7715008, -4358682]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![20, 29, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![20, 29, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![20, 29, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![20, 29, 1], ![43, 27, 88], ![2124, 1080, 86]]]
  hmulB := by decide  
  f := ![![![-19, -29, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -29, 101]], ![![0, 0, 1], ![-17, -25, 88], ![4, -14, 86]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [57, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 100], [0, 1]]
 g := ![![[45, 87], [71], [8, 77], [45], [77], [61, 1]], ![[100, 14], [71], [59, 24], [45], [77], [21, 100]]]
 h' := ![![[61, 100], [71, 17], [49, 24], [84, 28], [86, 67], [58, 28], [0, 1]], ![[0, 1], [98, 84], [99, 77], [75, 73], [32, 34], [49, 73], [61, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [25, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [57, 40, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2134, 168, 1984]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-414, -568, 1984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![13, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![13, 1, 0]] 
 ![![101, 0, 0], ![13, 1, 0], ![15, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![13, 1, 0], ![-1, 12, 3], ![72, 36, 14]]]
  hmulB := by decide  
  f := ![![![-5949, 71400, 17850], ![0, -600950, 0]], ![![-765, 9180, 2295], ![1, -77265, 0]], ![![-883, 10604, 2651], ![-4, -89250, 0]]]
  g := ![![![1, 0, 0], ![-13, 101, 0], ![-15, 0, 101]], ![![0, 1, 0], ![-2, 12, 3], ![-6, 36, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![20, 29, 1]] ![![101, 0, 0], ![13, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1313, 101, 0]], ![![2020, 2929, 101], ![303, 404, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![13, 1, 0]]], ![![![20, 29, 1]], ![![3, 4, 1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![21, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![21, 1, 0]] 
 ![![103, 0, 0], ![21, 1, 0], ![100, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![21, 1, 0], ![-1, 20, 3], ![72, 36, 22]]]
  hmulB := by decide  
  f := ![![![-3833, 76680, 11502], ![0, -394902, 0]], ![![-781, 15620, 2343], ![1, -80443, 0]], ![![-3734, 74446, 11167], ![62, -383400, 0]]]
  g := ![![![1, 0, 0], ![-21, 103, 0], ![-100, 0, 103]], ![![0, 1, 0], ![-7, 20, 3], ![-28, 36, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![38, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![38, 1, 0]] 
 ![![103, 0, 0], ![38, 1, 0], ![46, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![38, 1, 0], ![-1, 37, 3], ![72, 36, 39]]]
  hmulB := by decide  
  f := ![![![-873, 32338, 2622], ![0, -90022, 0]], ![![-322, 11914, 966], ![1, -33166, 0]], ![![-398, 14442, 1171], ![22, -40204, 0]]]
  g := ![![![1, 0, 0], ![-38, 103, 0], ![-46, 0, 103]], ![![0, 1, 0], ![-15, 37, 3], ![-30, 36, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-434, -11, 12]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-434, -11, 12]] 
 ![![103, 0, 0], ![44, 1, 0], ![90, 0, 1]] where
  M :=![![![-434, -11, 12], ![875, 9, -21], ![-360, 36, -1]]]
  hmulB := by decide  
  f := ![![![-747, -421, -123]], ![![-401, -226, -66]], ![![-990, -558, -163]]]
  g := ![![![-10, -11, 12], ![23, 9, -21], ![-18, 36, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![21, 1, 0]] ![![103, 0, 0], ![38, 1, 0]]
  ![![-747, -421, -123]] where
 M := ![![![10609, 0, 0], ![3914, 103, 0]], ![![2163, 103, 0], ![797, 58, 3]]]
 hmul := by decide  
 g := ![![![![-44702, -1133, 1236]], ![![-15617, -409, 435]]], ![![![-8239, -222, 231]], ![![-2876, -79, 81]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-747, -421, -123]] ![![-434, -11, 12]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![13, -44, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![13, -44, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![13, 63, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![13, -44, 1], ![116, 93, -131], ![-3132, -1548, 6]]]
  hmulB := by decide  
  f := ![![![-12, 44, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -63, 107]], ![![0, -1, 1], ![17, 78, -131], ![-30, -18, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [32, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 106], [0, 1]]
 g := ![![[43, 11], [102, 9], [83], [83, 90], [13], [15, 1]], ![[101, 96], [23, 98], [83], [42, 17], [13], [30, 106]]]
 h' := ![![[15, 106], [53, 15], [59, 104], [19, 46], [41, 25], [55, 86], [0, 1]], ![[0, 1], [64, 92], [14, 3], [67, 61], [95, 82], [61, 21], [15, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [52, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [32, 92, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![449, 324, 51]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -27, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![24, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![24, 1, 0]] 
 ![![107, 0, 0], ![24, 1, 0], ![101, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![24, 1, 0], ![-1, 23, 3], ![72, 36, 25]]]
  hmulB := by decide  
  f := ![![![-2145, 49358, 6438], ![0, -229622, 0]], ![![-481, 11063, 1443], ![1, -51467, 0]], ![![-2031, 46590, 6077], ![28, -216746, 0]]]
  g := ![![![1, 0, 0], ![-24, 107, 0], ![-101, 0, 107]], ![![0, 1, 0], ![-8, 23, 3], ![-31, 36, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![13, -44, 1]] ![![107, 0, 0], ![24, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2568, 107, 0]], ![![1391, -4708, 107], ![428, -963, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![24, 1, 0]]], ![![![13, -44, 1]], ![![4, -9, -1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [59, 76, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 20, 102], [13, 88, 7], [0, 1]]
 g := ![![[84, 61, 105], [108, 60], [4, 104, 43], [24, 5, 61], [63, 27], [1]], ![[16, 35, 41, 36], [98, 4], [50, 96, 5, 4], [37, 1, 106, 108], [92, 48], [28, 43, 60, 93]], ![[87, 99, 15, 12], [89, 12], [9, 51, 99, 48], [64, 32, 28, 12], [90, 38], [37, 55, 11, 16]]]
 h' := ![![[58, 20, 102], [56, 94, 43], [91, 101, 96], [1, 58, 77], [91, 80, 37], [50, 33, 71], [0, 1]], ![[13, 88, 7], [17, 75, 74], [83, 8, 2], [52, 14, 48], [29, 57, 80], [94, 103, 22], [58, 20, 102]], ![[0, 1], [86, 49, 101], [66, 0, 11], [2, 37, 93], [9, 81, 101], [14, 82, 16], [13, 88, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 97], []]
 b := ![[], [39, 70, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [59, 76, 38, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4298960, 2419146, 701088]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39440, 22194, 6432]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [67, 101, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 57, 109], [104, 55, 4], [0, 1]]
 g := ![![[102, 16, 100], [21, 7], [95, 25], [30, 100], [20, 92, 14], [1]], ![[42, 76, 64, 52], [23, 32], [70, 91], [7, 88], [100, 57, 21, 52], [84, 105, 101, 49]], ![[59, 48, 65, 18], [63, 91], [70, 28], [52, 106], [89, 51, 61, 72], [68, 32, 77, 64]]]
 h' := ![![[59, 57, 109], [40, 91, 103], [54, 74, 81], [54, 59, 108], [16, 34, 10], [46, 12, 50], [0, 1]], ![[104, 55, 4], [52, 27, 103], [24, 23, 91], [9, 105, 54], [34, 92, 75], [80, 42, 103], [59, 57, 109]], ![[0, 1], [17, 108, 20], [82, 16, 54], [34, 62, 64], [44, 100, 28], [26, 59, 73], [104, 55, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 103], []]
 b := ![[], [89, 78, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [67, 101, 63, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![145544, 42488, -46104]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1288, 376, -408]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [25, 34, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 52, 116], [97, 74, 11], [0, 1]]
 g := ![![[12, 29, 87], [31, 62, 76], [51, 35, 72], [114, 77, 21], [42, 24, 61], [1]], ![[83, 31, 50, 7], [96, 81, 85, 108], [126, 29, 44, 5], [12, 98, 116, 65], [36, 111, 15, 108], [115, 8, 17, 66]], ![[67, 22, 46, 60], [83, 96, 76, 99], [83, 31, 41, 42], [97, 115, 61, 69], [24, 100, 1, 69], [1, 28, 1, 61]]]
 h' := ![![[81, 52, 116], [114, 88, 50], [122, 19, 40], [71, 54, 31], [93, 121, 104], [102, 93, 51], [0, 1]], ![[97, 74, 11], [95, 9, 65], [109, 103, 84], [118, 106, 49], [93, 54, 15], [119, 104, 84], [81, 52, 116]], ![[0, 1], [80, 30, 12], [62, 5, 3], [21, 94, 47], [75, 79, 8], [26, 57, 119], [97, 74, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 29], []]
 b := ![[], [68, 74, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [25, 34, 76, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![594614, 485648, 388620]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4682, 3824, 3060]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [84, 60, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 64, 7], [113, 66, 124], [0, 1]]
 g := ![![[40, 73, 7], [42, 111, 63], [65, 121], [71, 48], [47, 45], [28, 1], []], ![[68, 1, 47, 108], [16, 82, 49, 113], [74, 7], [125, 74], [114, 33], [105, 33], [41, 49]], ![[28, 19, 42, 57], [51, 7, 101, 92], [99, 44], [47, 36], [30, 16], [95, 35], [55, 49]]]
 h' := ![![[46, 64, 7], [9, 105, 20], [91, 55, 60], [124, 105, 11], [18, 4, 21], [6, 70, 69], [0, 0, 1], [0, 1]], ![[113, 66, 124], [25, 34, 90], [100, 99, 22], [40, 69, 20], [86, 87, 104], [19, 107, 66], [113, 98, 66], [46, 64, 7]], ![[0, 1], [100, 123, 21], [66, 108, 49], [103, 88, 100], [120, 40, 6], [85, 85, 127], [27, 33, 64], [113, 66, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 4], []]
 b := ![[], [19, 38, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [84, 60, 103, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-397716, -235800, -85150]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3036, -1800, -650]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 11, -3]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![9, 11, -3]] 
 ![![137, 0, 0], ![0, 137, 0], ![134, 42, 1]] where
  M :=![![![9, 11, -3], ![-227, -110, 30], ![684, 288, -91]]]
  hmulB := by decide  
  f := ![![![-10, -1, 0]], ![![1, -9, -3]], ![![-10, -4, -1]]]
  g := ![![![3, 1, -3], ![-31, -10, 30], ![94, 30, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [128, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 136], [0, 1]]
 g := ![![[14, 76], [32], [112], [46, 135], [73], [121], [1]], ![[0, 61], [32], [112], [68, 2], [73], [121], [1]]]
 h' := ![![[126, 136], [90, 58], [58, 124], [3, 89], [105, 51], [74, 115], [9, 126], [0, 1]], ![[0, 1], [0, 79], [64, 13], [120, 48], [92, 86], [42, 22], [130, 11], [126, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [20, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [128, 11, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11554, -4836, 2664]
  a := ![-2, -12, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2690, -852, 2664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![10, 1, 0]] 
 ![![137, 0, 0], ![10, 1, 0], ![61, 0, 1]] where
  M :=![![![10, 1, 0], ![-1, 9, 3], ![72, 36, 11]]]
  hmulB := by decide  
  f := ![![![-9, -11, 3]], ![![1, 0, 0]], ![![-9, -7, 2]]]
  g := ![![![0, 1, 0], ![-2, 9, 3], ![-7, 36, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![9, 11, -3]] ![![10, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB144I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB144I2 : PrimesBelowBoundCertificateInterval O 79 137 144 where
  m := 11
  g := ![1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB144I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![18769, 137]
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
      exact NI103N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I137N1]
  Il := ![[], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
