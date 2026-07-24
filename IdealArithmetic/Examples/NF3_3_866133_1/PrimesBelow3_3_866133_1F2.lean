
import IdealArithmetic.Examples.NF3_3_866133_1.RI3_3_866133_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [9, 14, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 16, 40], [76, 66, 43], [0, 1]]
 g := ![![[75, 60, 44], [44, 65, 36], [76, 81], [27, 44], [61, 65, 1], []], ![[55, 82, 51, 3], [61, 48, 55, 29], [71, 75], [3, 48], [3, 51, 46, 23], [36, 23]], ![[15, 1, 5, 52], [67, 73, 34, 50], [1, 81], [81, 65], [32, 5, 3, 52], [33, 23]]]
 h' := ![![[72, 16, 40], [19, 56, 58], [57, 11, 6], [34, 7, 74], [32, 55, 58], [0, 0, 1], [0, 1]], ![[76, 66, 43], [79, 81, 9], [46, 23, 6], [41, 51, 18], [20, 65, 52], [46, 16, 66], [72, 16, 40]], ![[0, 1], [17, 29, 16], [69, 49, 71], [59, 25, 74], [37, 46, 56], [1, 67, 16], [76, 66, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 56], []]
 b := ![[], [61, 53, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [9, 14, 18, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8148940, -2343007, -856560]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98180, -28229, -10320]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![843, 30, -16]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![843, 30, -16]] 
 ![![89, 0, 0], ![0, 89, 0], ![53, 76, 1]] where
  M :=![![![843, 30, -16], ![-5524, -195, 104], ![7174, 242, -135]]]
  hmulB := by decide  
  f := ![![![-13, -2, 0]], ![![-4, -11, -8]], ![![-19, -12, -7]]]
  g := ![![![19, 14, -16], ![-124, -91, 104], ![161, 118, -135]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [76, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 88], [0, 1]]
 g := ![![[49, 8], [2], [81], [39, 20], [82, 18], [1]], ![[72, 81], [2], [81], [52, 69], [67, 71], [1]]]
 h' := ![![[14, 88], [30, 39], [2, 25], [62, 9], [87, 38], [13, 14], [0, 1]], ![[0, 1], [42, 50], [85, 64], [10, 80], [85, 51], [31, 75], [14, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [18, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [76, 75, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4236, 2149, 3648]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2220, -3091, 3648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -2, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-13, -2, 0]] 
 ![![89, 0, 0], ![51, 1, 0], ![75, 0, 1]] where
  M :=![![![-13, -2, 0], ![-4, -11, -8], ![-698, -126, -15]]]
  hmulB := by decide  
  f := ![![![843, 30, -16]], ![![421, 15, -8]], ![![791, 28, -15]]]
  g := ![![![1, -2, 0], ![13, -11, -8], ![77, -126, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![843, 30, -16]] ![![-13, -2, 0]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-17, -8, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-17, -8, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![80, 89, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-17, -8, 1], ![333, 54, -31], ![-2586, -401, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -89, 97]], ![![-1, -1, 1], ![29, 29, -31], ![-58, -39, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [18, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 96], [0, 1]]
 g := ![![[21, 27], [24], [93], [72], [31], [10, 1]], ![[0, 70], [24], [93], [72], [31], [20, 96]]]
 h' := ![![[10, 96], [88, 30], [61, 11], [59, 44], [26, 84], [14, 82], [0, 1]], ![[0, 1], [0, 67], [74, 86], [14, 53], [90, 13], [58, 15], [10, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [35, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [18, 87, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![849858, 440308, 277138]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-219806, -249742, 277138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![31, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![31, 1, 0]] 
 ![![97, 0, 0], ![31, 1, 0], ![59, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![31, 1, 0], ![2, 30, 4], ![349, 63, 32]]]
  hmulB := by decide  
  f := ![![![7062, 123083, 16416], ![3589, -398088, 0]], ![![2250, 39318, 5244], ![1165, -127167, 0]], ![![4298, 74865, 9985], ![2175, -242136, 0]]]
  g := ![![![1, 0, 0], ![-31, 97, 0], ![-59, 0, 97]], ![![0, 1, 0], ![-12, 30, 4], ![-36, 63, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-17, -8, 1]] ![![97, 0, 0], ![31, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3007, 97, 0]], ![![-1649, -776, 97], ![-194, -194, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![31, 1, 0]]], ![![![-17, -8, 1]], ![![-2, -2, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [44, 40, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 82, 99], [41, 18, 2], [0, 1]]
 g := ![![[66, 98, 54], [67, 22], [75, 31, 30], [29, 17], [22, 13], [1]], ![[46, 52, 88, 66], [60, 76], [51, 100, 68, 55], [100, 37], [81, 5], [86, 68, 52, 93]], ![[97, 52, 53, 18], [82, 24], [14, 60, 90, 63], [99, 24], [50, 37], [79, 13, 37, 8]]]
 h' := ![![[25, 82, 99], [60, 1, 85], [33, 66, 27], [84, 19, 63], [59, 48, 57], [57, 61, 66], [0, 1]], ![[41, 18, 2], [74, 65, 13], [54, 94, 51], [91, 91, 86], [42, 26, 21], [24, 60, 56], [25, 82, 99]], ![[0, 1], [73, 35, 3], [34, 42, 23], [39, 92, 53], [31, 27, 23], [98, 81, 80], [41, 18, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 12], []]
 b := ![[], [13, 4, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [44, 40, 35, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19614301, -6457536, -2715183]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-194201, -63936, -26883]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-63, 0, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-63, 0, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![40, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-63, 0, 1], ![349, 0, 1], ![206, 103, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, 0, 103]], ![![-1, 0, 1], ![3, 0, 1], ![2, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [58, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 102], [0, 1]]
 g := ![![[54, 16], [93, 64], [], [63], [68], [61, 1]], ![[0, 87], [83, 39], [], [63], [68], [19, 102]]]
 h' := ![![[61, 102], [65, 4], [0, 8], [27], [30, 75], [67, 58], [0, 1]], ![[0, 1], [0, 99], [76, 95], [27], [73, 28], [0, 45], [61, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [27, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [58, 42, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3171, 2987, 2044]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-763, 29, 2044]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-1, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-1, 1, 0]] 
 ![![103, 0, 0], ![102, 1, 0], ![0, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-1, 1, 0], ![2, -2, 4], ![349, 63, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![52, 26, 0]]]
  g := ![![![1, 0, 0], ![-102, 103, 0], ![0, 0, 103]], ![![-1, 1, 0], ![2, -2, 4], ![-59, 63, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-63, 0, 1]] ![![103, 0, 0], ![-1, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-103, 103, 0]], ![![-6489, 0, 103], ![412, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-1, 1, 0]]], ![![![-63, 0, 1]], ![![4, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [36, 76, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 17, 71], [95, 89, 36], [0, 1]]
 g := ![![[97, 83, 19], [14, 89, 12], [44, 53], [103, 60, 3], [64, 87], [1]], ![[29, 99, 45, 58], [50, 22, 45, 20], [52, 87], [40, 38, 13, 106], [25, 9], [80, 47, 76, 103]], ![[98, 51, 22, 101], [55, 24, 19, 92], [90, 14], [95, 65, 7, 4], [12, 44], [76, 95, 102, 4]]]
 h' := ![![[39, 17, 71], [31, 13, 74], [106, 85, 71], [37, 62, 38], [62, 44, 18], [71, 31, 27], [0, 1]], ![[95, 89, 36], [44, 2, 19], [32, 68, 49], [70, 100, 80], [102, 99, 18], [50, 35, 3], [39, 17, 71]], ![[0, 1], [53, 92, 14], [0, 61, 94], [64, 52, 96], [40, 71, 71], [30, 41, 77], [95, 89, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 45], []]
 b := ![[], [19, 27, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [36, 76, 80, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3818115133, 1036308268, 354740952]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35683319, 9685124, 3315336]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1516, 55, -29]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1516, 55, -29]] 
 ![![109, 0, 0], ![0, 109, 0], ![68, 62, 1]] where
  M :=![![![1516, 55, -29], ![-10011, -366, 191], ![13221, 478, -256]]]
  hmulB := by decide  
  f := ![![![22, 2, -1]], ![![-345, -43, 7]], ![![-178, -23, 3]]]
  g := ![![![32, 17, -29], ![-211, -112, 191], ![281, 150, -256]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [95, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 108], [0, 1]]
 g := ![![[102, 38], [75], [100, 15], [23, 66], [22], [11, 1]], ![[84, 71], [75], [47, 94], [95, 43], [22], [22, 108]]]
 h' := ![![[11, 108], [31, 16], [92, 27], [104, 61], [44, 75], [45, 26], [0, 1]], ![[0, 1], [98, 93], [62, 82], [12, 48], [106, 34], [4, 83], [11, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [21, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [95, 98, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1001, 326, 167]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-95, -92, 167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 2, -1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![22, 2, -1]] 
 ![![109, 0, 0], ![78, 1, 0], ![25, 0, 1]] where
  M :=![![![22, 2, -1], ![-345, -43, 7], ![492, 23, -39]]]
  hmulB := by decide  
  f := ![![![1516, 55, -29]], ![![993, 36, -19]], ![![469, 17, -9]]]
  g := ![![![-1, 2, -1], ![26, -43, 7], ![-3, 23, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1516, 55, -29]] ![![22, 2, -1]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-48, 23, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-48, 23, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![65, 23, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-48, 23, 1], ![395, -8, 93], ![8233, 1552, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -23, 113]], ![![-1, 0, 1], ![-50, -19, 93], ![51, 6, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [89, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 112], [0, 1]]
 g := ![![[26, 77], [111], [56], [51], [24, 4], [59, 1]], ![[49, 36], [111], [56], [51], [34, 109], [5, 112]]]
 h' := ![![[59, 112], [81, 90], [109, 87], [102, 100], [11, 27], [60, 2], [0, 1]], ![[0, 1], [80, 23], [44, 26], [13, 13], [22, 86], [65, 111], [59, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [97, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [89, 54, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7032, 7648, 6916]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3916, -1340, 6916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![20, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![20, 1, 0]] 
 ![![113, 0, 0], ![20, 1, 0], ![75, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![20, 1, 0], ![2, 19, 4], ![349, 63, 21]]]
  hmulB := by decide  
  f := ![![![-3191, -31647, -6664], ![-791, 188258, 0]], ![![-568, -5585, -1176], ![-112, 33222, 0]], ![![-2125, -21005, -4423], ![-485, 124950, 0]]]
  g := ![![![1, 0, 0], ![-20, 113, 0], ![-75, 0, 113]], ![![0, 1, 0], ![-6, 19, 4], ![-22, 63, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-48, 23, 1]] ![![113, 0, 0], ![20, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2260, 113, 0]], ![![-5424, 2599, 113], ![-565, 452, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![20, 1, 0]]], ![![![-48, 23, 1]], ![![-5, 4, 1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [82, 85, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 108, 99], [75, 18, 28], [0, 1]]
 g := ![![[111, 79, 99], [56, 21, 36], [96, 86, 107], [2, 111, 35], [96, 65, 100], [1]], ![[113, 68, 118, 68], [32, 63, 86, 52], [113, 91, 31, 69], [119, 37, 29, 71], [45, 64, 17, 49], [52, 5, 80, 19]], ![[57, 110, 103, 111], [54, 33, 4, 33], [0, 112, 26, 7], [69, 90, 118, 12], [113, 107, 126, 111], [108, 62, 108, 108]]]
 h' := ![![[42, 108, 99], [107, 126, 37], [2, 0, 6], [90, 3, 108], [2, 92, 17], [45, 42, 117], [0, 1]], ![[75, 18, 28], [60, 123, 59], [87, 10, 108], [95, 123, 82], [64, 16, 16], [101, 32, 41], [42, 108, 99]], ![[0, 1], [114, 5, 31], [5, 117, 13], [115, 1, 64], [116, 19, 94], [15, 53, 96], [75, 18, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 13], []]
 b := ![[], [1, 26, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [82, 85, 10, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6141593, -1635125, -542925]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48359, -12875, -4275]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![17, 9, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![17, 9, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![17, 9, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![17, 9, 1], ![367, 71, 37], ![3347, 670, 89]]]
  hmulB := by decide  
  f := ![![![-16, -9, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -9, 131]], ![![0, 0, 1], ![-2, -2, 37], ![14, -1, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [129, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 130], [0, 1]]
 g := ![![[110, 65], [99, 9], [45], [1], [48], [61], [1]], ![[0, 66], [114, 122], [45], [1], [48], [61], [1]]]
 h' := ![![[89, 130], [67, 117], [14, 3], [102, 69], [121, 1], [126, 21], [2, 89], [0, 1]], ![[0, 1], [0, 14], [19, 128], [86, 62], [79, 130], [30, 110], [63, 42], [89, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [119, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [129, 42, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34545, 12748, 6016]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-517, -316, 6016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-37, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-37, 1, 0]] 
 ![![131, 0, 0], ![94, 1, 0], ![42, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-37, 1, 0], ![2, -38, 4], ![349, 63, -36]]]
  hmulB := by decide  
  f := ![![![-10590, 227203, -23920], ![4847, 783380, 0]], ![![-7617, 162994, -17160], ![3407, 561990, 0]], ![![-3369, 72843, -7669], ![1647, 251160, 0]]]
  g := ![![![1, 0, 0], ![-94, 131, 0], ![-42, 0, 131]], ![![-1, 1, 0], ![26, -38, 4], ![-31, 63, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![17, 9, 1]] ![![131, 0, 0], ![-37, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4847, 131, 0]], ![![2227, 1179, 131], ![-262, -262, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-37, 1, 0]]], ![![![17, 9, 1]], ![![-2, -2, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [40, 12, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 40, 30], [135, 96, 107], [0, 1]]
 g := ![![[27, 22, 68], [125, 87], [104, 39], [29, 46, 101], [3, 17], [14, 1], []], ![[71, 75, 85, 101], [12, 105], [31, 118], [73, 105, 124, 22], [98, 69], [44, 37], [67, 78]], ![[46, 99, 45, 121], [22, 135], [68, 2], [136, 97, 105, 22], [17, 136], [61, 93], [127, 78]]]
 h' := ![![[16, 40, 30], [55, 14, 94], [73, 83, 19], [73, 32, 83], [24, 29, 52], [125, 66, 47], [0, 0, 1], [0, 1]], ![[135, 96, 107], [117, 131, 128], [7, 75, 67], [98, 69, 23], [69, 124, 108], [4, 28, 53], [42, 96, 96], [16, 40, 30]], ![[0, 1], [54, 129, 52], [48, 116, 51], [113, 36, 31], [13, 121, 114], [75, 43, 37], [130, 41, 40], [135, 96, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 57], []]
 b := ![[], [34, 10, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [40, 12, 123, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156109171, 44575416, 16524255]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1139483, 325368, 120615]
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



lemma PB207I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB207I2 : PrimesBelowBoundCertificateInterval O 79 137 207 where
  m := 11
  g := ![1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB207I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI103N1
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
  β := ![I89N1, I97N1, I103N1, I109N1, I113N1, I131N1]
  Il := ![[], [I89N1], [I97N1], [], [I103N1], [], [I109N1], [I113N1], [], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
