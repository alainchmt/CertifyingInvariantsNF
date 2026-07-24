
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [47, 9, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 41, 5], [67, 41, 78], [0, 1]]
 g := ![![[71, 25, 9], [72, 51, 61], [71, 69], [71, 28], [1, 50, 1], []], ![[77, 45, 51, 80], [15, 5, 34, 73], [23, 41], [73, 49], [62, 14, 32, 22], [0, 25]], ![[11, 46, 44, 4], [44, 5, 24, 36], [10, 78], [13, 44], [78, 36, 73, 61], [10, 25]]]
 h' := ![![[66, 41, 5], [19, 57, 80], [60, 80, 71], [34, 7, 61], [36, 48, 51], [0, 0, 1], [0, 1]], ![[67, 41, 78], [9, 1, 79], [46, 78, 74], [31, 33, 46], [15, 14, 7], [40, 4, 41], [66, 41, 5]], ![[0, 1], [81, 25, 7], [20, 8, 21], [65, 43, 59], [57, 21, 25], [35, 79, 41], [67, 41, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 31], []]
 b := ![[], [11, 60, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [47, 9, 33, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10371846, -2868397, -1103319]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-124962, -34559, -13293]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [44, 18, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 54, 85], [73, 34, 4], [0, 1]]
 g := ![![[57, 33, 10], [76, 72], [21, 18], [23, 14, 42], [27, 57, 1], []], ![[2, 25, 72, 49], [62, 5], [78, 39], [49, 76, 71, 10], [44, 60, 87, 4], [35, 16]], ![[39, 47], [68, 81], [36, 50], [42, 55], [35, 86, 82, 5], [27, 16]]]
 h' := ![![[73, 54, 85], [29, 40, 30], [76, 2, 61], [56, 20, 75], [58, 32, 24], [0, 0, 1], [0, 1]], ![[73, 34, 4], [29, 12, 59], [40, 48, 19], [1, 71, 67], [58, 63, 65], [51, 53, 34], [73, 54, 85]], ![[0, 1], [87, 37], [63, 39, 9], [57, 87, 36], [51, 83], [47, 36, 54], [73, 34, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 48], []]
 b := ![[], [68, 43, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [44, 18, 32, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5240320, 1481405, 626471]
  a := ![4, 5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58880, 16645, 7039]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-20, 17, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-20, 17, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![77, 17, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-20, 17, 1], ![-90, 28, 150], ![-2294, -349, -89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -17, 97]], ![![-1, 0, 1], ![-120, -26, 150], ![47, 12, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [48, 36, 1] where
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
 g := ![![[25, 95], [91], [24], [3], [72], [61, 1]], ![[0, 2], [91], [24], [3], [72], [25, 96]]]
 h' := ![![[61, 96], [67, 80], [78, 24], [58, 11], [69, 10], [79, 84], [0, 1]], ![[0, 1], [0, 17], [87, 73], [50, 86], [0, 87], [62, 13], [61, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [20, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [48, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-619039, -472039, -309649]
  a := ![-65, -65, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![239422, 49402, -309649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![44, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![44, 1, 0]] 
 ![![97, 0, 0], ![44, 1, 0], ![89, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![44, 1, 0], ![3, 48, 9], ![-141, -20, 41]]]
  hmulB := by decide  
  f := ![![![1153, 24759, 4644], ![873, -50052, 0]], ![![526, 11228, 2106], ![389, -22698, 0]], ![![1057, 22717, 4261], ![803, -45924, 0]]]
  g := ![![![1, 0, 0], ![-44, 97, 0], ![-89, 0, 97]], ![![0, 1, 0], ![-30, 48, 9], ![-30, -20, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-20, 17, 1]] ![![97, 0, 0], ![44, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4268, 97, 0]], ![![-1940, 1649, 97], ![-970, 776, 194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![44, 1, 0]]], ![![![-20, 17, 1]], ![![-10, 8, 2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-37, 26, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-37, 26, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![64, 26, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-37, 26, 1], ![-63, 47, 231], ![-3563, -529, -133]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -26, 101]], ![![-1, 0, 1], ![-147, -59, 231], ![49, 29, -133]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [56, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 100], [0, 1]]
 g := ![![[5, 92], [58], [42, 71], [13], [14], [23, 1]], ![[0, 9], [58], [59, 30], [13], [14], [46, 100]]]
 h' := ![![[23, 100], [17, 30], [72, 19], [10, 77], [43, 35], [25, 69], [0, 1]], ![[0, 1], [0, 71], [4, 82], [64, 24], [40, 66], [97, 32], [23, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [62, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [56, 78, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5865, -9601, -8088]
  a := ![-6, -8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5067, 1987, -8088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-29, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-29, 1, 0]] 
 ![![101, 0, 0], ![72, 1, 0], ![32, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-29, 1, 0], ![3, -25, 9], ![-141, -20, -32]]]
  hmulB := by decide  
  f := ![![![6384, -58727, 21150], ![-2323, -237350, 0]], ![![4562, -41859, 15075], ![-1615, -169175, 0]], ![![2035, -18607, 6701], ![-693, -75200, 0]]]
  g := ![![![1, 0, 0], ![-72, 101, 0], ![-32, 0, 101]], ![![-1, 1, 0], ![15, -25, 9], ![23, -20, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-37, 26, 1]] ![![101, 0, 0], ![-29, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2929, 101, 0]], ![![-3737, 2626, 101], ![1010, -707, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-29, 1, 0]]], ![![![-37, 26, 1]], ![![10, -7, 2]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [59, 66, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 97, 5], [6, 5, 98], [0, 1]]
 g := ![![[17, 54, 16], [67, 43, 60], [99, 35, 17], [30, 93], [63, 59], [1]], ![[92, 75, 40, 39], [43, 63, 4, 80], [88, 36, 63, 53], [14, 56], [36, 33], [98, 24, 70, 22]], ![[53, 29, 66, 13], [0, 87, 89, 34], [18, 89, 80, 8], [24, 98], [24, 17], [17, 38, 61, 81]]]
 h' := ![![[27, 97, 5], [64, 18, 4], [30, 6, 36], [57, 73, 74], [73, 46, 89], [44, 37, 33], [0, 1]], ![[6, 5, 98], [86, 32, 7], [33, 91, 4], [36, 92, 14], [55, 58, 57], [99, 6, 41], [27, 97, 5]], ![[0, 1], [35, 53, 92], [69, 6, 63], [72, 41, 15], [56, 102, 60], [37, 60, 29], [6, 5, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 58], []]
 b := ![[], [15, 34, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [59, 66, 70, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10603850, -3089279, -1255467]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102950, -29993, -12189]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![15, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![15, 1, 0]] 
 ![![107, 0, 0], ![15, 1, 0], ![40, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![15, 1, 0], ![3, 19, 9], ![-141, -20, 12]]]
  hmulB := by decide  
  f := ![![![7141, 46536, 22050], ![1498, -262150, 0]], ![![999, 6515, 3087], ![215, -36701, 0]], ![![2660, 17396, 8243], ![628, -98000, 0]]]
  g := ![![![1, 0, 0], ![-15, 107, 0], ![-40, 0, 107]], ![![0, 1, 0], ![-6, 19, 9], ![-3, -20, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![19, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![19, 1, 0]] 
 ![![107, 0, 0], ![19, 1, 0], ![35, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![19, 1, 0], ![3, 23, 9], ![-141, -20, 16]]]
  hmulB := by decide  
  f := ![![![3736, 29937, 11718], ![963, -139314, 0]], ![![655, 5311, 2079], ![215, -24717, 0]], ![![1213, 9792, 3833], ![366, -45570, 0]]]
  g := ![![![1, 0, 0], ![-19, 107, 0], ![-35, 0, 107]], ![![0, 1, 0], ![-7, 23, 9], ![-3, -20, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-35, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-35, 1, 0]] 
 ![![107, 0, 0], ![72, 1, 0], ![70, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-35, 1, 0], ![3, -31, 9], ![-141, -20, -38]]]
  hmulB := by decide  
  f := ![![![886, -10227, 2970], ![-321, -35310, 0]], ![![597, -6880, 1998], ![-213, -23754, 0]], ![![595, -6691, 1943], ![-163, -23100, 0]]]
  g := ![![![1, 0, 0], ![-72, 107, 0], ![-70, 0, 107]], ![![-1, 1, 0], ![15, -31, 9], ![37, -20, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![15, 1, 0]] ![![107, 0, 0], ![19, 1, 0]]
  ![![107, 0, 0], ![32, 28, 1]] where
 M := ![![![11449, 0, 0], ![2033, 107, 0]], ![![1605, 107, 0], ![288, 38, 9]]]
 hmul := by decide  
 g := ![![![![75, -28, -1], ![107, 0, 0]], ![![-13, -27, -1], ![107, 0, 0]]], ![![![-17, -27, -1], ![107, 0, 0]], ![![0, -2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![32, 28, 1]] ![![107, 0, 0], ![-35, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3745, 107, 0]], ![![3424, 2996, 107], ![-1177, -856, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-35, 1, 0]]], ![![![32, 28, 1]], ![![-11, -8, 2]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [9, 25, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 92, 8], [106, 16, 101], [0, 1]]
 g := ![![[10, 100, 38], [95, 61], [78, 107, 15], [24, 97, 5], [26, 38], [1]], ![[60, 73, 76, 39], [41, 49], [14, 59, 78, 72], [65, 63, 63, 101], [0, 84], [95, 5, 23, 76]], ![[64, 31, 41, 96], [4, 28], [108, 107, 101, 11], [101, 25, 68, 107], [8, 61], [90, 24, 3, 33]]]
 h' := ![![[19, 92, 8], [32, 25, 16], [61, 34, 72], [2, 27, 48], [65, 3, 21], [100, 84, 16], [0, 1]], ![[106, 16, 101], [19, 10, 20], [37, 17, 7], [32, 83, 3], [81, 9, 33], [9, 97, 56], [19, 92, 8]], ![[0, 1], [35, 74, 73], [92, 58, 30], [46, 108, 58], [63, 97, 55], [35, 37, 37], [106, 16, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 49], []]
 b := ![[], [47, 44, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [9, 25, 93, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6255295161, 1543979659, 501338851]
  a := ![42, 62, 125]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57388029, 14164951, 4599439]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [38, 4, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 87, 9], [91, 25, 104], [0, 1]]
 g := ![![[24, 35, 8], [16, 85], [87, 82], [52, 50], [100, 21, 109], [1]], ![[31, 69, 52, 11], [58, 4], [49, 100], [106, 61], [10, 40, 75, 112], [104, 6, 62, 51]], ![[107, 85, 7, 32], [52, 87], [59, 85], [0, 81], [1, 23, 52, 25], [8, 15, 34, 62]]]
 h' := ![![[105, 87, 9], [48, 44, 102], [54, 33, 56], [14, 24, 46], [42, 20, 84], [75, 109, 83], [0, 1]], ![[91, 25, 104], [5, 66, 8], [66, 101, 2], [81, 79, 10], [70, 71, 20], [56, 14, 5], [105, 87, 9]], ![[0, 1], [33, 3, 3], [75, 92, 55], [31, 10, 57], [101, 22, 9], [9, 103, 25], [91, 25, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 7], []]
 b := ![[], [58, 83, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [38, 4, 30, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1216671, 250634, 51302]
  a := ![2, 4, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10767, 2218, 454]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![71, -55, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![71, -55, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![71, 72, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![71, -55, 1], ![-306, -169, -498], ![7858, 1091, 218]]]
  hmulB := by decide  
  f := ![![![-70, 55, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -72, 127]], ![![0, -1, 1], ![276, 281, -498], ![-60, -115, 218]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [98, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 126], [0, 1]]
 g := ![![[13, 35], [94, 87], [112, 115], [86, 99], [2, 120], [123, 1]], ![[0, 92], [0, 40], [33, 12], [71, 28], [30, 7], [119, 126]]]
 h' := ![![[123, 126], [59, 110], [73, 50], [81, 49], [58, 37], [11, 45], [0, 1]], ![[0, 1], [0, 17], [0, 77], [12, 78], [37, 90], [85, 82], [123, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [50, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [98, 4, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14563, -15040, -10383]
  a := ![8, 11, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5690, 5768, -10383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-10, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-10, 1, 0]] 
 ![![127, 0, 0], ![117, 1, 0], ![36, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-10, 1, 0], ![3, -6, 9], ![-141, -20, -13]]]
  hmulB := by decide  
  f := ![![![-2031, 4102, -6156], ![254, 86868, 0]], ![![-1869, 3778, -5670], ![255, 80010, 0]], ![![-568, 1162, -1745], ![170, 24624, 0]]]
  g := ![![![1, 0, 0], ![-117, 127, 0], ![-36, 0, 127]], ![![-1, 1, 0], ![3, -6, 9], ![21, -20, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![71, -55, 1]] ![![127, 0, 0], ![-10, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1270, 127, 0]], ![![9017, -6985, 127], ![-1016, 381, -508]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-10, 1, 0]]], ![![![71, -55, 1]], ![![-8, 3, -4]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [124, 10, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 4, 18], [60, 126, 113], [0, 1]]
 g := ![![[99], [68, 129, 20], [116, 64], [32, 20], [54, 44], [98, 1], []], ![[70, 85, 54, 51], [6, 109, 32, 67], [12, 15], [92, 101], [82, 125], [60, 25], [63, 62]], ![[24, 70, 3, 80], [67, 48, 119, 105], [18, 112], [53, 63], [0, 113], [49, 16], [99, 62]]]
 h' := ![![[38, 4, 18], [83, 19], [53, 121, 85], [17, 90, 123], [29, 95, 85], [31, 75, 31], [0, 0, 1], [0, 1]], ![[60, 126, 113], [19, 76, 80], [78, 101, 50], [16, 20, 88], [114, 128, 106], [8, 111, 16], [51, 108, 126], [38, 4, 18]], ![[0, 1], [44, 36, 51], [47, 40, 127], [24, 21, 51], [35, 39, 71], [64, 76, 84], [101, 23, 4], [60, 126, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 5], []]
 b := ![[], [58, 46, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [124, 10, 33, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3362901, -890800, -317675]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25671, -6800, -2425]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-1, 12, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-1, 12, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![136, 12, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-1, 12, 1], ![-105, 27, 105], ![-1589, -249, -55]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -12, 137]], ![![-1, 0, 1], ![-105, -9, 105], ![43, 3, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [56, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 136], [0, 1]]
 g := ![![[58, 115], [22], [120], [76, 49], [8], [93], [1]], ![[0, 22], [22], [120], [118, 88], [8], [93], [1]]]
 h' := ![![[40, 136], [134, 72], [74, 76], [128, 95], [115, 130], [120, 62], [81, 40], [0, 1]], ![[0, 1], [0, 65], [100, 61], [92, 42], [109, 7], [134, 75], [37, 97], [40, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [98, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [56, 97, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65352, -43256, -29726]
  a := ![-12, -20, -38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29032, 2288, -29726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![32, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![32, 1, 0]] 
 ![![137, 0, 0], ![32, 1, 0], ![55, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![32, 1, 0], ![3, 36, 9], ![-141, -20, 29]]]
  hmulB := by decide  
  f := ![![![-2777, -35634, -8910], ![-822, 135630, 0]], ![![-661, -8315, -2079], ![-136, 31647, 0]], ![![-1127, -14306, -3577], ![-278, 54450, 0]]]
  g := ![![![1, 0, 0], ![-32, 137, 0], ![-55, 0, 137]], ![![0, 1, 0], ![-12, 36, 9], ![-8, -20, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-1, 12, 1]] ![![137, 0, 0], ![32, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![4384, 137, 0]], ![![-137, 1644, 137], ![-137, 411, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![32, 1, 0]]], ![![![-1, 12, 1]], ![![-1, 3, 1]]]]
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


lemma PB253I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB253I2 : PrimesBelowBoundCertificateInterval O 79 137 253 where
  m := 11
  g := ![1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB253I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![16129, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I97N1, I101N1, I107N0, I107N1, I107N2, I127N1, I137N1]
  Il := ![[], [], [I97N1], [I101N1], [], [I107N0, I107N1, I107N2], [], [], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
