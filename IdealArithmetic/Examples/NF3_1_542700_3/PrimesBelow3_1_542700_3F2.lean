
import IdealArithmetic.Examples.NF3_1_542700_3.RI3_1_542700_3
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [38, 24, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 74, 34], [27, 8, 49], [0, 1]]
 g := ![![[45, 68, 75], [20, 43, 3], [69, 4], [4, 26], [7, 60, 1], []], ![[24, 7, 69, 72], [53, 23, 82, 52], [21, 59], [7, 29], [4, 13, 0, 18], [24, 77]], ![[61, 6, 40, 38], [39, 53, 73, 48], [21, 40], [65, 23], [8, 10, 66, 68], [9, 77]]]
 h' := ![![[33, 74, 34], [70, 77, 65], [45, 49, 13], [54, 61, 2], [66, 42, 21], [0, 0, 1], [0, 1]], ![[27, 8, 49], [6, 78, 67], [62, 12, 27], [14, 57, 15], [23, 9, 19], [11, 54, 8], [33, 74, 34]], ![[0, 1], [80, 11, 34], [8, 22, 43], [68, 48, 66], [31, 32, 43], [55, 29, 74], [27, 8, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 2], []]
 b := ![[], [51, 19, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [38, 24, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1328, -3818, -1079]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, -46, -13]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [81, 76, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 83, 72], [44, 5, 17], [0, 1]]
 g := ![![[5, 85, 18], [65, 81], [14, 88], [9, 51, 44], [38, 84, 1], []], ![[29, 47, 85, 50], [11, 21], [16, 55], [73, 15, 41, 40], [78, 36, 63, 20], [5, 22]], ![[55, 22], [72, 42], [0, 69], [63, 13, 58, 1], [36, 82, 73, 78], [60, 22]]]
 h' := ![![[40, 83, 72], [53, 16, 75], [45, 36, 9], [72, 25, 34], [37, 9, 20], [0, 0, 1], [0, 1]], ![[44, 5, 17], [72, 46, 14], [47, 36, 56], [50, 1, 12], [0, 61, 36], [38, 28, 5], [40, 83, 72]], ![[0, 1], [41, 27], [55, 17, 24], [12, 63, 43], [70, 19, 33], [13, 61, 83], [44, 5, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 30], []]
 b := ![[], [32, 16, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [81, 76, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16109, -49662, 18067]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![181, -558, 203]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![15, 26, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![15, 26, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![15, 26, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![15, 26, 1], ![10, -15, 130], ![260, -778, -15]]]
  hmulB := by decide  
  f := ![![![-14, -26, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -26, 97]], ![![0, 0, 1], ![-20, -35, 130], ![5, -4, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [49, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 96], [0, 1]]
 g := ![![[38, 2], [61], [48], [94], [53], [78, 1]], ![[0, 95], [61], [48], [94], [53], [59, 96]]]
 h' := ![![[78, 96], [72, 14], [65, 62], [34, 40], [88, 71], [58, 21], [0, 1]], ![[0, 1], [0, 83], [51, 35], [50, 57], [0, 26], [47, 76], [78, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [4, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [49, 19, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2909, -47, 84]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, -23, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-33, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-33, 1, 0]] 
 ![![97, 0, 0], ![64, 1, 0], ![15, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-33, 1, 0], ![0, -33, 5], ![10, -30, -33]]]
  hmulB := by decide  
  f := ![![![2179, -66, 0], ![6402, 0, 0]], ![![1420, -43, 0], ![4172, 0, 0]], ![![339, 3, -2], ![996, 39, 0]]]
  g := ![![![1, 0, 0], ![-64, 97, 0], ![-15, 0, 97]], ![![-1, 1, 0], ![21, -33, 5], ![25, -30, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![15, 26, 1]] ![![97, 0, 0], ![-33, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3201, 97, 0]], ![![1455, 2522, 97], ![-485, -873, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-33, 1, 0]]], ![![![15, 26, 1]], ![![-5, -9, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -1, -5]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-151, -1, -5]] 
 ![![101, 0, 0], ![0, 101, 0], ![10, 81, 1]] where
  M :=![![![-151, -1, -5], ![-50, -1, -5], ![-10, 20, -1]]]
  hmulB := by decide  
  f := ![![![-1, 1, 0]], ![![0, -1, 5]], ![![0, -1, 4]]]
  g := ![![![-1, 4, -5], ![0, 4, -5], ![0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [90, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 100], [0, 1]]
 g := ![![[11, 45], [19], [17, 1], [97], [49], [20, 1]], ![[2, 56], [19], [37, 100], [97], [49], [40, 100]]]
 h' := ![![[20, 100], [30, 34], [86, 25], [52, 100], [55, 20], [18, 7], [0, 1]], ![[0, 1], [3, 67], [81, 76], [32, 1], [51, 81], [57, 94], [20, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [51, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [90, 81, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, 281, -514]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52, 415, -514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![101, 0, 0], ![100, 1, 0], ![20, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 5], ![10, -30, -1]]]
  hmulB := by decide  
  f := ![![![-151, -1, -5]], ![![-150, -1, -5]], ![![-30, 0, -1]]]
  g := ![![![-1, 1, 0], ![0, -1, 5], ![30, -30, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-151, -1, -5]] ![![-1, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [61, 93, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 83, 78], [30, 19, 25], [0, 1]]
 g := ![![[89, 62, 58], [78, 55, 13], [60, 86, 19], [84, 97], [76, 98], [1]], ![[54, 89, 42, 3], [58, 54, 48, 40], [40, 73, 86, 12], [42, 17], [43, 30], [52, 72, 101, 31]], ![[23, 40, 49, 30], [89, 15, 98, 97], [92, 0, 31, 38], [66, 13], [90, 14], [39, 93, 84, 72]]]
 h' := ![![[30, 83, 78], [83, 38, 77], [48, 49, 42], [67, 61, 15], [12, 51, 71], [42, 10, 60], [0, 1]], ![[30, 19, 25], [96, 88, 101], [98, 35, 88], [95, 18, 99], [44, 95, 74], [35, 14, 66], [30, 83, 78]], ![[0, 1], [3, 80, 28], [66, 19, 76], [10, 24, 92], [88, 60, 61], [4, 79, 80], [30, 19, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 29], []]
 b := ![[], [9, 68, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [61, 93, 43, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1751, -5047, -1648]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, -49, -16]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [85, 7, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 82, 23], [58, 24, 84], [0, 1]]
 g := ![![[58, 49, 76], [70, 64, 92], [48, 44], [74, 49, 99], [73, 39], [1]], ![[29, 26, 99, 102], [96, 12, 96, 69], [65, 29], [35, 85, 105, 61], [81, 105], [14, 42, 77, 76]], ![[96, 24, 37, 24], [6, 73, 98, 106], [9, 90], [49, 34, 13, 93], [94, 40], [45, 22, 48, 31]]]
 h' := ![![[99, 82, 23], [42, 34, 66], [87, 45, 78], [23, 64, 30], [57, 39, 62], [22, 100, 50], [0, 1]], ![[58, 24, 84], [74, 12, 12], [96, 98, 18], [48, 105, 52], [63, 52, 31], [10, 92, 76], [99, 82, 23]], ![[0, 1], [43, 61, 29], [105, 71, 11], [96, 45, 25], [20, 16, 14], [78, 22, 88], [58, 24, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 43], []]
 b := ![[], [8, 24, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [85, 7, 57, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![348820, -1032764, -54356]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3260, -9652, -508]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![4, -54, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![4, -54, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![4, 55, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![4, -54, 1], ![10, -26, -270], ![-540, 1622, -26]]]
  hmulB := by decide  
  f := ![![![-3, 54, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -55, 109]], ![![0, -1, 1], ![10, 136, -270], ![-4, 28, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [37, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 108], [0, 1]]
 g := ![![[45, 16], [64], [52, 28], [54, 83], [81], [79, 1]], ![[1, 93], [64], [84, 81], [71, 26], [81], [49, 108]]]
 h' := ![![[79, 108], [57, 105], [38, 8], [73, 30], [19, 44], [20, 100], [0, 1]], ![[0, 1], [68, 4], [16, 101], [45, 79], [7, 65], [72, 9], [79, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [82, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [37, 30, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52, 266, -13]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, 9, -13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![52, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![52, 1, 0]] 
 ![![109, 0, 0], ![52, 1, 0], ![26, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![52, 1, 0], ![0, 52, 5], ![10, -30, 52]]]
  hmulB := by decide  
  f := ![![![1717, 33, 0], ![-3597, 0, 0]], ![![780, 15, 0], ![-1634, 0, 0]], ![![338, -4, -1], ![-708, 22, 0]]]
  g := ![![![1, 0, 0], ![-52, 109, 0], ![-26, 0, 109]], ![![0, 1, 0], ![-26, 52, 5], ![2, -30, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![4, -54, 1]] ![![109, 0, 0], ![52, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5668, 109, 0]], ![![436, -5886, 109], ![218, -2834, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![52, 1, 0]]], ![![![4, -54, 1]], ![![2, -26, -2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![69, -36, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![69, -36, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![69, 77, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![69, -36, 1], ![10, 39, -180], ![-360, 1082, 39]]]
  hmulB := by decide  
  f := ![![![-68, 36, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -77, 113]], ![![0, -1, 1], ![110, 123, -180], ![-27, -17, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [46, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 112], [0, 1]]
 g := ![![[79, 15], [104], [102], [91], [37, 105], [95, 1]], ![[35, 98], [104], [102], [91], [68, 8], [77, 112]]]
 h' := ![![[95, 112], [90, 44], [69, 45], [44, 92], [106, 54], [37, 52], [0, 1]], ![[0, 1], [89, 69], [50, 68], [83, 21], [38, 59], [5, 61], [95, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [37, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [46, 18, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86, -94, -79]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 53, -79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-46, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-46, 1, 0]] 
 ![![113, 0, 0], ![67, 1, 0], ![74, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-46, 1, 0], ![0, -46, 5], ![10, -30, -46]]]
  hmulB := by decide  
  f := ![![![4693, -102, 0], ![11526, 0, 0]], ![![2807, -61, 0], ![6894, 0, 0]], ![![3114, -40, -3], ![7648, 68, 0]]]
  g := ![![![1, 0, 0], ![-67, 113, 0], ![-74, 0, 113]], ![![-1, 1, 0], ![24, -46, 5], ![48, -30, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![69, -36, 1]] ![![113, 0, 0], ![-46, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5198, 113, 0]], ![![7797, -4068, 113], ![-3164, 1695, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-46, 1, 0]]], ![![![69, -36, 1]], ![![-28, 15, -2]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [36, 63, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 5, 24], [78, 121, 103], [0, 1]]
 g := ![![[90, 39, 62], [96, 45, 16], [117, 123, 17], [121, 43, 1], [34, 51, 42], [1]], ![[90, 104, 12, 40], [33, 69, 87, 92], [3, 67, 119, 53], [51, 24, 58, 97], [116, 3, 45, 23], [64, 40, 11, 108]], ![[86, 102, 99, 31], [56, 11, 43, 103], [32, 4, 7, 50], [118, 119, 7, 32], [1, 14, 22, 21], [6, 57, 39, 19]]]
 h' := ![![[62, 5, 24], [100, 12, 58], [106, 59, 4], [89, 57, 115], [46, 112, 126], [91, 64, 13], [0, 1]], ![[78, 121, 103], [70, 38, 67], [32, 57, 122], [87, 110, 43], [49, 48, 27], [58, 118, 61], [62, 5, 24]], ![[0, 1], [113, 77, 2], [103, 11, 1], [62, 87, 96], [59, 94, 101], [118, 72, 53], [78, 121, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 88], []]
 b := ![[], [38, 122, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [36, 63, 114, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61214, 186690, -37338]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-482, 1470, -294]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-64, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-64, 1, 0]] 
 ![![131, 0, 0], ![67, 1, 0], ![124, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-64, 1, 0], ![0, -64, 5], ![10, -30, -64]]]
  hmulB := by decide  
  f := ![![![4289, -67, 0], ![8777, 0, 0]], ![![2177, -34, 0], ![4455, 0, 0]], ![![4052, -12, -4], ![8292, 105, 0]]]
  g := ![![![1, 0, 0], ![-67, 131, 0], ![-124, 0, 131]], ![![-1, 1, 0], ![28, -64, 5], ![76, -30, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-38, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-38, 1, 0]] 
 ![![131, 0, 0], ![93, 1, 0], ![78, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-38, 1, 0], ![0, -38, 5], ![10, -30, -38]]]
  hmulB := by decide  
  f := ![![![4333, -114, 0], ![14934, 0, 0]], ![![3079, -81, 0], ![10612, 0, 0]], ![![2602, -38, -4], ![8968, 105, 0]]]
  g := ![![![1, 0, 0], ![-93, 131, 0], ![-78, 0, 131]], ![![-1, 1, 0], ![24, -38, 5], ![44, -30, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-29, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-29, 1, 0]] 
 ![![131, 0, 0], ![102, 1, 0], ![120, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-29, 1, 0], ![0, -29, 5], ![10, -30, -29]]]
  hmulB := by decide  
  f := ![![![3655, -126, 0], ![16506, 0, 0]], ![![2872, -99, 0], ![12970, 0, 0]], ![![3372, -93, -4], ![15228, 105, 0]]]
  g := ![![![1, 0, 0], ![-102, 131, 0], ![-120, 0, 131]], ![![-1, 1, 0], ![18, -29, 5], ![50, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-64, 1, 0]] ![![131, 0, 0], ![-38, 1, 0]]
  ![![131, 0, 0], ![41, 32, 1]] where
 M := ![![![17161, 0, 0], ![-4978, 131, 0]], ![![-8384, 131, 0], ![2432, -102, 5]]]
 hmul := by decide  
 g := ![![![![90, -32, -1], ![131, 0, 0]], ![![-38, 1, 0], ![0, 0, 0]]], ![![![-64, 1, 0], ![0, 0, 0]], ![![17, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![41, 32, 1]] ![![131, 0, 0], ![-29, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3799, 131, 0]], ![![5371, 4192, 131], ![-1179, -917, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-29, 1, 0]]], ![![![41, 32, 1]], ![![-9, -7, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![87, -11, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![87, -11, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![87, 126, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![87, -11, 1], ![10, 57, -55], ![-110, 332, 57]]]
  hmulB := by decide  
  f := ![![![-86, 11, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -126, 137]], ![![0, -1, 1], ![35, 51, -55], ![-37, -50, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [56, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 136], [0, 1]]
 g := ![![[76, 115], [17], [37], [50, 118], [25], [81], [1]], ![[0, 22], [17], [37], [84, 19], [25], [81], [1]]]
 h' := ![![[128, 136], [37, 65], [21, 90], [77, 41], [48, 23], [107, 5], [81, 128], [0, 1]], ![[0, 1], [0, 72], [33, 47], [119, 96], [115, 114], [62, 132], [25, 9], [128, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [70, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [56, 9, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![322, 27, 10]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -9, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![55, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![55, 1, 0]] 
 ![![137, 0, 0], ![55, 1, 0], ![80, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![55, 1, 0], ![0, 55, 5], ![10, -30, 55]]]
  hmulB := by decide  
  f := ![![![166, 3, 0], ![-411, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![60, -21, -2], ![-148, 55, 0]]]
  g := ![![![1, 0, 0], ![-55, 137, 0], ![-80, 0, 137]], ![![0, 1, 0], ![-25, 55, 5], ![-20, -30, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![87, -11, 1]] ![![137, 0, 0], ![55, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7535, 137, 0]], ![![11919, -1507, 137], ![4795, -548, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![55, 1, 0]]], ![![![87, -11, 1]], ![![35, -4, 0]]]]
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


lemma PB209I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB209I2 : PrimesBelowBoundCertificateInterval O 79 137 209 where
  m := 11
  g := ![1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB209I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
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
      exact NI137N1
  β := ![I97N1, I101N1, I109N1, I113N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[], [], [I97N1], [I101N1], [], [], [I109N1], [I113N1], [], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
