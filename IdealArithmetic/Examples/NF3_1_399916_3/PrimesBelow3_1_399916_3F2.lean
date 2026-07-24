
import IdealArithmetic.Examples.NF3_1_399916_3.RI3_1_399916_3
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [30, 29, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 49, 26], [66, 33, 57], [0, 1]]
 g := ![![[30, 43, 29], [32, 67, 44], [46, 28], [74, 37], [70, 79, 1], []], ![[8, 47, 58, 40], [55, 37, 82, 28], [72, 51], [13, 41], [64, 37, 32, 11], [10, 12]], ![[76, 45, 74, 73], [67, 47, 42, 5], [47, 59], [40, 75], [74, 25, 12, 73], [62, 12]]]
 h' := ![![[13, 49, 26], [36, 81, 64], [23, 30, 58], [65, 31, 32], [58, 82, 55], [0, 0, 1], [0, 1]], ![[66, 33, 57], [9, 81, 68], [36, 63, 38], [11, 73, 36], [61, 75, 46], [35, 43, 33], [13, 49, 26]], ![[0, 1], [39, 4, 34], [27, 73, 70], [62, 62, 15], [73, 9, 65], [6, 40, 49], [66, 33, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 22], []]
 b := ![[], [13, 81, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [30, 29, 4, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60507, -1245, -2490]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-729, -15, -30]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [9, 76, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 39, 10], [76, 49, 79], [0, 1]]
 g := ![![[8, 36, 53], [37, 39], [47, 67], [19, 56, 5], [29, 4, 1], []], ![[37, 72, 16, 10], [40, 80], [73, 25], [19, 42, 51, 88], [56, 32, 33, 69], [23, 11]], ![[46, 14, 19, 8], [78, 81], [61, 87], [35, 26, 68, 84], [84, 37, 66, 9], [43, 11]]]
 h' := ![![[17, 39, 10], [80, 65, 63], [71, 29, 67], [7, 46, 45], [6, 74, 70], [0, 0, 1], [0, 1]], ![[76, 49, 79], [32, 61, 88], [6, 44, 13], [29, 65, 84], [62, 58, 76], [82, 13, 49], [17, 39, 10]], ![[0, 1], [8, 52, 27], [40, 16, 9], [12, 67, 49], [71, 46, 32], [49, 76, 39], [76, 49, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 75], []]
 b := ![[], [70, 46, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [9, 76, 85, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![844076, 136081, -1958]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9484, 1529, -22]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![15, -3, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![15, -3, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![15, 94, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![15, -3, 1], ![119, 15, -5], ![-305, 61, 12]]]
  hmulB := by decide  
  f := ![![![-14, 3, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -94, 97]], ![![0, -1, 1], ![2, 5, -5], ![-5, -11, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [89, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 96], [0, 1]]
 g := ![![[35, 12], [49], [72], [33], [54], [86, 1]], ![[0, 85], [49], [72], [33], [54], [75, 96]]]
 h' := ![![[86, 96], [26, 20], [64, 90], [78, 84], [28, 79], [9, 32], [0, 1]], ![[0, 1], [0, 77], [44, 7], [27, 13], [32, 18], [45, 65], [86, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [5, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [89, 11, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![253212, 265597, 7724]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1416, -4747, 7724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![5, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![5, 1, 0]] 
 ![![97, 0, 0], ![5, 1, 0], ![85, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![5, 1, 0], ![1, 5, 2], ![122, 0, 6]]]
  hmulB := by decide  
  f := ![![![-779, -3900, -1560], ![0, 75660, 0]], ![![-40, -200, -80], ![1, 3880, 0]], ![![-680, -3417, -1367], ![-51, 66300, 0]]]
  g := ![![![1, 0, 0], ![-5, 97, 0], ![-85, 0, 97]], ![![0, 1, 0], ![-2, 5, 2], ![-4, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![15, -3, 1]] ![![97, 0, 0], ![5, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![485, 97, 0]], ![![1455, -291, 97], ![194, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![5, 1, 0]]], ![![![15, -3, 1]], ![![2, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-6, 29, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-6, 29, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![95, 29, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-6, 29, 1], ![151, -6, 59], ![3599, 61, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -29, 101]], ![![-1, 0, 1], ![-54, -17, 59], ![14, -6, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [43, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 100], [0, 1]]
 g := ![![[34, 47], [9], [24, 84], [68], [6], [53, 1]], ![[0, 54], [9], [32, 17], [68], [6], [5, 100]]]
 h' := ![![[53, 100], [97, 42], [79, 3], [11, 65], [62, 13], [44, 39], [0, 1]], ![[0, 1], [0, 59], [36, 98], [22, 36], [44, 88], [91, 62], [53, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [14, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [43, 48, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![257, 1569, -228]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![217, 81, -228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![42, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![42, 1, 0]] 
 ![![101, 0, 0], ![42, 1, 0], ![78, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![42, 1, 0], ![1, 42, 2], ![122, 0, 43]]]
  hmulB := by decide  
  f := ![![![-2734, -160708, -7654], ![-2626, 386527, 0]], ![![-1129, -66811, -3182], ![-1110, 160691, 0]], ![![-2106, -124111, -5911], ![-2041, 298506, 0]]]
  g := ![![![1, 0, 0], ![-42, 101, 0], ![-78, 0, 101]], ![![0, 1, 0], ![-19, 42, 2], ![-32, 0, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-6, 29, 1]] ![![101, 0, 0], ![42, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4242, 101, 0]], ![![-606, 2929, 101], ![-101, 1212, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![42, 1, 0]]], ![![![-6, 29, 1]], ![![-1, 12, 1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [67, 20, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 78, 62], [84, 24, 41], [0, 1]]
 g := ![![[9, 68, 29], [18, 98, 36], [83, 1, 16], [24, 58], [96, 16], [1]], ![[39, 66, 23, 39], [45, 30, 63, 47], [62, 63, 28, 37], [35, 58], [100, 9], [90, 74, 53, 89]], ![[98, 88, 77, 32], [64, 44, 0, 19], [52, 16, 79, 92], [15, 26], [25, 1], [48, 79, 54, 14]]]
 h' := ![![[15, 78, 62], [30, 79, 82], [1, 100, 97], [30, 82, 99], [14, 100, 26], [36, 83, 99], [0, 1]], ![[84, 24, 41], [18, 51, 68], [26, 80, 82], [2, 82, 44], [9, 19, 26], [23, 57, 3], [15, 78, 62]], ![[0, 1], [24, 76, 56], [29, 26, 27], [32, 42, 63], [25, 87, 51], [19, 66, 1], [84, 24, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 42], []]
 b := ![[], [10, 47, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [67, 20, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60461, -1236, -2472]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-587, -12, -24]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![26, -17, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![26, -17, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![26, 90, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![26, -17, 1], ![105, 26, -33], ![-2013, 61, 9]]]
  hmulB := by decide  
  f := ![![![-25, 17, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -90, 107]], ![![0, -1, 1], ![9, 28, -33], ![-21, -7, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [3, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 106], [0, 1]]
 g := ![![[42, 36], [69, 105], [27], [18, 48], [85], [88, 1]], ![[0, 71], [0, 2], [27], [69, 59], [85], [69, 106]]]
 h' := ![![[88, 106], [7, 6], [53, 76], [53, 53], [105, 35], [57, 37], [0, 1]], ![[0, 1], [0, 101], [0, 31], [9, 54], [82, 72], [103, 70], [88, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [49, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [3, 19, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14863, 986, 905]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81, -752, 905]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![33, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![33, 1, 0]] 
 ![![107, 0, 0], ![33, 1, 0], ![98, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![33, 1, 0], ![1, 33, 2], ![122, 0, 34]]]
  hmulB := by decide  
  f := ![![![953, 39032, 2366], ![749, -126581, 0]], ![![298, 12010, 728], ![215, -38948, 0]], ![![875, 35749, 2167], ![679, -115934, 0]]]
  g := ![![![1, 0, 0], ![-33, 107, 0], ![-98, 0, 107]], ![![0, 1, 0], ![-12, 33, 2], ![-30, 0, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![26, -17, 1]] ![![107, 0, 0], ![33, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![3531, 107, 0]], ![![2782, -1819, 107], ![963, -535, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![33, 1, 0]]], ![![![26, -17, 1]], ![![9, -5, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [36, 7, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 59, 83], [55, 49, 26], [0, 1]]
 g := ![![[44, 47, 83], [81, 25], [95, 57, 78], [60, 70, 15], [15, 9], [1]], ![[96, 53, 93, 1], [93, 64], [5, 92, 44, 38], [74, 90, 38, 28], [81, 26], [80, 24, 51, 82]], ![[11, 62, 6, 29], [98, 9], [78, 32, 81, 94], [15, 63, 44, 82], [76, 43], [22, 102, 101, 27]]]
 h' := ![![[51, 59, 83], [73, 66, 65], [68, 81, 5], [20, 52, 29], [102, 75, 48], [73, 102, 106], [0, 1]], ![[55, 49, 26], [106, 48, 52], [27, 98, 101], [100, 29, 69], [42, 79, 75], [61, 63, 35], [51, 59, 83]], ![[0, 1], [62, 104, 101], [59, 39, 3], [75, 28, 11], [24, 64, 95], [12, 53, 77], [55, 49, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 98], []]
 b := ![[], [99, 3, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [36, 7, 3, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-194347, -6540, 6540]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1783, -60, 60]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [78, 102, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 4, 66], [107, 108, 47], [0, 1]]
 g := ![![[94, 94, 64], [74, 63], [110, 22], [5, 83], [109, 45, 49], [1]], ![[40, 103, 20, 29], [88, 72], [47, 49], [8, 81], [11, 4, 33, 80], [98, 30, 8, 24]], ![[69, 27, 20, 45], [55, 30], [94, 111], [17, 77], [62, 4, 111, 42], [22, 109, 32, 89]]]
 h' := ![![[13, 4, 66], [55, 8, 105], [8, 59, 17], [0, 19, 94], [86, 44, 14], [35, 11, 7], [0, 1]], ![[107, 108, 47], [82, 14, 3], [77, 20, 80], [50, 5, 106], [30, 38, 9], [90, 88, 13], [13, 4, 66]], ![[0, 1], [81, 91, 5], [90, 34, 16], [90, 89, 26], [88, 31, 90], [102, 14, 93], [107, 108, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 49], []]
 b := ![[], [69, 49, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [78, 102, 106, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![700374, 114243, 16950]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6198, 1011, 150]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![46, 12, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![46, 12, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![46, 12, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![46, 12, 1], ![134, 46, 25], ![1525, 61, 58]]]
  hmulB := by decide  
  f := ![![![-45, -12, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -12, 127]], ![![0, 0, 1], ![-8, -2, 25], ![-9, -5, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [123, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 126], [0, 1]]
 g := ![![[70, 26], [100, 69], [31, 88], [99, 17], [34, 120], [26, 1]], ![[111, 101], [116, 58], [33, 39], [33, 110], [106, 7], [52, 126]]]
 h' := ![![[26, 126], [19, 91], [124, 113], [15, 56], [9, 115], [104, 45], [0, 1]], ![[0, 1], [99, 36], [14, 14], [74, 71], [78, 12], [4, 82], [26, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [123, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [123, 101, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1168, 1525, -455]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![174, 55, -455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-25, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-25, 1, 0]] 
 ![![127, 0, 0], ![102, 1, 0], ![69, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-25, 1, 0], ![1, -25, 2], ![122, 0, -24]]]
  hmulB := by decide  
  f := ![![![-4071, 110536, -8844], ![1778, 561594, 0]], ![![-3275, 88764, -7102], ![1398, 450977, 0]], ![![-2212, 60055, -4805], ![965, 305118, 0]]]
  g := ![![![1, 0, 0], ![-102, 127, 0], ![-69, 0, 127]], ![![-1, 1, 0], ![19, -25, 2], ![14, 0, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![46, 12, 1]] ![![127, 0, 0], ![-25, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3175, 127, 0]], ![![5842, 1524, 127], ![-1016, -254, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-25, 1, 0]]], ![![![46, 12, 1]], ![![-8, -2, 0]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [4, 13, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 47, 110], [12, 83, 21], [0, 1]]
 g := ![![[68, 66, 58], [130, 78, 77], [115, 62], [111, 20], [47, 81], [2, 1], []], ![[36, 118, 14, 90], [104, 79, 43, 85], [43, 28], [91, 74], [114, 65], [73, 77], [87, 48]], ![[60, 102, 128, 46], [5, 4, 62, 74], [9, 91], [66, 89], [25, 25], [73, 113], [45, 48]]]
 h' := ![![[121, 47, 110], [4, 2, 53], [68, 92, 48], [129, 98, 18], [7, 69, 85], [123, 101, 122], [0, 0, 1], [0, 1]], ![[12, 83, 21], [71, 20, 34], [82, 107, 87], [56, 28, 91], [114, 52, 104], [35, 93, 14], [14, 95, 83], [121, 47, 110]], ![[0, 1], [85, 109, 44], [99, 63, 127], [2, 5, 22], [2, 10, 73], [87, 68, 126], [95, 36, 47], [12, 83, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 94], []]
 b := ![[], [112, 82, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [4, 13, 129, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-221128, 451426, -87770]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1688, 3446, -670]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143, -22, -8]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-143, -22, -8]] 
 ![![137, 0, 0], ![0, 137, 0], ![35, 37, 1]] where
  M :=![![![-143, -22, -8], ![-998, -143, -52], ![-3172, -488, -165]]]
  hmulB := by decide  
  f := ![![![13, -2, 0]], ![![-2, 13, -4]], ![![1, 3, -1]]]
  g := ![![![1, 2, -8], ![6, 13, -52], ![19, 41, -165]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [15, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 136], [0, 1]]
 g := ![![[120, 64], [36], [44], [45, 11], [32], [87], [1]], ![[0, 73], [36], [44], [110, 126], [32], [87], [1]]]
 h' := ![![[118, 136], [15, 8], [125, 131], [10, 110], [50, 82], [16, 13], [122, 118], [0, 1]], ![[0, 1], [0, 129], [102, 6], [112, 27], [136, 55], [43, 124], [72, 19], [118, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [116, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [15, 19, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10543, 13678, 677]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -83, 677]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -2, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![13, -2, 0]] 
 ![![137, 0, 0], ![62, 1, 0], ![65, 0, 1]] where
  M :=![![![13, -2, 0], ![-2, 13, -4], ![-244, 0, 11]]]
  hmulB := by decide  
  f := ![![![-143, -22, -8]], ![![-72, -11, -4]], ![![-91, -14, -5]]]
  g := ![![![1, -2, 0], ![-4, 13, -4], ![-7, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-143, -22, -8]] ![![13, -2, 0]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB179I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB179I2 : PrimesBelowBoundCertificateInterval O 79 137 179 where
  m := 11
  g := ![1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB179I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
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
    · exact ![11449, 107]
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
  β := ![I97N1, I101N1, I107N1, I127N1, I137N1]
  Il := ![[], [], [I97N1], [I101N1], [], [I107N1], [], [], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
