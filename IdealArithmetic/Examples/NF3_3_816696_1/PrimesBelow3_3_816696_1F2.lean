
import IdealArithmetic.Examples.NF3_3_816696_1.RI3_3_816696_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [61, 17, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 52, 72], [53, 30, 11], [0, 1]]
 g := ![![[50, 26, 61], [26, 62, 51], [0, 61], [76, 30], [64, 74, 1], []], ![[59, 13, 28, 62], [51, 34, 68, 55], [38, 59], [79, 21], [67, 23, 28, 60], [8, 38]], ![[46, 61, 73, 12], [69, 62, 57, 9], [2, 65], [39, 37], [58, 7, 45, 30], [69, 38]]]
 h' := ![![[21, 52, 72], [74, 21, 71], [26, 70, 47], [21, 29, 71], [80, 42, 14], [0, 0, 1], [0, 1]], ![[53, 30, 11], [0, 16, 73], [34, 80, 59], [32, 17, 68], [55, 64, 41], [36, 62, 30], [21, 52, 72]], ![[0, 1], [59, 46, 22], [20, 16, 60], [15, 37, 27], [53, 60, 28], [11, 21, 52], [53, 30, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 50], []]
 b := ![[], [14, 80, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [61, 17, 9, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108398, -85158, -49551]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1306, -1026, -597]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [82, 41, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 32, 76], [4, 56, 13], [0, 1]]
 g := ![![[34, 16, 81], [28, 21], [23, 36], [24, 50, 87], [50, 64, 1], []], ![[10, 17, 78, 59], [72, 57], [59, 32], [72, 34, 75, 12], [24, 59, 7, 83], [16, 80]], ![[6, 81, 45, 61], [66, 47], [66, 22], [23, 73, 18, 76], [40, 79, 80, 51], [79, 80]]]
 h' := ![![[60, 32, 76], [54, 30, 80], [83, 55, 56], [79, 25, 6], [83, 0, 49], [0, 0, 1], [0, 1]], ![[4, 56, 13], [41, 16, 85], [58, 49, 18], [88, 35, 11], [55, 27, 74], [63, 6, 56], [60, 32, 76]], ![[0, 1], [37, 43, 13], [38, 74, 15], [33, 29, 72], [18, 62, 55], [35, 83, 32], [4, 56, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 4], []]
 b := ![[], [43, 88, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [82, 41, 25, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-905041, -108491, 998224]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10169, -1219, 11216]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [13, 81, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 0, 27], [26, 96, 70], [0, 1]]
 g := ![![[92, 76, 27], [8, 94], [11, 70], [20, 32], [77, 36], [1]], ![[32, 74, 38, 31], [24, 12], [51, 81], [31, 6], [68, 75], [61, 22, 48, 89]], ![[73, 2, 96, 50], [23, 36], [3, 8], [8, 72], [72, 93], [5, 91, 93, 8]]]
 h' := ![![[65, 0, 27], [96, 46, 30], [43, 11, 26], [63, 19, 19], [41, 57, 41], [84, 16, 91], [0, 1]], ![[26, 96, 70], [68, 42, 48], [63, 17, 77], [85, 46, 9], [87, 38, 43], [1, 11, 50], [65, 0, 27]], ![[0, 1], [45, 9, 19], [76, 69, 91], [55, 32, 69], [16, 2, 13], [51, 70, 53], [26, 96, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 15], []]
 b := ![[], [70, 35, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [13, 81, 6, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1163906880, -942122394, -597711381]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11999040, -9712602, -6161973]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23942, -508, 565]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-23942, -508, 565]] 
 ![![101, 0, 0], ![0, 101, 0], ![42, 5, 1]] where
  M :=![![![-23942, -508, 565], ![40623, 861, -959], ![-17423, -374, 410]]]
  hmulB := by decide  
  f := ![![![-56, -30, 7]], ![![527, 275, -83]], ![![-16, -9, 1]]]
  g := ![![![-472, -33, 565], ![801, 56, -959], ![-343, -24, 410]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [28, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 100], [0, 1]]
 g := ![![[37, 30], [21], [52, 76], [56], [47], [75, 1]], ![[65, 71], [21], [96, 25], [56], [47], [49, 100]]]
 h' := ![![[75, 100], [65, 63], [59, 18], [93, 50], [34, 37], [21, 42], [0, 1]], ![[0, 1], [43, 38], [96, 83], [5, 51], [82, 64], [40, 59], [75, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [92, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [28, 26, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2333, -208, 2544]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1081, -128, 2544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56, 30, -7]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![56, 30, -7]] 
 ![![101, 0, 0], ![85, 1, 0], ![10, 0, 1]] where
  M :=![![![56, 30, -7], ![-527, -275, 83], ![1899, 1024, -222]]]
  hmulB := by decide  
  f := ![![![23942, 508, -565]], ![![19747, 419, -466]], ![![2543, 54, -60]]]
  g := ![![![-24, 30, -7], ![218, -275, 83], ![-821, 1024, -222]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-23942, -508, 565]] ![![56, 30, -7]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6170, -4108, -1109]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-6170, -4108, -1109]] 
 ![![103, 0, 0], ![44, 1, 0], ![90, 0, 1]] where
  M :=![![![-6170, -4108, -1109], ![-74631, -49749, -13433], ![-328265, -218786, -59074]]]
  hmulB := by decide  
  f := ![![![-79912, -42318, 11123]], ![![-26059, -13799, 3627]], ![![-95433, -50540, 13284]]]
  g := ![![![2664, -4108, -1109], ![32265, -49749, -13433], ![141893, -218786, -59074]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1163, 634, -166]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1163, 634, -166]] 
 ![![103, 0, 0], ![77, 1, 0], ![6, 0, 1]] where
  M :=![![![1163, 634, -166], ![-12420, -6609, 1736], ![39536, 20954, -5507]]]
  hmulB := by decide  
  f := ![![![-19619, -13074, -3530]], ![![-16973, -11311, -3054]], ![![-11286, -7522, -2031]]]
  g := ![![![-453, 634, -166], ![4719, -6609, 1736], ![-14960, 20954, -5507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 4, -1]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![8, 4, -1]] 
 ![![103, 0, 0], ![85, 1, 0], ![23, 0, 1]] where
  M :=![![![8, 4, -1], ![-75, -39, 11], ![251, 134, -32]]]
  hmulB := by decide  
  f := ![![![226, 6, -5]], ![![183, 5, -4]], ![![53, 2, -1]]]
  g := ![![![-3, 4, -1], ![29, -39, 11], ![-101, 134, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-6170, -4108, -1109]] ![![1163, 634, -166]]
  ![![226, 6, -5]] where
 M := ![![![226, 6, -5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![226, 6, -5]] ![![8, 4, -1]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-68019, -1464, 1610]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-68019, -1464, 1610]] 
 ![![107, 0, 0], ![0, 107, 0], ![28, 71, 1]] where
  M :=![![![-68019, -1464, 1610], ![115774, 2675, -2782], ![-50814, -1772, 1357]]]
  hmulB := by decide  
  f := ![![![12147, 8096, 2186]], ![![147110, 98049, 26474]], ![![106840, 71209, 19227]]]
  g := ![![![-1057, -1082, 1610], ![1810, 1871, -2782], ![-830, -917, 1357]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [34, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 106], [0, 1]]
 g := ![![[102, 85], [29, 42], [89], [53, 16], [41], [63, 1]], ![[0, 22], [0, 65], [89], [98, 91], [41], [19, 106]]]
 h' := ![![[63, 106], [84, 70], [45, 91], [17, 14], [1, 4], [105, 83], [0, 1]], ![[0, 1], [0, 37], [0, 16], [43, 93], [39, 103], [91, 24], [63, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [53, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [34, 44, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![376, 342, 258]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -168, 258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12147, 8096, 2186]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![12147, 8096, 2186]] 
 ![![107, 0, 0], ![0, 1, 0], ![71, 0, 1]] where
  M :=![![![12147, 8096, 2186], ![147110, 98049, 26474], ![646954, 431196, 116427]]]
  hmulB := by decide  
  f := ![![![-68019, -1464, 1610]], ![![1082, 25, -26]], ![![-45609, -988, 1081]]]
  g := ![![![-1337, 8096, 2186], ![-16192, 98049, 26474], ![-71209, 431196, 116427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-68019, -1464, 1610]] ![![12147, 8096, 2186]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51706, -26880, 7083]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-51706, -26880, 7083]] 
 ![![109, 0, 0], ![0, 109, 0], ![20, 33, 1]] where
  M :=![![![-51706, -26880, 7083], ![529773, 279743, -73557], ![-1674741, -886686, 233066]]]
  hmulB := by decide  
  f := ![![![214496, 142962, 38601]], ![![2597709, 1731377, 467487]], ![![930628, 620265, 167477]]]
  g := ![![![-1774, -2391, 7083], ![18357, 24836, -73557], ![-58129, -78696, 233066]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [68, 98, 1] where
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
 g := ![![[88, 49], [84], [12, 35], [21, 49], [84], [11, 1]], ![[82, 60], [84], [70, 74], [15, 60], [84], [22, 108]]]
 h' := ![![[11, 108], [40, 102], [56, 53], [98, 12], [72, 7], [15, 53], [0, 1]], ![[0, 1], [72, 7], [94, 56], [12, 97], [40, 102], [53, 56], [11, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [75, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [68, 98, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10399, 8204, 2204]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-309, -592, 2204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![214496, 142962, 38601]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![214496, 142962, 38601]] 
 ![![109, 0, 0], ![9, 1, 0], ![12, 0, 1]] where
  M :=![![![214496, 142962, 38601], ![2597709, 1731377, 467487], ![11424135, 7614204, 2055902]]]
  hmulB := by decide  
  f := ![![![-51706, -26880, 7083]], ![![591, 347, -90]], ![![-21057, -11094, 2918]]]
  g := ![![![-14086, 142962, 38601], ![-170592, 1731377, 467487], ![-750225, 7614204, 2055902]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-51706, -26880, 7083]] ![![214496, 142962, 38601]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-202, -134, -35]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-202, -134, -35]] 
 ![![113, 0, 0], ![0, 113, 0], ![9, 91, 1]] where
  M :=![![![-202, -134, -35], ![-2351, -1573, -437], ![-10669, -7092, -1876]]]
  hmulB := by decide  
  f := ![![![-1312, -28, 31]], ![![2229, 49, -53]], ![![1682, 37, -40]]]
  g := ![![![1, 27, -35], ![14, 338, -437], ![55, 1448, -1876]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [81, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 112], [0, 1]]
 g := ![![[93, 60], [50], [4], [69], [15, 49], [38, 1]], ![[0, 53], [50], [4], [69], [69, 64], [76, 112]]]
 h' := ![![[38, 112], [67, 25], [106, 29], [54, 2], [28, 42], [86, 7], [0, 1]], ![[0, 1], [0, 88], [78, 84], [17, 111], [42, 71], [13, 106], [38, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [64, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [81, 75, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1603, -476, 412]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -336, 412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1312, 28, -31]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1312, 28, -31]] 
 ![![113, 0, 0], ![65, 1, 0], ![82, 0, 1]] where
  M :=![![![1312, 28, -31], ![-2229, -49, 53], ![965, 26, -24]]]
  hmulB := by decide  
  f := ![![![202, 134, 35]], ![![137, 91, 24]], ![![241, 160, 42]]]
  g := ![![![18, 28, -31], ![-30, -49, 53], ![11, 26, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-202, -134, -35]] ![![1312, 28, -31]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4752889, 3167808, 855336]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![4752889, 3167808, 855336]] 
 ![![127, 0, 0], ![0, 127, 0], ![66, 23, 1]] where
  M :=![![![4752889, 3167808, 855336], ![57561048, 38364529, 10358760], ![253140456, 168718512, 45555481]]]
  hmulB := by decide  
  f := ![![![-11273, 192, 168]], ![![11736, -4241, 744]], ![![-3582, -553, 193]]]
  g := ![![![-407081, -129960, 855336], ![-4930056, -1573913, 10358760], ![-21681270, -6921713, 45555481]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [60, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 126], [0, 1]]
 g := ![![[67, 36], [21, 98], [7, 18], [39, 107], [5, 79], [44, 1]], ![[0, 91], [15, 29], [37, 109], [48, 20], [52, 48], [88, 126]]]
 h' := ![![[44, 126], [10, 121], [88, 112], [73, 79], [81, 19], [27, 98], [0, 1]], ![[0, 1], [0, 6], [63, 15], [120, 48], [28, 108], [21, 29], [44, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [80, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [60, 83, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![233, 772, 2049]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1063, -365, 2049]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11273, -192, -168]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![11273, -192, -168]] 
 ![![127, 0, 0], ![57, 1, 0], ![121, 0, 1]] where
  M :=![![![11273, -192, -168], ![-11736, 4241, -744], ![-19176, -14640, 3689]]]
  hmulB := by decide  
  f := ![![![-4752889, -3167808, -855336]], ![![-2586423, -1723855, -465456]], ![![-6521575, -4346640, -1173631]]]
  g := ![![![335, -192, -168], ![-1287, 4241, -744], ![2905, -14640, 3689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![4752889, 3167808, 855336]] ![![11273, -192, -168]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102, -64, -9]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-102, -64, -9]] 
 ![![131, 0, 0], ![0, 131, 0], ![55, 109, 1]] where
  M :=![![![-102, -64, -9], ![-575, -425, -201], ![-4841, -3094, -562]]]
  hmulB := by decide  
  f := ![![![2924, 62, -69]], ![![-4961, -105, 117]], ![![-2884, -61, 68]]]
  g := ![![![3, 7, -9], ![80, 164, -201], ![199, 444, -562]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [75, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 130], [0, 1]]
 g := ![![[88, 7], [74, 91], [84], [117], [49], [11], [1]], ![[0, 124], [109, 40], [84], [117], [49], [11], [1]]]
 h' := ![![[81, 130], [83, 20], [117, 22], [103, 79], [106, 36], [84, 7], [56, 81], [0, 1]], ![[0, 1], [0, 111], [65, 109], [83, 52], [9, 95], [127, 124], [67, 50], [81, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [128, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [75, 50, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![900, 950, 850]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-350, -700, 850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2924, 62, -69]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![2924, 62, -69]] 
 ![![131, 0, 0], ![65, 1, 0], ![54, 0, 1]] where
  M :=![![![2924, 62, -69], ![-4961, -105, 117], ![2125, 44, -50]]]
  hmulB := by decide  
  f := ![![![-102, -64, -9]], ![![-55, -35, -6]], ![![-79, -50, -8]]]
  g := ![![![20, 62, -69], ![-34, -105, 117], ![15, 44, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-102, -64, -9]] ![![2924, 62, -69]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-140, -72, 19]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-140, -72, 19]] 
 ![![137, 0, 0], ![78, 1, 0], ![7, 0, 1]] where
  M :=![![![-140, -72, 19], ![1421, 749, -197], ![-4485, -2374, 624]]]
  hmulB := by decide  
  f := ![![![-302, -178, -47]], ![![-195, -117, -31]], ![![-119, -78, -21]]]
  g := ![![![39, -72, 19], ![-406, 749, -197], ![1287, -2374, 624]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -2, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-21, -2, 0]] 
 ![![137, 0, 0], ![79, 1, 0], ![92, 0, 1]] where
  M :=![![![-21, -2, 0], ![2, -19, -6], ![-142, -86, -23]]]
  hmulB := by decide  
  f := ![![![79, 46, -12]], ![![39, 23, -6]], ![![74, 42, -11]]]
  g := ![![![1, -2, 0], ![15, -19, -6], ![64, -86, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -4, -1]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-8, -4, -1]] 
 ![![137, 0, 0], ![117, 1, 0], ![88, 0, 1]] where
  M :=![![![-8, -4, -1], ![-67, -47, -13], ![-317, -210, -56]]]
  hmulB := by decide  
  f := ![![![-98, -14, 5]], ![![-81, -11, 4]], ![![-69, -12, 4]]]
  g := ![![![4, -4, -1], ![48, -47, -13], ![213, -210, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-140, -72, 19]] ![![-21, -2, 0]]
  ![![98, 14, -5]] where
 M := ![![![98, 14, -5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![98, 14, -5]] ![![-8, -4, -1]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB201I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB201I2 : PrimesBelowBoundCertificateInterval O 79 137 201 where
  m := 11
  g := ![1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB201I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I101N1, I103N0, I103N1, I103N2, I107N1, I109N1, I113N1, I127N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[], [], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [I113N1], [I127N1], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
