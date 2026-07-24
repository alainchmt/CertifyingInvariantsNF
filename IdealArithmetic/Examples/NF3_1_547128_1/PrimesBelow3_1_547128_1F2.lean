
import IdealArithmetic.Examples.NF3_1_547128_1.RI3_1_547128_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-11, 8, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-11, 8, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![72, 8, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-11, 8, 1], ![160, 27, 76], ![1038, 60, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -8, 83]], ![![-1, 0, 1], ![-64, -7, 76], ![42, 4, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [59, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 82], [0, 1]]
 g := ![![[58, 38], [26, 75], [1], [29], [31, 29], [1]], ![[0, 45], [12, 8], [1], [29], [61, 54], [1]]]
 h' := ![![[64, 82], [43, 11], [45, 65], [41, 82], [80, 19], [24, 64], [0, 1]], ![[0, 1], [0, 72], [55, 18], [60, 1], [51, 64], [53, 19], [64, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [45, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [59, 19, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1529, 465, 110]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -5, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![7, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![7, 1, 0]] 
 ![![83, 0, 0], ![7, 1, 0], ![34, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![7, 1, 0], ![2, 11, 10], ![144, 6, 3]]]
  hmulB := by decide  
  f := ![![![-760, -4223, -3840], ![-83, 31872, 0]], ![![-64, -352, -320], ![1, 2656, 0]], ![![-312, -1730, -1573], ![-26, 13056, 0]]]
  g := ![![![1, 0, 0], ![-7, 83, 0], ![-34, 0, 83]], ![![0, 1, 0], ![-5, 11, 10], ![0, 6, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-11, 8, 1]] ![![83, 0, 0], ![7, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![581, 83, 0]], ![![-913, 664, 83], ![83, 83, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![7, 1, 0]]], ![![![-11, 8, 1]], ![![1, 1, 1]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [48, 67, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 34, 21], [33, 54, 68], [0, 1]]
 g := ![![[75, 19, 64], [77, 16], [56, 42], [33, 16, 80], [71, 82, 1], []], ![[29, 81, 49, 1], [83, 32], [2, 18], [81, 24, 69, 81], [2, 85, 36, 4], [32, 85]], ![[87, 47, 34, 85], [1, 49], [39, 20], [56, 40, 79, 40], [67, 65, 68, 21], [74, 85]]]
 h' := ![![[49, 34, 21], [50, 32, 81], [39, 57, 4], [18, 11, 24], [63, 29, 13], [0, 0, 1], [0, 1]], ![[33, 54, 68], [38, 16, 62], [62, 71, 78], [46, 30, 14], [2, 58, 65], [64, 45, 54], [49, 34, 21]], ![[0, 1], [73, 41, 35], [78, 50, 7], [9, 48, 51], [62, 2, 11], [29, 44, 34], [33, 54, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 9], []]
 b := ![[], [57, 29, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [48, 67, 7, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1733186, 273230, -23229]
  a := ![2, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19474, 3070, -261]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [86, 90, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 24, 2], [44, 72, 95], [0, 1]]
 g := ![![[28, 72, 86], [51, 54], [44, 36], [78, 93], [79, 35], [1]], ![[55, 59, 1, 22], [25, 25], [49, 32], [39, 2], [25, 32], [74, 30, 0, 8]], ![[18, 4, 77, 2], [53, 11], [57, 75], [20, 66], [2, 25], [46, 64, 85, 89]]]
 h' := ![![[17, 24, 2], [43, 40, 59], [8, 34, 65], [94, 47, 6], [20, 25, 53], [11, 7, 61], [0, 1]], ![[44, 72, 95], [8, 60, 60], [86, 53, 92], [41, 4, 41], [0, 48, 83], [4, 25, 41], [17, 24, 2]], ![[0, 1], [74, 94, 75], [48, 10, 37], [10, 46, 50], [88, 24, 58], [39, 65, 92], [44, 72, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 78], []]
 b := ![[], [26, 65, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [86, 90, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43352167611, -5133560391, -1847827593]
  a := ![-65, -129, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-446929563, -52923303, -19049769]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1448905, 90327, 17290]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1448905, 90327, 17290]] 
 ![![101, 0, 0], ![0, 101, 0], ![50, 23, 1]] where
  M :=![![![-1448905, 90327, 17290], ![2670414, -983857, 834110], ![11036028, 749442, -1654603]]]
  hmulB := by decide  
  f := ![![![-9928472051, -1608051261, -914391500]], ![![-134888478522, -21847026095, -12422946610]], ![![-36892845140, -5975298701, -3397753837]]]
  g := ![![![-22905, -3043, 17290], ![-386486, -199687, 834110], ![928378, 384211, -1654603]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [17, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 100], [0, 1]]
 g := ![![[33, 6], [17], [37, 37], [36], [43], [45, 1]], ![[0, 95], [17], [86, 64], [36], [43], [90, 100]]]
 h' := ![![[45, 100], [38, 62], [78, 57], [43, 21], [7, 95], [43, 89], [0, 1]], ![[0, 1], [0, 39], [17, 44], [79, 80], [40, 6], [8, 12], [45, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [57, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [17, 56, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4363, 1728, 343]
  a := ![-2, -3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-213, -61, 343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9928472051, 1608051261, 914391500]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![9928472051, 1608051261, 914391500]] 
 ![![101, 0, 0], ![77, 1, 0], ![33, 0, 1]] where
  M :=![![![9928472051, 1608051261, 914391500], ![134888478522, 21847026095, 12422946610], ![127318750584, 20621005566, 11725790507]]]
  hmulB := by decide  
  f := ![![![1448905, -90327, -17290]], ![![1078171, -59122, -21440]], ![![364137, -36933, 10733]]]
  g := ![![![-1426399946, 1608051261, 914391500], ![-19379106623, 21847026095, 12422946610], ![-18291581829, 20621005566, 11725790507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1448905, 90327, 17290]] ![![9928472051, 1608051261, 914391500]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [48, 95, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 15, 85], [38, 87, 18], [0, 1]]
 g := ![![[11, 9, 72], [69, 64, 76], [84, 41, 4], [80, 82], [60, 7], [1]], ![[35, 60, 47, 53], [88, 32, 27, 87], [64, 23, 8, 35], [48, 72], [30, 17], [6, 90, 2, 39]], ![[21, 9, 102, 26], [99, 6, 5, 83], [61, 80, 16, 60], [58, 30], [40, 16], [73, 39, 56, 64]]]
 h' := ![![[90, 15, 85], [87, 74, 22], [88, 93, 30], [87, 11, 2], [42, 97, 44], [55, 8, 25], [0, 1]], ![[38, 87, 18], [26, 77, 67], [14, 80, 9], [54, 43, 79], [68, 7, 22], [90, 37, 74], [90, 15, 85]], ![[0, 1], [32, 55, 14], [87, 33, 64], [29, 49, 22], [54, 102, 37], [74, 58, 4], [38, 87, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 88], []]
 b := ![[], [89, 89, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [48, 95, 78, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236076, -2472, -4120]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2292, -24, -40]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-46, -24, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-46, -24, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![61, 83, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-46, -24, 1], ![96, -136, -244], ![-3570, -132, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -83, 107]], ![![-1, -1, 1], ![140, 188, -244], ![-67, -47, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [68, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 106], [0, 1]]
 g := ![![[68, 9], [13, 10], [4], [25, 102], [19], [84, 1]], ![[75, 98], [104, 97], [4], [33, 5], [19], [61, 106]]]
 h' := ![![[84, 106], [79, 104], [86, 63], [12, 2], [68, 67], [66, 33], [0, 1]], ![[0, 1], [41, 3], [28, 44], [73, 105], [25, 40], [56, 74], [84, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [99, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [68, 23, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51558, 6193, 4606]
  a := ![2, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2144, -3515, 4606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![30, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![30, 1, 0]] 
 ![![107, 0, 0], ![30, 1, 0], ![48, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![30, 1, 0], ![2, 34, 10], ![144, 6, 26]]]
  hmulB := by decide  
  f := ![![![-3869, -73934, -21750], ![-1712, 232725, 0]], ![![-1098, -20702, -6090], ![-427, 65163, 0]], ![![-1746, -33167, -9757], ![-731, 104400, 0]]]
  g := ![![![1, 0, 0], ![-30, 107, 0], ![-48, 0, 107]], ![![0, 1, 0], ![-14, 34, 10], ![-12, 6, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-46, -24, 1]] ![![107, 0, 0], ![30, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![3210, 107, 0]], ![![-4922, -2568, 107], ![-1284, -856, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![30, 1, 0]]], ![![![-46, -24, 1]], ![![-12, -8, -2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![825, -157, 102]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![825, -157, 102]] 
 ![![109, 0, 0], ![0, 109, 0], ![69, 38, 1]] where
  M :=![![![825, -157, 102], ![14374, 809, -1978], ![-34236, 282, 2371]]]
  hmulB := by decide  
  f := ![![![22715, 3679, 2092]], ![![308606, 49983, 28422]], ![![124639, 20187, 11479]]]
  g := ![![![-57, -37, 102], ![1384, 697, -1978], ![-1815, -824, 2371]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [71, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 108], [0, 1]]
 g := ![![[26, 43], [38], [56, 61], [107, 43], [48], [7, 1]], ![[0, 66], [38], [47, 48], [81, 66], [48], [14, 108]]]
 h' := ![![[7, 108], [6, 77], [57, 93], [33, 72], [95, 77], [48, 87], [0, 1]], ![[0, 1], [0, 32], [54, 16], [101, 37], [89, 32], [3, 22], [7, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [6, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [71, 102, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6769, 986, -215]
  a := ![-2, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![74, 84, -215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22715, 3679, 2092]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![22715, 3679, 2092]] 
 ![![109, 0, 0], ![60, 1, 0], ![74, 0, 1]] where
  M :=![![![22715, 3679, 2092], ![308606, 49983, 28422], ![291288, 47178, 26827]]]
  hmulB := by decide  
  f := ![![![825, -157, 102]], ![![586, -79, 38]], ![![246, -104, 91]]]
  g := ![![![-3237, 3679, 2092], ![-43978, 49983, 28422], ![-41510, 47178, 26827]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![825, -157, 102]] ![![22715, 3679, 2092]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-919, 28, 42]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-919, 28, 42]] 
 ![![113, 0, 0], ![11, 1, 0], ![108, 0, 1]] where
  M :=![![![-919, 28, 42], ![6104, -555, 112], ![-756, 672, -653]]]
  hmulB := by decide  
  f := ![![![-287151, -46508, -26446]], ![![-62477, -10119, -5754]], ![![-307032, -49728, -28277]]]
  g := ![![![-51, 28, 42], ![1, -555, 112], ![552, 672, -653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![18, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![18, 1, 0]] 
 ![![113, 0, 0], ![18, 1, 0], ![51, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![18, 1, 0], ![2, 22, 10], ![144, 6, 14]]]
  hmulB := by decide  
  f := ![![![-1019, -11614, -5280], ![-226, 59664, 0]], ![![-168, -1848, -840], ![1, 9492, 0]], ![![-465, -5242, -2383], ![-70, 26928, 0]]]
  g := ![![![1, 0, 0], ![-18, 113, 0], ![-51, 0, 113]], ![![0, 1, 0], ![-8, 22, 10], ![-6, 6, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-29, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-29, 1, 0]] 
 ![![113, 0, 0], ![84, 1, 0], ![52, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-29, 1, 0], ![2, -25, 10], ![144, 6, -33]]]
  hmulB := by decide  
  f := ![![![4331, -59186, 23680], ![-1582, -267584, 0]], ![![3231, -43990, 17600], ![-1129, -198880, 0]], ![![1992, -27236, 10897], ![-732, -123136, 0]]]
  g := ![![![1, 0, 0], ![-84, 113, 0], ![-52, 0, 113]], ![![-1, 1, 0], ![14, -25, 10], ![12, 6, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-919, 28, 42]] ![![113, 0, 0], ![18, 1, 0]]
  ![![113, 0, 0], ![20, -8, 1]] where
 M := ![![![-103847, 3164, 4746], ![-10438, -51, 868]]]
 hmul := by decide  
 g := ![![![![-899, 20, 43], ![-113, 0, 0]], ![![-106, 5, 7], ![77, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![20, -8, 1]] ![![113, 0, 0], ![-29, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-3277, 113, 0]], ![![2260, -904, 113], ![-452, 226, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-29, 1, 0]]], ![![![20, -8, 1]], ![![-4, 2, -1]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64629561798302961216103011, 10467637700321810084866733, 5952247400559588631874742]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![64629561798302961216103011, 10467637700321810084866733, 5952247400559588631874742]] 
 ![![127, 0, 0], ![34, 1, 0], ![125, 0, 1]] where
  M :=![![![64629561798302961216103011, 10467637700321810084866733, 5952247400559588631874742], ![878058901081224383159696314, 142213597002947733346818395, 80867387400979746321168362], ![828783625182547548187088964, 134232795008645924091697302, 76329237602052018563508757]]]
  hmulB := by decide  
  f := ![![![152141388025691, -6118180134797, -5382235577744]], ![![34531723696132, -886951736717, -1753140698270]], ![![147639609603649, -6819436414105, -4288231959471]]]
  g := ![![![-8151976732933757170501643, 10467637700321810084866733, 5952247400559588631874742], ![-110752967103476116856521058, 142213597002947733346818395, 80867387400979746321168362], ![-104537685869038710168261527, 134232795008645924091697302, 76329237602052018563508757]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-27, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-27, 1, 0]] 
 ![![127, 0, 0], ![100, 1, 0], ![27, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-27, 1, 0], ![2, -23, 10], ![144, 6, -31]]]
  hmulB := by decide  
  f := ![![![-3328, 41069, -17860], ![1143, 226822, 0]], ![![-2622, 32331, -14060], ![890, 178562, 0]], ![![-702, 8731, -3797], ![269, 48222, 0]]]
  g := ![![![1, 0, 0], ![-100, 127, 0], ![-27, 0, 127]], ![![-1, 1, 0], ![16, -23, 10], ![3, 6, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-7, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-7, 1, 0]] 
 ![![127, 0, 0], ![120, 1, 0], ![87, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-7, 1, 0], ![2, -3, 10], ![144, 6, -11]]]
  hmulB := by decide  
  f := ![![![-4082, 6153, -20520], ![381, 260604, 0]], ![![-3854, 5811, -19380], ![382, 246126, 0]], ![![-2796, 4215, -14057], ![267, 178524, 0]]]
  g := ![![![1, 0, 0], ![-120, 127, 0], ![-87, 0, 127]], ![![-1, 1, 0], ![-4, -3, 10], ![3, 6, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![64629561798302961216103011, 10467637700321810084866733, 5952247400559588631874742]] ![![127, 0, 0], ![-27, 1, 0]]
  ![![127, 0, 0], ![10, -37, 1]] where
 M := ![![![8207954348384476074445082397, 1329389987940869880778075091, 755935419871067756248092234], ![-866939267472955569675084983, -140412620905741138944583396, -79843292414129146739449672]]]
 hmul := by decide  
 g := ![![![![64479016159078185815425221, 11024656565453479067374556, 5937192836637111091806963], ![1911929618154647588607933, 0, 0]], ![![-6810392536762885348123499, -1164444547486589934324139, -627097251052930973961493], ![-201941530406913046340061, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![10, -37, 1]] ![![127, 0, 0], ![-7, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-889, 127, 0]], ![![1270, -4699, 127], ![0, 127, -381]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-7, 1, 0]]], ![![![10, -37, 1]], ![![0, 1, -3]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [97, 90, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 24, 110], [71, 106, 21], [0, 1]]
 g := ![![[68, 38, 21], [34, 33, 77], [92, 62], [47, 4], [123, 121], [25, 1], []], ![[75, 49, 89, 86], [107, 96, 52, 14], [32, 89], [35, 1], [61, 62], [71, 101], [61, 48]], ![[75, 119, 8, 109], [122, 128, 10, 41], [47, 28], [54, 1], [58, 55], [76, 52], [19, 48]]]
 h' := ![![[85, 24, 110], [108, 27, 105], [0, 47, 83], [127, 25, 18], [25, 85, 2], [64, 11, 11], [0, 0, 1], [0, 1]], ![[71, 106, 21], [97, 116, 83], [30, 35, 82], [120, 11, 73], [41, 126, 130], [60, 86, 18], [129, 91, 106], [85, 24, 110]], ![[0, 1], [97, 119, 74], [90, 49, 97], [123, 95, 40], [11, 51, 130], [129, 34, 102], [54, 40, 24], [71, 106, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 15], []]
 b := ![[], [92, 22, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [97, 90, 106, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2782309, 495180, 191260]
  a := ![2, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21239, 3780, 1460]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [50, 14, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 119, 81], [5, 17, 56], [0, 1]]
 g := ![![[116, 12, 77], [109, 99], [134, 25], [47, 118, 136], [86, 118], [96, 1], []], ![[132, 106, 90, 14], [16, 49], [38, 22], [59, 38, 133, 77], [123, 61], [46, 15], [28, 122]], ![[89, 60, 12, 65], [45, 129], [37, 109], [47, 124, 83, 77], [44, 118], [36, 50], [53, 122]]]
 h' := ![![[91, 119, 81], [98, 99, 25], [43, 43, 109], [116, 117, 132], [109, 123, 100], [132, 113, 23], [0, 0, 1], [0, 1]], ![[5, 17, 56], [18, 70, 87], [74, 100, 130], [59, 17, 76], [17, 125, 18], [31, 37, 91], [31, 96, 17], [91, 119, 81]], ![[0, 1], [43, 105, 25], [52, 131, 35], [126, 3, 66], [31, 26, 19], [54, 124, 23], [115, 41, 119], [5, 17, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 51], []]
 b := ![[], [73, 25, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [50, 14, 41, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19201920, -2037190, -731580]
  a := ![-5, -10, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140160, -14870, -5340]
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



lemma PB210I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB210I2 : PrimesBelowBoundCertificateInterval O 79 137 210 where
  m := 11
  g := ![2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB210I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I101N1, I107N1, I109N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2]
  Il := ![[I83N1], [], [], [I101N1], [], [I107N1], [I109N1], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
