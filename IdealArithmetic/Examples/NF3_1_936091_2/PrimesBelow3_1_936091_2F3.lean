
import IdealArithmetic.Examples.NF3_1_936091_2.RI3_1_936091_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-19, 29, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-19, 29, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![120, 29, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-19, 29, 1], ![44, 6, 144], ![2910, -930, -80]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -29, 139]], ![![-1, 0, 1], ![-124, -30, 144], ![90, 10, -80]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [32, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 138], [0, 1]]
 g := ![![[67, 69], [114, 34], [4], [19, 66], [29], [6], [1]], ![[27, 70], [54, 105], [4], [17, 73], [29], [6], [1]]]
 h' := ![![[80, 138], [105, 25], [74, 112], [87, 2], [49, 30], [137, 86], [107, 80], [0, 1]], ![[0, 1], [20, 114], [138, 27], [108, 137], [86, 109], [67, 53], [113, 59], [80, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [111, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [32, 59, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1996, -486, -1100]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![964, 226, -1100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-5, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-5, 1, 0]] 
 ![![139, 0, 0], ![134, 1, 0], ![80, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-5, 1, 0], ![-2, -3, 5], ![102, -33, -6]]]
  hmulB := by decide  
  f := ![![![7322, 10990, -18315], ![-139, 509157, 0]], ![![7058, 10594, -17655], ![-138, 490809, 0]], ![![4215, 6325, -10541], ![-55, 293040, 0]]]
  g := ![![![1, 0, 0], ![-134, 139, 0], ![-80, 0, 139]], ![![-1, 1, 0], ![0, -3, 5], ![36, -33, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-19, 29, 1]] ![![139, 0, 0], ![-5, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-695, 139, 0]], ![![-2641, 4031, 139], ![139, -139, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-5, 1, 0]]], ![![![-19, 29, 1]], ![![1, -1, 1]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [82, 42, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 138, 33], [128, 10, 116], [0, 1]]
 g := ![![[93, 58, 80], [119, 125], [2, 127, 64], [26, 39], [122, 10, 133], [101, 1], []], ![[30, 51, 56, 96], [36, 45], [5, 38, 82, 144], [102, 46], [110, 143, 73, 29], [131, 100], [46, 46]], ![[89, 18, 49, 129], [113, 20], [70, 86, 47, 113], [35, 25], [102, 33, 135, 35], [78, 121], [112, 46]]]
 h' := ![![[122, 138, 33], [3, 138, 26], [134, 103, 42], [97, 23, 8], [128, 135, 28], [62, 146, 27], [0, 0, 1], [0, 1]], ![[128, 10, 116], [3, 20, 46], [71, 148, 94], [15, 140, 94], [83, 114, 116], [81, 37, 22], [86, 105, 10], [122, 138, 33]], ![[0, 1], [141, 140, 77], [136, 47, 13], [147, 135, 47], [127, 49, 5], [80, 115, 100], [48, 44, 138], [128, 10, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 113], []]
 b := ![[], [109, 146, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [82, 42, 48, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4479387, -2030870, 1603240]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30063, -13630, 10760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1827, 43, 54]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![1827, 43, 54]] 
 ![![151, 0, 0], ![0, 151, 0], ![59, 149, 1]] where
  M :=![![![1827, 43, 54], ![5422, 131, 161], ![1794, 39, 56]]]
  hmulB := by decide  
  f := ![![![7, -2, -1]], ![![-98, 36, -9]], ![![-95, 35, -9]]]
  g := ![![![-9, -53, 54], ![-27, -158, 161], ![-10, -55, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [46, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 150], [0, 1]]
 g := ![![[9, 64], [36, 124], [77, 139], [37], [13, 144], [11], [1]], ![[89, 87], [40, 27], [62, 12], [37], [42, 7], [11], [1]]]
 h' := ![![[39, 150], [5, 8], [82, 107], [146, 21], [6, 108], [100, 12], [105, 39], [0, 1]], ![[0, 1], [15, 143], [27, 44], [59, 130], [141, 43], [115, 139], [116, 112], [39, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [60, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [46, 112, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3299932, -627609, -1257577]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![513225, 1236764, -1257577]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -2, -1]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![7, -2, -1]] 
 ![![151, 0, 0], ![11, 1, 0], ![122, 0, 1]] where
  M :=![![![7, -2, -1], ![-98, 36, -9], ![-156, 39, 41]]]
  hmulB := by decide  
  f := ![![![1827, 43, 54]], ![![169, 4, 5]], ![![1488, 35, 44]]]
  g := ![![![1, -2, -1], ![4, 36, -9], ![-37, 39, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![1827, 43, 54]] ![![7, -2, -1]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [12, 58, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 143, 44], [36, 13, 113], [0, 1]]
 g := ![![[94, 0, 146], [43, 115], [109, 79, 10], [112, 156, 138], [54, 84, 81], [7, 1], []], ![[149, 80, 29, 126], [140, 89], [90, 149, 36, 46], [63, 94, 49, 121], [20, 94, 93, 156], [140, 12], [74, 52]], ![[111, 24, 69, 146], [42, 124], [103, 62, 128, 9], [1, 26, 50, 44], [37, 72, 67, 10], [128, 39], [5, 52]]]
 h' := ![![[128, 143, 44], [147, 53, 97], [105, 3, 30], [69, 39, 139], [137, 90, 74], [73, 53, 148], [0, 0, 1], [0, 1]], ![[36, 13, 113], [17, 107, 139], [21, 83, 51], [98, 7, 69], [15, 95, 55], [58, 84, 17], [110, 135, 13], [128, 143, 44]], ![[0, 1], [115, 154, 78], [84, 71, 76], [106, 111, 106], [13, 129, 28], [120, 20, 149], [137, 22, 143], [36, 13, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 30], []]
 b := ![[], [107, 81, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [12, 58, 150, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3042503, 1885884, -2587674]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19379, 12012, -16482]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-8, 49, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-8, 49, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![155, 49, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-8, 49, 1], ![4, 57, 244], ![4950, -1590, -89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-155, -49, 163]], ![![-1, 0, 1], ![-232, -73, 244], ![115, 17, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [45, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 162], [0, 1]]
 g := ![![[153, 104], [115, 160], [60], [145], [88], [100, 54], [1]], ![[9, 59], [69, 3], [60], [145], [88], [113, 109], [1]]]
 h' := ![![[124, 162], [41, 105], [39, 117], [72, 68], [136, 54], [64, 96], [118, 124], [0, 1]], ![[0, 1], [21, 58], [40, 46], [28, 95], [149, 109], [69, 67], [9, 39], [124, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [43, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [45, 39, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1969, -426, -1000]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![963, 298, -1000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-81, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-81, 1, 0]] 
 ![![163, 0, 0], ![82, 1, 0], ![89, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-81, 1, 0], ![-2, -79, 5], ![102, -33, -82]]]
  hmulB := by decide  
  f := ![![![201, 7900, -500], ![0, 16300, 0]], ![![101, 3950, -250], ![1, 8150, 0]], ![![150, 4313, -273], ![81, 8900, 0]]]
  g := ![![![1, 0, 0], ![-82, 163, 0], ![-89, 0, 163]], ![![-1, 1, 0], ![37, -79, 5], ![62, -33, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-8, 49, 1]] ![![163, 0, 0], ![-81, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-13203, 163, 0]], ![![-1304, 7987, 163], ![652, -3912, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-81, 1, 0]]], ![![![-8, 49, 1]], ![![4, -24, 1]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-24, 5, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-24, 5, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![143, 5, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-24, 5, 1], ![92, -47, 24], ![462, -138, -61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-143, -5, 167]], ![![-1, 0, 1], ![-20, -1, 24], ![55, 1, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [34, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 166], [0, 1]]
 g := ![![[110, 50], [119, 18], [110, 32], [87], [98], [57, 14], [1]], ![[150, 117], [100, 149], [2, 135], [87], [98], [135, 153], [1]]]
 h' := ![![[101, 166], [129, 65], [101, 128], [31, 52], [22, 33], [66, 91], [133, 101], [0, 1]], ![[0, 1], [14, 102], [3, 39], [106, 115], [15, 134], [72, 76], [147, 66], [101, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [121, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [34, 66, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33251, -7978, 709]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-408, -69, 709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-24, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-24, 1, 0]] 
 ![![167, 0, 0], ![143, 1, 0], ![61, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-24, 1, 0], ![-2, -22, 5], ![102, -33, -25]]]
  hmulB := by decide  
  f := ![![![36737, 408336, -92800], ![-2672, 3099520, 0]], ![![31449, 349638, -79460], ![-2337, 2653964, 0]], ![![13411, 149153, -33897], ![-1031, 1132160, 0]]]
  g := ![![![1, 0, 0], ![-143, 167, 0], ![-61, 0, 167]], ![![-1, 1, 0], ![17, -22, 5], ![38, -33, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-24, 5, 1]] ![![167, 0, 0], ![-24, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-4008, 167, 0]], ![![-4008, 835, 167], ![668, -167, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-24, 1, 0]]], ![![![-24, 5, 1]], ![![4, -1, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![84, 7, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![84, 7, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![84, 7, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![84, 7, 1], ![88, 65, 34], ![666, -204, 45]]]
  hmulB := by decide  
  f := ![![![-83, -7, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -7, 173]], ![![0, 0, 1], ![-16, -1, 34], ![-18, -3, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [160, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 172], [0, 1]]
 g := ![![[84, 133], [158], [158, 43], [44, 81], [64], [54, 148], [1]], ![[0, 40], [158], [58, 130], [93, 92], [64], [88, 25], [1]]]
 h' := ![![[54, 172], [116, 126], [151, 136], [53, 133], [67, 9], [10, 165], [13, 54], [0, 1]], ![[0, 1], [0, 47], [56, 37], [142, 40], [34, 164], [97, 8], [161, 119], [54, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [2, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [160, 119, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-916, 1077, -3059]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1480, 130, -3059]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-34, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-34, 1, 0]] 
 ![![173, 0, 0], ![139, 1, 0], ![128, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-34, 1, 0], ![-2, -32, 5], ![102, -33, -35]]]
  hmulB := by decide  
  f := ![![![38331, 625270, -97695], ![-3806, 3380247, 0]], ![![30785, 502354, -78490], ![-3113, 2715754, 0]], ![![28378, 462627, -72283], ![-2727, 2500992, 0]]]
  g := ![![![1, 0, 0], ![-139, 173, 0], ![-128, 0, 173]], ![![-1, 1, 0], ![22, -32, 5], ![53, -33, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![84, 7, 1]] ![![173, 0, 0], ![-34, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-5882, 173, 0]], ![![14532, 1211, 173], ![-2768, -173, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-34, 1, 0]]], ![![![84, 7, 1]], ![![-16, -1, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![52, -65, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![52, -65, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![52, 114, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![52, -65, 1], ![232, -111, -326], ![-6678, 2172, 85]]]
  hmulB := by decide  
  f := ![![![-51, 65, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -114, 179]], ![![0, -1, 1], ![96, 207, -326], ![-62, -42, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [118, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 178], [0, 1]]
 g := ![![[140, 27], [29, 141], [107], [89], [49, 70], [7, 19], [1]], ![[168, 152], [36, 38], [107], [89], [168, 109], [93, 160], [1]]]
 h' := ![![[127, 178], [158, 57], [53, 61], [111, 110], [125, 39], [69, 41], [61, 127], [0, 1]], ![[0, 1], [58, 122], [103, 118], [119, 69], [66, 140], [85, 138], [80, 52], [127, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [42, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [118, 52, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5276, -330, -2735]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![824, 1740, -2735]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-32, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-32, 1, 0]] 
 ![![179, 0, 0], ![147, 1, 0], ![94, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-32, 1, 0], ![-2, -30, 5], ![102, -33, -33]]]
  hmulB := by decide  
  f := ![![![30325, 462075, -77010], ![-2685, 2756958, 0]], ![![24881, 379453, -63240], ![-2326, 2263992, 0]], ![![15922, 242654, -40441], ![-1426, 1447788, 0]]]
  g := ![![![1, 0, 0], ![-147, 179, 0], ![-94, 0, 179]], ![![-1, 1, 0], ![22, -30, 5], ![45, -33, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![52, -65, 1]] ![![179, 0, 0], ![-32, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-5728, 179, 0]], ![![9308, -11635, 179], ![-1432, 1969, -358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-32, 1, 0]]], ![![![52, -65, 1]], ![![-8, 11, -2]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-54, -38, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-54, -38, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![127, 143, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-54, -38, 1], ![178, -163, -191], ![-3924, 1281, -48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -143, 181]], ![![-1, -1, 1], ![135, 150, -191], ![12, 45, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [65, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 180], [0, 1]]
 g := ![![[109, 39], [81], [80, 111], [133], [118, 73], [103, 133], [1]], ![[0, 142], [81], [90, 70], [133], [30, 108], [84, 48], [1]]]
 h' := ![![[155, 180], [32, 43], [49, 9], [142, 78], [113, 155], [2, 142], [116, 155], [0, 1]], ![[0, 1], [0, 138], [177, 172], [105, 103], [65, 26], [111, 39], [68, 26], [155, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [147, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [65, 26, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19820, -3985, -7540]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5400, 5935, -7540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![10, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![10, 1, 0]] 
 ![![181, 0, 0], ![10, 1, 0], ![48, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![10, 1, 0], ![-2, 12, 5], ![102, -33, 9]]]
  hmulB := by decide  
  f := ![![![27019, -162352, -67645], ![724, 2448749, 0]], ![![1484, -8965, -3735], ![182, 135207, 0]], ![![7162, -43055, -17939], ![251, 649392, 0]]]
  g := ![![![1, 0, 0], ![-10, 181, 0], ![-48, 0, 181]], ![![0, 1, 0], ![-2, 12, 5], ![0, -33, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-54, -38, 1]] ![![181, 0, 0], ![10, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![1810, 181, 0]], ![![-9774, -6878, 181], ![-362, -543, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![10, 1, 0]]], ![![![-54, -38, 1]], ![![-2, -3, -1]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![23, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![23, 1, 0]] 
 ![![191, 0, 0], ![23, 1, 0], ![152, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![23, 1, 0], ![-2, 25, 5], ![102, -33, 22]]]
  hmulB := by decide  
  f := ![![![9004, -113403, -22680], ![573, 866376, 0]], ![![1069, -13651, -2730], ![192, 104286, 0]], ![![7152, -90248, -18049], ![568, 689472, 0]]]
  g := ![![![1, 0, 0], ![-23, 191, 0], ![-152, 0, 191]], ![![0, 1, 0], ![-7, 25, 5], ![-13, -33, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-12, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-12, 1, 0]] 
 ![![191, 0, 0], ![179, 1, 0], ![52, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-12, 1, 0], ![-2, -10, 5], ![102, -33, -13]]]
  hmulB := by decide  
  f := ![![![49243, 246759, -123375], ![-1719, 4712925, 0]], ![![46153, 231248, -115620], ![-1527, 4416684, 0]], ![![13412, 67180, -33589], ![-380, 1283100, 0]]]
  g := ![![![1, 0, 0], ![-179, 191, 0], ![-52, 0, 191]], ![![-1, 1, 0], ![8, -10, 5], ![35, -33, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![23, 1, 0]] ![![191, 0, 0], ![-12, 1, 0]]
  ![![191, 0, 0], ![59, 79, 1]] where
 M := ![![![36481, 0, 0], ![-2292, 191, 0]], ![![4393, 191, 0], ![-278, 13, 5]]]
 hmul := by decide  
 g := ![![![![132, -79, -1], ![191, 0, 0]], ![![-12, 1, 0], ![0, 0, 0]]], ![![![-36, -78, -1], ![191, 0, 0]], ![![-3, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![59, 79, 1]] ![![191, 0, 0], ![-12, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-2292, 191, 0]], ![![11269, 15089, 191], ![-764, -764, 382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-12, 1, 0]]], ![![![59, 79, 1]], ![![-4, -4, 2]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-75, -87, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-75, -87, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![118, 106, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-75, -87, 1], ![276, -282, -436], ![-8922, 2898, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-118, -106, 193]], ![![-1, -1, 1], ![268, 238, -436], ![-34, 26, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [33, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 192], [0, 1]]
 g := ![![[113, 190], [128], [63], [96], [56], [85], [131, 1]], ![[106, 3], [128], [63], [96], [56], [85], [69, 192]]]
 h' := ![![[131, 192], [94, 169], [119, 30], [70, 177], [27, 17], [36, 153], [116, 144], [0, 1]], ![[0, 1], [38, 24], [189, 163], [97, 16], [131, 176], [7, 40], [66, 49], [131, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [123, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [33, 62, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19127, 8932, -7308]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4369, 4060, -7308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![50, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![50, 1, 0]] 
 ![![193, 0, 0], ![50, 1, 0], ![20, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![50, 1, 0], ![-2, 52, 5], ![102, -33, 49]]]
  hmulB := by decide  
  f := ![![![31205, -837324, -80510], ![3860, 3107686, 0]], ![![8042, -216898, -20855], ![1159, 805003, 0]], ![![3200, -86770, -8343], ![530, 322040, 0]]]
  g := ![![![1, 0, 0], ![-50, 193, 0], ![-20, 0, 193]], ![![0, 1, 0], ![-14, 52, 5], ![4, -33, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-75, -87, 1]] ![![193, 0, 0], ![50, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![9650, 193, 0]], ![![-14475, -16791, 193], ![-3474, -4632, -386]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![50, 1, 0]]], ![![![-75, -87, 1]], ![![-18, -24, -2]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB274I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB274I3 : PrimesBelowBoundCertificateInterval O 137 193 274 where
  m := 11
  g := ![2, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB274I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N1]
    · exact ![I193N0, I193N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N1, I163N1, I167N1, I173N1, I179N1, I181N1, I191N0, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [], [I163N1], [I167N1], [I173N1], [I179N1], [I181N1], [I191N0, I191N1, I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
