
import IdealArithmetic.Examples.NF3_1_399735_1.RI3_1_399735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [130, 30, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 7, 109], [70, 131, 30], [0, 1]]
 g := ![![[3, 37, 31], [57, 60, 96], [15, 9], [5, 108, 44], [124, 47], [97, 1], []], ![[122, 87, 3, 75], [57, 95, 109, 60], [126, 42], [123, 44, 10, 21], [53, 129], [6, 64], [5, 66]], ![[77, 108, 19, 44], [77, 111, 135, 113], [95, 71], [8, 44, 82, 91], [38, 7], [56, 49], [84, 66]]]
 h' := ![![[27, 7, 109], [96, 7, 46], [75, 130, 97], [45, 4, 136], [135, 53, 105], [39, 18, 66], [0, 0, 1], [0, 1]], ![[70, 131, 30], [27, 53, 117], [128, 24, 50], [55, 64, 43], [131, 84, 72], [40, 29, 44], [79, 127, 131], [27, 7, 109]], ![[0, 1], [137, 79, 115], [0, 124, 131], [37, 71, 99], [25, 2, 101], [129, 92, 29], [96, 12, 7], [70, 131, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 12], []]
 b := ![[], [132, 17, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [130, 30, 42, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2338814, -858186, -134691]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16826, -6174, -969]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-100, -64, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-100, -64, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![49, 85, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-100, -64, 1], ![384, -88, -129], ![-24960, -4710, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -85, 149]], ![![-1, -1, 1], ![45, 73, -129], ![-181, -55, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [138, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 148], [0, 1]]
 g := ![![[120, 82], [125], [128, 7], [140], [64, 103], [143], [1]], ![[37, 67], [125], [130, 142], [140], [136, 46], [143], [1]]]
 h' := ![![[128, 148], [53, 23], [67, 42], [92, 93], [108, 132], [55, 111], [11, 128], [0, 1]], ![[0, 1], [17, 126], [79, 107], [76, 56], [18, 17], [108, 38], [5, 21], [128, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [121, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [138, 21, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2954, 3092, 1302]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-448, -722, 1302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-20, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-20, 1, 0]] 
 ![![149, 0, 0], ![129, 1, 0], ![108, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-20, 1, 0], ![0, -19, 2], ![384, 76, -21]]]
  hmulB := by decide  
  f := ![![![1881, -94, 0], ![14006, 0, 0]], ![![1621, -81, 0], ![12070, 0, 0]], ![![1372, -59, -1], ![10216, 75, 0]]]
  g := ![![![1, 0, 0], ![-129, 149, 0], ![-108, 0, 149]], ![![-1, 1, 0], ![15, -19, 2], ![-48, 76, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-100, -64, 1]] ![![149, 0, 0], ![-20, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-2980, 149, 0]], ![![-14900, -9536, 149], ![2384, 1192, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-20, 1, 0]]], ![![![-100, -64, 1]], ![![16, 8, -1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-24, 68, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-24, 68, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![127, 68, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-24, 68, 1], ![384, 120, 135], ![25728, 5322, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -68, 151]], ![![-1, 0, 1], ![-111, -60, 135], ![183, 42, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [51, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 150], [0, 1]]
 g := ![![[142, 59], [64, 31], [138, 84], [118], [98, 78], [36], [1]], ![[43, 92], [99, 120], [38, 67], [118], [113, 73], [36], [1]]]
 h' := ![![[6, 150], [58, 19], [59, 22], [96, 50], [136, 32], [10, 57], [100, 6], [0, 1]], ![[0, 1], [21, 132], [40, 129], [94, 101], [26, 119], [50, 94], [136, 145], [6, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [124, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [51, 145, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5517, 154, 60]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87, -26, 60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![16, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![16, 1, 0]] 
 ![![151, 0, 0], ![16, 1, 0], ![15, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![16, 1, 0], ![0, 17, 2], ![384, 76, 15]]]
  hmulB := by decide  
  f := ![![![1169, 73, 0], ![-11023, 0, 0]], ![![112, 7, 0], ![-1056, 0, 0]], ![![89, -3, -1], ![-839, 76, 0]]]
  g := ![![![1, 0, 0], ![-16, 151, 0], ![-15, 0, 151]], ![![0, 1, 0], ![-2, 17, 2], ![-7, 76, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-24, 68, 1]] ![![151, 0, 0], ![16, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![2416, 151, 0]], ![![-3624, 10268, 151], ![0, 1208, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![16, 1, 0]]], ![![![-24, 68, 1]], ![![0, 8, 1]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [119, 41, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 7, 88], [150, 149, 69], [0, 1]]
 g := ![![[133, 91, 86], [134, 12], [88, 28, 76], [107, 95, 127], [91, 55, 132], [23, 1], []], ![[19, 102, 43, 34], [104, 132], [55, 101, 98, 103], [100, 67, 4, 129], [7, 135, 82, 32], [155, 64], [50, 51]], ![[76, 41, 155, 128], [1, 16], [21, 139, 95, 8], [10, 56, 34, 149], [10, 95, 149, 150], [112, 49], [69, 51]]]
 h' := ![![[30, 7, 88], [79, 4, 137], [47, 67, 13], [141, 24, 95], [4, 0, 136], [89, 37, 17], [0, 0, 1], [0, 1]], ![[150, 149, 69], [91, 148, 41], [149, 77, 140], [118, 69, 96], [79, 126, 11], [129, 0, 137], [131, 151, 149], [30, 7, 88]], ![[0, 1], [11, 5, 136], [75, 13, 4], [6, 64, 123], [119, 31, 10], [21, 120, 3], [2, 6, 7], [150, 149, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 73], []]
 b := ![[], [2, 54, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [119, 41, 134, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8377049, -3077200, -457184]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53357, -19600, -2912]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [34, 48, 133, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 15, 74], [116, 147, 89], [0, 1]]
 g := ![![[108, 159, 111], [50, 17, 15], [14, 93], [70, 40], [69, 140], [37, 30, 1], []], ![[20, 127, 128, 91], [114, 66, 89, 136], [109, 97], [15, 41], [27, 95], [106, 21, 81, 36], [77, 97]], ![[17, 126, 20, 106], [42, 6, 26, 154], [49, 104], [82, 104], [7, 87], [147, 7, 23, 139], [62, 97]]]
 h' := ![![[77, 15, 74], [93, 11, 130], [113, 20, 34], [153, 117, 16], [96, 60, 140], [46, 138, 125], [0, 0, 1], [0, 1]], ![[116, 147, 89], [72, 50, 38], [127, 132, 121], [35, 161, 89], [120, 74, 81], [95, 110, 62], [51, 43, 147], [77, 15, 74]], ![[0, 1], [155, 102, 158], [162, 11, 8], [19, 48, 58], [6, 29, 105], [154, 78, 139], [101, 120, 15], [116, 147, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 47], []]
 b := ![[], [79, 114, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [34, 48, 133, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2234078, -648740, -72046]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13706, -3980, -442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [56, 128, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 39, 123], [47, 127, 44], [0, 1]]
 g := ![![[12, 5, 98], [50, 2, 99], [165, 166, 36], [58, 11], [32, 61], [51, 43, 1], []], ![[160, 158, 152, 20], [101, 63, 82, 53], [63, 15, 23, 74], [149, 64], [6, 28], [64, 153, 82, 74], [157, 99]], ![[66, 27, 28, 38], [18, 164, 138, 81], [50, 48, 119, 85], [69, 87], [68, 162], [53, 157, 88, 124], [69, 99]]]
 h' := ![![[163, 39, 123], [39, 20, 91], [112, 92, 123], [92, 143, 161], [0, 54, 41], [150, 82, 140], [0, 0, 1], [0, 1]], ![[47, 127, 44], [104, 27, 156], [118, 23, 50], [72, 134, 127], [20, 27, 159], [135, 164, 144], [75, 100, 127], [163, 39, 123]], ![[0, 1], [6, 120, 87], [102, 52, 161], [43, 57, 46], [147, 86, 134], [92, 88, 50], [15, 67, 39], [47, 127, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 118], []]
 b := ![[], [50, 47, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [56, 128, 124, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1072124469, 394657740, 64209329]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6419907, 2363220, 384487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-89, -59, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-89, -59, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![84, 114, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-89, -59, 1], ![384, -72, -119], ![-23040, -4330, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -114, 173]], ![![-1, -1, 1], ![60, 78, -119], ![-156, -56, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [114, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 172], [0, 1]]
 g := ![![[170, 140], [64], [20, 152], [117, 90], [25], [156, 16], [1]], ![[129, 33], [64], [104, 21], [103, 83], [25], [92, 157], [1]]]
 h' := ![![[169, 172], [66, 113], [142, 8], [156, 124], [105, 69], [35, 168], [59, 169], [0, 1]], ![[0, 1], [133, 60], [110, 165], [6, 49], [2, 104], [55, 5], [75, 4], [169, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162]]
 b := ![[], [162, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [114, 4, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1263, 466, 83]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -52, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-54, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-54, 1, 0]] 
 ![![173, 0, 0], ![119, 1, 0], ![126, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-54, 1, 0], ![0, -53, 2], ![384, 76, -55]]]
  hmulB := by decide  
  f := ![![![8803, -163, 0], ![28199, 0, 0]], ![![6049, -112, 0], ![19377, 0, 0]], ![![6462, -93, -1], ![20700, 87, 0]]]
  g := ![![![1, 0, 0], ![-119, 173, 0], ![-126, 0, 173]], ![![-1, 1, 0], ![35, -53, 2], ![-10, 76, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-89, -59, 1]] ![![173, 0, 0], ![-54, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-9342, 173, 0]], ![![-15397, -10207, 173], ![5190, 3114, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-54, 1, 0]]], ![![![-89, -59, 1]], ![![30, 18, -1]]]]
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


lemma PB179I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 178 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 178 (by omega)

def PB179I3 : PrimesBelowBoundCertificateInterval O 137 178 179 where
  m := 7
  g := ![1, 2, 2, 1, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB179I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I149N1, I151N1, I173N1]
  Il := ![[], [I149N1], [I151N1], [], [], [], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
