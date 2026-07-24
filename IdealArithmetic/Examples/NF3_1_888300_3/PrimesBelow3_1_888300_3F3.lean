
import IdealArithmetic.Examples.NF3_1_888300_3.RI3_1_888300_3
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [41, 5, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 79, 54], [15, 59, 85], [0, 1]]
 g := ![![[106, 4, 86], [80, 128, 47], [44, 80], [6, 137, 129], [21, 91], [117, 1], []], ![[14, 127, 21, 124], [17, 84, 16, 36], [105, 6], [25, 81, 51, 77], [24, 11], [79, 6], [119, 136]], ![[53, 106, 31, 32], [124, 12], [59, 51], [50, 124, 76, 133], [116, 125], [115, 125], [88, 136]]]
 h' := ![![[102, 79, 54], [56, 48, 124], [54, 112, 66], [32, 13, 48], [10, 127, 44], [68, 69, 62], [0, 0, 1], [0, 1]], ![[15, 59, 85], [56, 11, 39], [133, 103, 73], [95, 88, 59], [26, 33, 2], [71, 16, 17], [104, 76, 59], [102, 79, 54]], ![[0, 1], [91, 80, 115], [22, 63], [56, 38, 32], [125, 118, 93], [135, 54, 60], [92, 63, 79], [15, 59, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 94], []]
 b := ![[], [76, 75, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [41, 5, 22, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-829969, -266185, -21823]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5971, -1915, -157]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-31, -62, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-31, -62, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![118, 87, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-31, -62, 1], ![730, 119, -62], ![-45260, -8570, 119]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-118, -87, 149]], ![![-1, -1, 1], ![54, 37, -62], ![-398, -127, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [120, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 148], [0, 1]]
 g := ![![[112, 113], [67], [34, 125], [80], [63, 140], [6], [1]], ![[0, 36], [67], [9, 24], [80], [35, 9], [6], [1]]]
 h' := ![![[119, 148], [126, 34], [92, 118], [116, 42], [39, 123], [121, 17], [29, 119], [0, 1]], ![[0, 1], [0, 115], [128, 31], [48, 107], [74, 26], [58, 132], [35, 30], [119, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [117, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [120, 30, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8669, 4714, 1438]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1197, -808, 1438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![62, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![62, 1, 0]] 
 ![![149, 0, 0], ![62, 1, 0], ![30, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![62, 1, 0], ![0, 62, 1], ![730, 150, 62]]]
  hmulB := by decide  
  f := ![![![2915, 47, 0], ![-7003, 0, 0]], ![![1178, 19, 0], ![-2830, 0, 0]], ![![522, 8, 0], ![-1254, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 149, 0], ![-30, 0, 149]], ![![0, 1, 0], ![-26, 62, 1], ![-70, 150, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-31, -62, 1]] ![![149, 0, 0], ![62, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![9238, 149, 0]], ![![-4619, -9238, 149], ![-1192, -3725, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![62, 1, 0]]], ![![![-31, -62, 1]], ![![-8, -25, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-103, -54, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-103, -54, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![48, 97, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-103, -54, 1], ![730, 47, -54], ![-39420, -7370, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -97, 151]], ![![-1, -1, 1], ![22, 35, -54], ![-276, -79, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [133, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 150], [0, 1]]
 g := ![![[7, 10], [99, 105], [11, 148], [42], [21, 128], [21], [1]], ![[59, 141], [41, 46], [86, 3], [42], [143, 23], [21], [1]]]
 h' := ![![[126, 150], [121, 114], [47, 135], [39, 65], [76, 58], [98, 85], [18, 126], [0, 1]], ![[0, 1], [140, 37], [145, 16], [75, 86], [136, 93], [87, 66], [39, 25], [126, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [128, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [133, 25, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1169, 327, 254]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73, -161, 254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![54, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![54, 1, 0]] 
 ![![151, 0, 0], ![54, 1, 0], ![104, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![54, 1, 0], ![0, 54, 1], ![730, 150, 54]]]
  hmulB := by decide  
  f := ![![![649, 12, 0], ![-1812, 0, 0]], ![![162, 3, 0], ![-452, 0, 0]], ![![452, 8, 0], ![-1262, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 151, 0], ![-104, 0, 151]], ![![0, 1, 0], ![-20, 54, 1], ![-86, 150, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-103, -54, 1]] ![![151, 0, 0], ![54, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![8154, 151, 0]], ![![-15553, -8154, 151], ![-4832, -2869, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![54, 1, 0]]], ![![![-103, -54, 1]], ![![-32, -19, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-24, 35, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-24, 35, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![133, 35, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-24, 35, 1], ![730, 126, 35], ![25550, 5980, 126]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-133, -35, 157]], ![![-1, 0, 1], ![-25, -7, 35], ![56, 10, 126]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [43, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 156], [0, 1]]
 g := ![![[148, 110], [4], [16, 81], [8, 67], [140, 101], [148], [1]], ![[14, 47], [4], [120, 76], [32, 90], [134, 56], [148], [1]]]
 h' := ![![[73, 156], [131, 61], [97, 155], [127, 148], [103, 99], [38, 130], [114, 73], [0, 1]], ![[0, 1], [31, 96], [108, 2], [98, 9], [108, 58], [108, 27], [105, 84], [73, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [82, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [43, 84, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4252, 5756, 1093]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-953, -207, 1093]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-35, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-35, 1, 0]] 
 ![![157, 0, 0], ![122, 1, 0], ![31, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-35, 1, 0], ![0, -35, 1], ![730, 150, -35]]]
  hmulB := by decide  
  f := ![![![456, -13, 0], ![2041, 0, 0]], ![![386, -11, 0], ![1728, 0, 0]], ![![148, -4, 0], ![663, 1, 0]]]
  g := ![![![1, 0, 0], ![-122, 157, 0], ![-31, 0, 157]], ![![-1, 1, 0], ![27, -35, 1], ![-105, 150, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-24, 35, 1]] ![![157, 0, 0], ![-35, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-5495, 157, 0]], ![![-3768, 5495, 157], ![1570, -1099, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-35, 1, 0]]], ![![![-24, 35, 1]], ![![10, -7, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-110, 23, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-110, 23, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![53, 23, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-110, 23, 1], ![730, 40, 23], ![16790, 4180, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -23, 163]], ![![-1, 0, 1], ![-3, -3, 23], ![90, 20, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [13, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 162], [0, 1]]
 g := ![![[106, 91], [132, 35], [15], [155], [113], [125, 97], [1]], ![[55, 72], [150, 128], [15], [155], [113], [119, 66], [1]]]
 h' := ![![[89, 162], [77, 55], [3, 19], [144, 129], [23, 36], [5, 90], [150, 89], [0, 1]], ![[0, 1], [82, 108], [64, 144], [52, 34], [130, 127], [28, 73], [84, 74], [89, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [136, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [13, 74, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1473, 956, 77]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -5, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-23, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-23, 1, 0]] 
 ![![163, 0, 0], ![140, 1, 0], ![123, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-23, 1, 0], ![0, -23, 1], ![730, 150, -23]]]
  hmulB := by decide  
  f := ![![![2071, -90, 0], ![14670, 0, 0]], ![![1772, -77, 0], ![12552, 0, 0]], ![![1591, -69, 0], ![11270, 1, 0]]]
  g := ![![![1, 0, 0], ![-140, 163, 0], ![-123, 0, 163]], ![![-1, 1, 0], ![19, -23, 1], ![-107, 150, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-110, 23, 1]] ![![163, 0, 0], ![-23, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-3749, 163, 0]], ![![-17930, 3749, 163], ![3260, -489, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-23, 1, 0]]], ![![![-110, 23, 1]], ![![20, -3, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-88, -88, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-88, -88, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![79, 79, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-88, -88, 1], ![730, 62, -88], ![-64240, -12470, 62]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -79, 167]], ![![-1, -1, 1], ![46, 42, -88], ![-414, -104, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [89, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 166], [0, 1]]
 g := ![![[123, 152], [39, 93], [135, 65], [84], [4], [43, 114], [1]], ![[0, 15], [0, 74], [0, 102], [84], [4], [76, 53], [1]]]
 h' := ![![[75, 166], [36, 73], [9, 60], [88, 30], [7, 77], [14, 165], [78, 75], [0, 1]], ![[0, 1], [0, 94], [0, 107], [0, 137], [104, 90], [31, 2], [25, 92], [75, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [166, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [89, 92, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27922, 8216, 605]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119, -237, 605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-79, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-79, 1, 0]] 
 ![![167, 0, 0], ![88, 1, 0], ![105, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-79, 1, 0], ![0, -79, 1], ![730, 150, -79]]]
  hmulB := by decide  
  f := ![![![8375, -106, 0], ![17702, 0, 0]], ![![4504, -57, 0], ![9520, 0, 0]], ![![5331, -67, 0], ![11268, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 167, 0], ![-105, 0, 167]], ![![-1, 1, 0], ![41, -79, 1], ![-25, 150, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-88, -88, 1]] ![![167, 0, 0], ![-79, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-13193, 167, 0]], ![![-14696, -14696, 167], ![7682, 7014, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-79, 1, 0]]], ![![![-88, -88, 1]], ![![46, 42, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [40, 124, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 6, 170], [13, 166, 3], [0, 1]]
 g := ![![[129, 8, 138], [92, 49], [134, 172, 40], [142, 154, 4], [8, 6], [168, 43, 1], []], ![[138, 123, 149, 105], [96, 106], [66, 45, 26, 69], [61, 58, 104, 129], [23, 57], [117, 93, 111, 26], [5, 9]], ![[126, 94, 137, 99], [53, 151], [72, 161, 40, 20], [164, 106, 76, 50], [145, 37], [93, 7, 70, 108], [172, 9]]]
 h' := ![![[30, 6, 170], [135, 1, 151], [3, 8, 166], [29, 96, 46], [63, 91, 171], [27, 111, 122], [0, 0, 1], [0, 1]], ![[13, 166, 3], [162, 152, 151], [14, 63, 25], [163, 82, 82], [9, 56, 87], [8, 108, 24], [8, 72, 166], [30, 6, 170]], ![[0, 1], [48, 20, 44], [28, 102, 155], [165, 168, 45], [136, 26, 88], [153, 127, 27], [36, 101, 6], [13, 166, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 27], []]
 b := ![[], [150, 85, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [40, 124, 130, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83905, -54149, 346]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-485, -313, 2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [16, 87, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 158, 70], [83, 20, 109], [0, 1]]
 g := ![![[46, 87, 171], [169, 105, 27], [101, 83], [83, 89], [122, 136, 76], [123, 63, 1], []], ![[43, 113, 82, 4], [161, 11, 171, 31], [7, 144], [144, 169], [50, 136, 166, 100], [58, 104, 133, 76], [28, 67]], ![[87, 108, 109, 6], [94, 26, 104, 55], [70, 81], [90, 19], [107, 64, 38, 26], [115, 15, 35, 97], [168, 67]]]
 h' := ![![[159, 158, 70], [160, 100, 156], [146, 14, 122], [35, 91, 21], [17, 99, 39], [1, 105, 104], [0, 0, 1], [0, 1]], ![[83, 20, 109], [159, 15, 96], [96, 169, 19], [71, 57, 167], [103, 16, 13], [69, 100, 122], [131, 17, 20], [159, 158, 70]], ![[0, 1], [84, 64, 106], [100, 175, 38], [44, 31, 170], [54, 64, 127], [89, 153, 132], [84, 162, 158], [83, 20, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158, 57], []]
 b := ![[], [10, 167, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [16, 87, 116, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5916666, 2434937, 259550]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33054, 13603, 1450]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [118, 123, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 150, 154], [93, 30, 27], [0, 1]]
 g := ![![[34, 14, 180], [31, 67], [79, 16, 34], [69, 139], [127, 28, 29], [45, 63, 1], []], ![[10, 87, 136, 156], [66, 144], [91, 43, 155, 100], [64, 29], [48, 18, 152, 80], [36, 53, 41, 135], [179, 5]], ![[36, 72, 116, 165], [102, 73], [108, 155, 24, 101], [9, 1], [174, 166, 22, 25], [64, 162, 84, 64], [125, 5]]]
 h' := ![![[151, 150, 154], [98, 83, 19], [90, 144, 130], [105, 89, 45], [37, 0, 146], [120, 63, 36], [0, 0, 1], [0, 1]], ![[93, 30, 27], [6, 167, 139], [98, 32, 12], [47, 120, 33], [97, 154, 36], [30, 133, 103], [50, 68, 30], [151, 150, 154]], ![[0, 1], [136, 112, 23], [100, 5, 39], [88, 153, 103], [173, 27, 180], [104, 166, 42], [53, 113, 150], [93, 30, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 14], []]
 b := ![[], [126, 57, 148], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [118, 123, 118, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13226756, -1047990, 270414]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73076, -5790, 1494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-132, -20, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-132, -20, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![59, 171, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-132, -20, 1], ![730, 18, -20], ![-14600, -2270, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -171, 191]], ![![-1, -1, 1], ![10, 18, -20], ![-82, -28, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [14, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 190], [0, 1]]
 g := ![![[34, 104], [74, 9], [80, 138], [73, 162], [74, 147], [33, 50], [1]], ![[190, 87], [183, 182], [96, 53], [125, 29], [8, 44], [108, 141], [1]]]
 h' := ![![[97, 190], [110, 88], [26, 3], [124, 105], [110, 60], [111, 23], [177, 97], [0, 1]], ![[0, 1], [51, 103], [126, 188], [186, 86], [9, 131], [50, 168], [36, 94], [97, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [143, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [14, 94, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55, 310, 271]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-84, -241, 271]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![20, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![20, 1, 0]] 
 ![![191, 0, 0], ![20, 1, 0], ![173, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![20, 1, 0], ![0, 20, 1], ![730, 150, 20]]]
  hmulB := by decide  
  f := ![![![1521, 76, 0], ![-14516, 0, 0]], ![![140, 7, 0], ![-1336, 0, 0]], ![![1403, 70, 0], ![-13390, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 191, 0], ![-173, 0, 191]], ![![0, 1, 0], ![-3, 20, 1], ![-30, 150, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-132, -20, 1]] ![![191, 0, 0], ![20, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![3820, 191, 0]], ![![-25212, -3820, 191], ![-1910, -382, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![20, 1, 0]]], ![![![-132, -20, 1]], ![![-10, -2, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-69, 9, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-69, 9, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![124, 9, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-69, 9, 1], ![730, 81, 9], ![6570, 2080, 81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -9, 193]], ![![-1, 0, 1], ![-2, 0, 9], ![-18, 7, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [169, 181, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 192], [0, 1]]
 g := ![![[97, 8], [109], [1], [151], [181], [46], [12, 1]], ![[0, 185], [109], [1], [151], [181], [46], [24, 192]]]
 h' := ![![[12, 192], [103, 104], [31, 130], [134, 192], [62, 99], [93, 48], [95, 168], [0, 1]], ![[0, 1], [0, 89], [47, 63], [122, 1], [92, 94], [90, 145], [181, 25], [12, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119]]
 b := ![[], [29, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [169, 181, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6191, 1198, -17]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 7, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-9, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-9, 1, 0]] 
 ![![193, 0, 0], ![184, 1, 0], ![112, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-9, 1, 0], ![0, -9, 1], ![730, 150, -9]]]
  hmulB := by decide  
  f := ![![![424, -47, 0], ![9071, 0, 0]], ![![406, -45, 0], ![8686, 0, 0]], ![![244, -27, 0], ![5220, 1, 0]]]
  g := ![![![1, 0, 0], ![-184, 193, 0], ![-112, 0, 193]], ![![-1, 1, 0], ![8, -9, 1], ![-134, 150, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-69, 9, 1]] ![![193, 0, 0], ![-9, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-1737, 193, 0]], ![![-13317, 1737, 193], ![1351, 0, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-9, 1, 0]]], ![![![-69, 9, 1]], ![![7, 0, 0]]]]
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


lemma PB267I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB267I3 : PrimesBelowBoundCertificateInterval O 137 193 267 where
  m := 11
  g := ![1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB267I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
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
      exact NI157N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N1, I151N1, I157N1, I163N1, I167N1, I191N1, I193N1]
  Il := ![[], [I149N1], [I151N1], [I157N1], [I163N1], [I167N1], [], [], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
