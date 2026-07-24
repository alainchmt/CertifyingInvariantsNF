
import IdealArithmetic.Examples.NF3_1_603288_2.RI3_1_603288_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![42, 48, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![42, 48, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![42, 48, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![42, 48, 1], ![140, 21, 96], ![6720, -938, 21]]]
  hmulB := by decide  
  f := ![![![-41, -48, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -48, 139]], ![![0, 0, 1], ![-28, -33, 96], ![42, -14, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [40, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 138], [0, 1]]
 g := ![![[69, 29], [49, 127], [117], [53, 4], [36], [122], [1]], ![[93, 110], [87, 12], [117], [133, 135], [36], [122], [1]]]
 h' := ![![[20, 138], [125, 53], [20, 108], [104, 16], [28, 2], [56, 6], [99, 20], [0, 1]], ![[0, 1], [73, 86], [95, 31], [7, 123], [68, 137], [37, 133], [82, 119], [20, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [58, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [40, 119, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![320, -91, -138]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, 47, -138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![43, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![43, 1, 0]] 
 ![![139, 0, 0], ![43, 1, 0], ![118, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![43, 1, 0], ![0, 43, 2], ![140, -21, 43]]]
  hmulB := by decide  
  f := ![![![2452, 57, 0], ![-7923, 0, 0]], ![![774, 18, 0], ![-2501, 0, 0]], ![![2136, 28, -1], ![-6902, 70, 0]]]
  g := ![![![1, 0, 0], ![-43, 139, 0], ![-118, 0, 139]], ![![0, 1, 0], ![-15, 43, 2], ![-29, -21, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![42, 48, 1]] ![![139, 0, 0], ![43, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![5977, 139, 0]], ![![5838, 6672, 139], ![1946, 2085, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![43, 1, 0]]], ![![![42, 48, 1]], ![![14, 15, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![59, -67, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![59, -67, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![59, 82, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![59, -67, 1], ![140, 38, -134], ![-9380, 1477, 38]]]
  hmulB := by decide  
  f := ![![![-58, 67, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -82, 149]], ![![0, -1, 1], ![54, 74, -134], ![-78, -11, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [72, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 148], [0, 1]]
 g := ![![[94, 116], [39], [113, 25], [19], [109, 125], [95], [1]], ![[87, 33], [39], [28, 124], [19], [131, 24], [95], [1]]]
 h' := ![![[86, 148], [77, 50], [59, 121], [139, 5], [49, 67], [132, 107], [77, 86], [0, 1]], ![[0, 1], [56, 99], [35, 28], [122, 144], [0, 82], [96, 42], [23, 63], [86, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [59, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [72, 63, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1670, 760, 2]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 4, 2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-15, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-15, 1, 0]] 
 ![![149, 0, 0], ![134, 1, 0], ![111, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-15, 1, 0], ![0, -15, 2], ![140, -21, -15]]]
  hmulB := by decide  
  f := ![![![181, -12, 0], ![1788, 0, 0]], ![![166, -11, 0], ![1640, 0, 0]], ![![159, -3, -1], ![1572, 75, 0]]]
  g := ![![![1, 0, 0], ![-134, 149, 0], ![-111, 0, 149]], ![![-1, 1, 0], ![12, -15, 2], ![31, -21, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![59, -67, 1]] ![![149, 0, 0], ![-15, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-2235, 149, 0]], ![![8791, -9983, 149], ![-745, 1043, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-15, 1, 0]]], ![![![59, -67, 1]], ![![-5, 7, -1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-45, 32, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-45, 32, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![106, 32, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-45, 32, 1], ![140, -66, 64], ![4480, -602, -66]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -32, 151]], ![![-1, 0, 1], ![-44, -14, 64], ![76, 10, -66]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [25, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 150], [0, 1]]
 g := ![![[63, 145], [78, 49], [61, 18], [72], [138, 29], [148], [1]], ![[0, 6], [64, 102], [99, 133], [72], [65, 122], [148], [1]]]
 h' := ![![[86, 150], [13, 121], [136, 7], [88, 13], [23, 125], [96, 123], [126, 86], [0, 1]], ![[0, 1], [0, 30], [134, 144], [149, 138], [52, 26], [104, 28], [123, 65], [86, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [71, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [25, 65, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-319, 49, 44]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -9, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-64, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-64, 1, 0]] 
 ![![151, 0, 0], ![87, 1, 0], ![66, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-64, 1, 0], ![0, -64, 2], ![140, -21, -64]]]
  hmulB := by decide  
  f := ![![![5441, -85, 0], ![12835, 0, 0]], ![![3201, -50, 0], ![7551, 0, 0]], ![![2446, -6, -1], ![5770, 76, 0]]]
  g := ![![![1, 0, 0], ![-87, 151, 0], ![-66, 0, 151]], ![![-1, 1, 0], ![36, -64, 2], ![41, -21, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-45, 32, 1]] ![![151, 0, 0], ![-64, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-9664, 151, 0]], ![![-6795, 4832, 151], ![3020, -2114, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-64, 1, 0]]], ![![![-45, 32, 1]], ![![20, -14, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-64, -6, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-64, -6, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![93, 151, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-64, -6, 1], ![140, -85, -12], ![-840, 196, -85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -151, 157]], ![![-1, -1, 1], ![8, 11, -12], ![45, 83, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [145, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 156], [0, 1]]
 g := ![![[82, 13], [148], [141, 145], [76, 146], [49, 145], [37], [1]], ![[0, 144], [148], [108, 12], [85, 11], [16, 12], [37], [1]]]
 h' := ![![[42, 156], [18, 22], [122, 84], [127, 107], [117, 60], [117, 50], [12, 42], [0, 1]], ![[0, 1], [0, 135], [39, 73], [68, 50], [125, 97], [19, 107], [49, 115], [42, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [91, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [145, 115, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-579, 873, -538]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![315, 523, -538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![12, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![12, 1, 0]] 
 ![![157, 0, 0], ![12, 1, 0], ![85, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![12, 1, 0], ![0, 12, 2], ![140, -21, 12]]]
  hmulB := by decide  
  f := ![![![1465, 122, 0], ![-19154, 0, 0]], ![![108, 9, 0], ![-1412, 0, 0]], ![![793, 60, -1], ![-10368, 79, 0]]]
  g := ![![![1, 0, 0], ![-12, 157, 0], ![-85, 0, 157]], ![![0, 1, 0], ![-2, 12, 2], ![-4, -21, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-64, -6, 1]] ![![157, 0, 0], ![12, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![1884, 157, 0]], ![![-10048, -942, 157], ![-628, -157, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![12, 1, 0]]], ![![![-64, -6, 1]], ![![-4, -1, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-39, 40, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-39, 40, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![124, 40, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-39, 40, 1], ![140, -60, 80], ![5600, -770, -60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -40, 163]], ![![-1, 0, 1], ![-60, -20, 80], ![80, 10, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [162, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 162], [0, 1]]
 g := ![![[62, 111], [49, 74], [143], [16], [74], [146, 95], [1]], ![[98, 52], [73, 89], [143], [16], [74], [5, 68], [1]]]
 h' := ![![[62, 162], [49, 130], [21, 20], [81, 44], [37, 159], [146, 20], [1, 62], [0, 1]], ![[0, 1], [122, 33], [120, 143], [38, 119], [115, 4], [82, 143], [96, 101], [62, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [106, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [162, 101, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442, -73, -120]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![94, 29, -120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-80, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-80, 1, 0]] 
 ![![163, 0, 0], ![83, 1, 0], ![60, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-80, 1, 0], ![0, -80, 2], ![140, -21, -80]]]
  hmulB := by decide  
  f := ![![![11041, -138, 0], ![22494, 0, 0]], ![![5681, -71, 0], ![11574, 0, 0]], ![![4180, -12, -1], ![8516, 82, 0]]]
  g := ![![![1, 0, 0], ![-83, 163, 0], ![-60, 0, 163]], ![![-1, 1, 0], ![40, -80, 2], ![41, -21, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-39, 40, 1]] ![![163, 0, 0], ![-80, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-13040, 163, 0]], ![![-6357, 6520, 163], ![3260, -3260, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-80, 1, 0]]], ![![![-39, 40, 1]], ![![20, -20, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![86, 28, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![86, 28, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![86, 28, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![86, 28, 1], ![140, 65, 56], ![3920, -518, 65]]]
  hmulB := by decide  
  f := ![![![-85, -28, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -28, 167]], ![![0, 0, 1], ![-28, -9, 56], ![-10, -14, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [27, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 166], [0, 1]]
 g := ![![[0, 99], [0, 14], [], [], [47], [], [1]], ![[0, 68], [0, 153], [], [], [47], [], [1]]]
 h' := ![![[0, 166], [0, 123], [0, 66], [147], [67], [0, 61], [140], [0, 1]], ![[0, 1], [0, 44], [0, 101], [147], [67], [0, 106], [140], [0, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [0, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [27, 0, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5348, -690, 703]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-330, -122, 703]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-56, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-56, 1, 0]] 
 ![![167, 0, 0], ![111, 1, 0], ![102, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-56, 1, 0], ![0, -56, 2], ![140, -21, -56]]]
  hmulB := by decide  
  f := ![![![281, -5, 0], ![835, 0, 0]], ![![225, -4, 0], ![669, 0, 0]], ![![234, 24, -1], ![696, 84, 0]]]
  g := ![![![1, 0, 0], ![-111, 167, 0], ![-102, 0, 167]], ![![-1, 1, 0], ![36, -56, 2], ![49, -21, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![86, 28, 1]] ![![167, 0, 0], ![-56, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-9352, 167, 0]], ![![14362, 4676, 167], ![-4676, -1503, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-56, 1, 0]]], ![![![86, 28, 1]], ![![-28, -9, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [129, 95, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 74, 24], [45, 98, 149], [0, 1]]
 g := ![![[165, 8, 135], [154, 33], [157, 51, 81], [84, 170, 160], [160, 41], [42, 39, 1], []], ![[99, 81, 168, 160], [151, 57], [94, 106, 160, 122], [144, 69, 9, 43], [113, 47], [64, 0, 104, 60], [66, 57]], ![[116, 140, 26, 116], [118, 126], [9, 50, 111, 109], [138, 82, 73, 169], [47, 57], [149, 147, 139, 56], [114, 57]]]
 h' := ![![[167, 74, 24], [0, 7, 57], [161, 121, 129], [63, 115, 164], [31, 80, 81], [118, 148, 53], [0, 0, 1], [0, 1]], ![[45, 98, 149], [74, 158, 45], [171, 72, 149], [74, 17, 148], [162, 9, 170], [42, 128, 96], [172, 21, 98], [167, 74, 24]], ![[0, 1], [119, 8, 71], [109, 153, 68], [170, 41, 34], [111, 84, 95], [43, 70, 24], [121, 152, 74], [45, 98, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 131], []]
 b := ![[], [155, 22, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [129, 95, 134, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-138573, 27161, 1730]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-801, 157, 10]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![17, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![17, 1, 0]] 
 ![![179, 0, 0], ![17, 1, 0], ![124, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![17, 1, 0], ![0, 17, 2], ![140, -21, 17]]]
  hmulB := by decide  
  f := ![![![2211, 130, 0], ![-23270, 0, 0]], ![![187, 11, 0], ![-1968, 0, 0]], ![![1540, 82, -1], ![-16208, 90, 0]]]
  g := ![![![1, 0, 0], ![-17, 179, 0], ![-124, 0, 179]], ![![0, 1, 0], ![-3, 17, 2], ![-9, -21, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![69, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![69, 1, 0]] 
 ![![179, 0, 0], ![69, 1, 0], ![36, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![69, 1, 0], ![0, 69, 2], ![140, -21, 69]]]
  hmulB := by decide  
  f := ![![![4141, 60, 0], ![-10740, 0, 0]], ![![1587, 23, 0], ![-4116, 0, 0]], ![![738, -24, -1], ![-1914, 90, 0]]]
  g := ![![![1, 0, 0], ![-69, 179, 0], ![-36, 0, 179]], ![![0, 1, 0], ![-27, 69, 2], ![-5, -21, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-86, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-86, 1, 0]] 
 ![![179, 0, 0], ![93, 1, 0], ![61, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-86, 1, 0], ![0, -86, 2], ![140, -21, -86]]]
  hmulB := by decide  
  f := ![![![11869, -138, 0], ![24702, 0, 0]], ![![6107, -71, 0], ![12710, 0, 0]], ![![4063, -4, -1], ![8456, 90, 0]]]
  g := ![![![1, 0, 0], ![-93, 179, 0], ![-61, 0, 179]], ![![-1, 1, 0], ![44, -86, 2], ![41, -21, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![17, 1, 0]] ![![179, 0, 0], ![69, 1, 0]]
  ![![179, 0, 0], ![-40, 43, 1]] where
 M := ![![![32041, 0, 0], ![12351, 179, 0]], ![![3043, 179, 0], ![1173, 86, 2]]]
 hmul := by decide  
 g := ![![![![179, 0, 0], ![0, 0, 0]], ![![69, 1, 0], ![0, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![7, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-40, 43, 1]] ![![179, 0, 0], ![-86, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-15394, 179, 0]], ![![-7160, 7697, 179], ![3580, -3759, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-86, 1, 0]]], ![![![-40, 43, 1]], ![![20, -21, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [60, 61, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 85, 129], [153, 95, 52], [0, 1]]
 g := ![![[13, 127, 27], [5, 42], [14, 123, 154], [125, 12], [31, 134, 106], [117, 97, 1], []], ![[61, 88, 13, 70], [116, 108], [40, 143, 86, 156], [25, 138], [171, 117, 81, 154], [168, 126, 75, 33], [48, 170]], ![[155, 104, 58, 133], [10, 165], [64, 115, 70, 38], [64, 167], [40, 117, 175, 172], [116, 41, 78, 125], [125, 170]]]
 h' := ![![[125, 85, 129], [124, 104, 82], [65, 10, 59], [68, 55, 71], [131, 97, 115], [39, 75, 123], [0, 0, 1], [0, 1]], ![[153, 95, 52], [88, 76, 29], [129, 36, 17], [141, 146, 84], [66, 170, 89], [177, 107, 2], [75, 158, 95], [125, 85, 129]], ![[0, 1], [179, 1, 70], [112, 135, 105], [75, 161, 26], [117, 95, 158], [127, 180, 56], [162, 23, 85], [153, 95, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 15], []]
 b := ![[], [10, 108, 143], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [60, 61, 84, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90500, -905, -1810]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![500, -5, -10]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [98, 97, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 113, 156], [173, 77, 35], [0, 1]]
 g := ![![[24, 91, 39], [112, 22, 184], [58, 181, 156], [66, 116, 120], [67, 187, 20], [66, 113, 1], []], ![[70, 61, 150, 85], [117, 17, 86, 177], [141, 49, 36, 144], [149, 182, 133, 24], [90, 107, 185, 107], [46, 112, 141, 102], [62, 79]], ![[119, 190, 170, 82], [36, 131, 43, 188], [39, 130, 130, 83], [72, 101, 165, 164], [7, 126, 155, 176], [145, 179, 31, 166], [183, 79]]]
 h' := ![![[131, 113, 156], [102, 174, 82], [46, 41, 152], [26, 20, 27], [119, 108, 104], [26, 96, 28], [0, 0, 1], [0, 1]], ![[173, 77, 35], [168, 125, 33], [178, 166, 146], [161, 78, 42], [97, 50, 26], [1, 68, 133], [7, 188, 77], [131, 113, 156]], ![[0, 1], [157, 83, 76], [26, 175, 84], [168, 93, 122], [144, 33, 61], [99, 27, 30], [153, 3, 113], [173, 77, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 132], []]
 b := ![[], [1, 57, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [98, 97, 78, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-318588, 139430, -27886]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1668, 730, -146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-80, -25, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-80, -25, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![113, 168, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-80, -25, 1], ![140, -101, -50], ![-3500, 595, -101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -168, 193]], ![![-1, -1, 1], ![30, 43, -50], ![41, 91, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [104, 158, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 192], [0, 1]]
 g := ![![[124, 107], [49], [121], [95], [96], [18], [35, 1]], ![[9, 86], [49], [121], [95], [96], [18], [70, 192]]]
 h' := ![![[35, 192], [178, 140], [177, 7], [71, 11], [84, 148], [15, 176], [27, 156], [0, 1]], ![[0, 1], [60, 53], [36, 186], [70, 182], [53, 45], [192, 17], [83, 37], [35, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [147, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [104, 158, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2047, -72, 165]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86, -144, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![50, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![50, 1, 0]] 
 ![![193, 0, 0], ![50, 1, 0], ![101, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![50, 1, 0], ![0, 50, 2], ![140, -21, 50]]]
  hmulB := by decide  
  f := ![![![4801, 96, 0], ![-18528, 0, 0]], ![![1250, 25, 0], ![-4824, 0, 0]], ![![2457, 24, -1], ![-9482, 97, 0]]]
  g := ![![![1, 0, 0], ![-50, 193, 0], ![-101, 0, 193]], ![![0, 1, 0], ![-14, 50, 2], ![-20, -21, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-80, -25, 1]] ![![193, 0, 0], ![50, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![9650, 193, 0]], ![![-15440, -4825, 193], ![-3860, -1351, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![50, 1, 0]]], ![![![-80, -25, 1]], ![![-20, -7, 0]]]]
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


lemma PB220I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB220I3 : PrimesBelowBoundCertificateInterval O 137 193 220 where
  m := 11
  g := ![2, 2, 2, 2, 2, 2, 1, 3, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB220I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0]
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
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![5929741]
    · exact ![6967871]
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
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N1, I157N1, I163N1, I167N1, I179N0, I179N1, I179N2, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N1], [I167N1], [], [I179N0, I179N1, I179N2], [], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
