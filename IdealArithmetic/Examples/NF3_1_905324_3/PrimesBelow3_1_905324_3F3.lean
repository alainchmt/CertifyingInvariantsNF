
import IdealArithmetic.Examples.NF3_1_905324_3.RI3_1_905324_3
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [131, 81, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 37, 108], [99, 101, 31], [0, 1]]
 g := ![![[78, 21, 129], [134, 57, 5], [6, 122], [47, 6, 116], [104, 64], [28, 1], []], ![[13, 84, 34, 110], [68, 66, 96, 102], [72, 13], [126, 119, 55, 70], [95, 67], [31, 54], [11, 127]], ![[100, 61, 95, 64], [88, 81, 22, 65], [1, 107], [54, 22, 26, 45], [68, 57], [44, 118], [88, 127]]]
 h' := ![![[68, 37, 108], [99, 134, 95], [61, 44, 127], [98, 19, 20], [134, 7, 106], [85, 103, 8], [0, 0, 1], [0, 1]], ![[99, 101, 31], [97, 33, 20], [24, 70, 65], [137, 10, 41], [99, 75, 64], [27, 31, 117], [125, 14, 101], [68, 37, 108]], ![[0, 1], [115, 111, 24], [121, 25, 86], [104, 110, 78], [133, 57, 108], [80, 5, 14], [80, 125, 37], [99, 101, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 90], []]
 b := ![[], [119, 35, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [131, 81, 111, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14873, 20989, -2224]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![107, 151, -16]
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


def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![39, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![39, 1, 0]] 
 ![![149, 0, 0], ![39, 1, 0], ![118, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![39, 1, 0], ![0, 39, 1], ![182, -14, 39]]]
  hmulB := by decide  
  f := ![![![2692, 69, 0], ![-10281, 0, 0]], ![![702, 18, 0], ![-2681, 0, 0]], ![![2078, 53, 0], ![-7936, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 149, 0], ![-118, 0, 149]], ![![0, 1, 0], ![-11, 39, 1], ![-26, -14, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![55, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![55, 1, 0]] 
 ![![149, 0, 0], ![55, 1, 0], ![104, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![55, 1, 0], ![0, 55, 1], ![182, -14, 55]]]
  hmulB := by decide  
  f := ![![![2861, 52, 0], ![-7748, 0, 0]], ![![1045, 19, 0], ![-2830, 0, 0]], ![![1946, 35, 0], ![-5270, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 149, 0], ![-104, 0, 149]], ![![0, 1, 0], ![-21, 55, 1], ![-32, -14, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![39, 1, 0]] ![![149, 0, 0], ![55, 1, 0]]
  ![![149, 0, 0], ![59, -55, 1]] where
 M := ![![![22201, 0, 0], ![8195, 149, 0]], ![![5811, 149, 0], ![2145, 94, 1]]]
 hmul := by decide  
 g := ![![![![90, 55, -1], ![149, 0, 0]], ![![-4, 56, -1], ![149, 0, 0]]], ![![![-20, 56, -1], ![149, 0, 0]], ![![-45, 56, -1], ![150, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![59, -55, 1]] ![![149, 0, 0], ![55, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![8195, 149, 0]], ![![8791, -8195, 149], ![3427, -2980, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![55, 1, 0]]], ![![![59, -55, 1]], ![![23, -20, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![4, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![4, 1, 0]] 
 ![![151, 0, 0], ![4, 1, 0], ![135, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![4, 1, 0], ![0, 4, 1], ![182, -14, 4]]]
  hmulB := by decide  
  f := ![![![145, 36, 0], ![-5436, 0, 0]], ![![-4, -1, 0], ![152, 0, 0]], ![![129, 32, 0], ![-4836, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 151, 0], ![-135, 0, 151]], ![![0, 1, 0], ![-1, 4, 1], ![-2, -14, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![25, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![25, 1, 0]] 
 ![![151, 0, 0], ![25, 1, 0], ![130, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![25, 1, 0], ![0, 25, 1], ![182, -14, 25]]]
  hmulB := by decide  
  f := ![![![2476, 99, 0], ![-14949, 0, 0]], ![![400, 16, 0], ![-2415, 0, 0]], ![![2130, 85, 0], ![-12860, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 151, 0], ![-130, 0, 151]], ![![0, 1, 0], ![-5, 25, 1], ![-18, -14, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-29, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-29, 1, 0]] 
 ![![151, 0, 0], ![122, 1, 0], ![65, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-29, 1, 0], ![0, -29, 1], ![182, -14, -29]]]
  hmulB := by decide  
  f := ![![![3858, -133, 0], ![20083, 0, 0]], ![![3162, -109, 0], ![16460, 0, 0]], ![![1688, -58, 0], ![8787, 1, 0]]]
  g := ![![![1, 0, 0], ![-122, 151, 0], ![-65, 0, 151]], ![![-1, 1, 0], ![23, -29, 1], ![25, -14, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![4, 1, 0]] ![![151, 0, 0], ![25, 1, 0]]
  ![![151, 0, 0], ![-51, 29, 1]] where
 M := ![![![22801, 0, 0], ![3775, 151, 0]], ![![604, 151, 0], ![100, 29, 1]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-51, 29, 1]] ![![151, 0, 0], ![-29, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-4379, 151, 0]], ![![-7701, 4379, 151], ![1661, -906, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-29, 1, 0]]], ![![![-51, 29, 1]], ![![11, -6, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![4, -33, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![4, -33, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![4, 124, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![4, -33, 1], ![182, -10, -33], ![-6006, 644, -10]]]
  hmulB := by decide  
  f := ![![![-3, 33, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -124, 157]], ![![0, -1, 1], ![2, 26, -33], ![-38, 12, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [117, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 156], [0, 1]]
 g := ![![[99, 51], [9], [124, 147], [38, 146], [11, 144], [126], [1]], ![[0, 106], [9], [88, 10], [124, 11], [27, 13], [126], [1]]]
 h' := ![![[35, 156], [60, 88], [93, 3], [107, 124], [126, 97], [46, 145], [40, 35], [0, 1]], ![[0, 1], [0, 69], [41, 154], [51, 33], [67, 60], [97, 12], [9, 122], [35, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [38, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [117, 122, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2188, 1566, 238]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -178, 238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![33, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![33, 1, 0]] 
 ![![157, 0, 0], ![33, 1, 0], ![10, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![33, 1, 0], ![0, 33, 1], ![182, -14, 33]]]
  hmulB := by decide  
  f := ![![![2905, 88, 0], ![-13816, 0, 0]], ![![561, 17, 0], ![-2668, 0, 0]], ![![172, 5, 0], ![-818, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 157, 0], ![-10, 0, 157]], ![![0, 1, 0], ![-7, 33, 1], ![2, -14, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![4, -33, 1]] ![![157, 0, 0], ![33, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![5181, 157, 0]], ![![628, -5181, 157], ![314, -1099, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![33, 1, 0]]], ![![![4, -33, 1]], ![![2, -7, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![40, 29, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![40, 29, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![40, 29, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![40, 29, 1], ![182, 26, 29], ![5278, -224, 26]]]
  hmulB := by decide  
  f := ![![![-39, -29, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -29, 163]], ![![0, 0, 1], ![-6, -5, 29], ![26, -6, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [80, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 162], [0, 1]]
 g := ![![[40, 43], [3, 4], [150], [61], [87], [42, 14], [1]], ![[12, 120], [80, 159], [150], [61], [87], [67, 149], [1]]]
 h' := ![![[60, 162], [86, 80], [63, 2], [162, 98], [106, 77], [63, 139], [83, 60], [0, 1]], ![[0, 1], [159, 83], [20, 161], [11, 65], [162, 86], [90, 24], [97, 103], [60, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [3, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [80, 103, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2780, 185, 12]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -1, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-29, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-29, 1, 0]] 
 ![![163, 0, 0], ![134, 1, 0], ![137, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-29, 1, 0], ![0, -29, 1], ![182, -14, -29]]]
  hmulB := by decide  
  f := ![![![1654, -57, 0], ![9291, 0, 0]], ![![1364, -47, 0], ![7662, 0, 0]], ![![1398, -48, 0], ![7853, 1, 0]]]
  g := ![![![1, 0, 0], ![-134, 163, 0], ![-137, 0, 163]], ![![-1, 1, 0], ![23, -29, 1], ![37, -14, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![40, 29, 1]] ![![163, 0, 0], ![-29, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4727, 163, 0]], ![![6520, 4727, 163], ![-978, -815, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-29, 1, 0]]], ![![![40, 29, 1]], ![![-6, -5, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![65, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![65, 1, 0]] 
 ![![167, 0, 0], ![65, 1, 0], ![117, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![65, 1, 0], ![0, 65, 1], ![182, -14, 65]]]
  hmulB := by decide  
  f := ![![![1041, 16, 0], ![-2672, 0, 0]], ![![325, 5, 0], ![-834, 0, 0]], ![![741, 11, 0], ![-1902, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 167, 0], ![-117, 0, 167]], ![![0, 1, 0], ![-26, 65, 1], ![-39, -14, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-64, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-64, 1, 0]] 
 ![![167, 0, 0], ![103, 1, 0], ![79, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-64, 1, 0], ![0, -64, 1], ![182, -14, -64]]]
  hmulB := by decide  
  f := ![![![8513, -133, 0], ![22211, 0, 0]], ![![5249, -82, 0], ![13695, 0, 0]], ![![4057, -63, 0], ![10585, 1, 0]]]
  g := ![![![1, 0, 0], ![-103, 167, 0], ![-79, 0, 167]], ![![-1, 1, 0], ![39, -64, 1], ![40, -14, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![167, 0, 0], ![166, 1, 0], ![166, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![182, -14, -1]]]
  hmulB := by decide  
  f := ![![![15, 1, 1]], ![![16, 1, 1]], ![![16, 2, 1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![16, -14, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![65, 1, 0]] ![![167, 0, 0], ![-64, 1, 0]]
  ![![15, 1, 1]] where
 M := ![![![27889, 0, 0], ![-10688, 167, 0]], ![![10855, 167, 0], ![-4160, 1, 1]]]
 hmul := by decide  
 g := ![![![![-167, 167, 0]], ![![64, -65, 1]]], ![![![-65, 64, 1]], ![![26, -25, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![15, 1, 1]] ![![-1, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [138, 127, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 133, 132], [16, 39, 41], [0, 1]]
 g := ![![[91, 43, 96], [71, 169], [103, 3, 88], [145, 63, 31], [12, 37], [3, 87, 1], []], ![[139, 98, 156, 55], [134, 23], [20, 76, 9, 4], [162, 57, 14, 142], [85, 67], [56, 166, 136, 92], [55, 124]], ![[121, 15, 109, 109], [160, 1], [61, 133, 102, 164], [144, 153, 33, 92], [55, 56], [38, 126, 24, 33], [146, 124]]]
 h' := ![![[71, 133, 132], [155, 81, 142], [145, 76, 13], [58, 89, 61], [27, 75, 107], [105, 69, 146], [0, 0, 1], [0, 1]], ![[16, 39, 41], [155, 6, 141], [84, 147, 159], [14, 3, 114], [67, 116, 60], [129, 56, 97], [46, 152, 39], [71, 133, 132]], ![[0, 1], [147, 86, 63], [16, 123, 1], [108, 81, 171], [164, 155, 6], [90, 48, 103], [3, 21, 133], [16, 39, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 114], []]
 b := ![[], [70, 14, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [138, 127, 86, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1059798, 294792, -12283]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6126, 1704, -71]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![94, -59, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![94, -59, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![94, 120, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![94, -59, 1], ![182, 80, -59], ![-10738, 1008, 80]]]
  hmulB := by decide  
  f := ![![![-93, 59, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -120, 179]], ![![0, -1, 1], ![32, 40, -59], ![-102, -48, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [156, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 178], [0, 1]]
 g := ![![[150, 70], [115, 173], [117], [139], [11, 169], [152, 74], [1]], ![[0, 109], [0, 6], [117], [139], [58, 10], [19, 105], [1]]]
 h' := ![![[49, 178], [139, 41], [123, 129], [81, 98], [74, 26], [95, 13], [23, 49], [0, 1]], ![[0, 1], [0, 138], [0, 50], [50, 81], [95, 153], [16, 166], [97, 130], [49, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [10, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [156, 130, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![520, 24, -143]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 96, -143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![59, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![59, 1, 0]] 
 ![![179, 0, 0], ![59, 1, 0], ![99, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![59, 1, 0], ![0, 59, 1], ![182, -14, 59]]]
  hmulB := by decide  
  f := ![![![3659, 62, 0], ![-11098, 0, 0]], ![![1121, 19, 0], ![-3400, 0, 0]], ![![1967, 33, 0], ![-5966, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 179, 0], ![-99, 0, 179]], ![![0, 1, 0], ![-20, 59, 1], ![-27, -14, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![94, -59, 1]] ![![179, 0, 0], ![59, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![10561, 179, 0]], ![![16826, -10561, 179], ![5728, -3401, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![59, 1, 0]]], ![![![94, -59, 1]], ![![32, -19, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [16, 72, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 74, 26], [36, 106, 155], [0, 1]]
 g := ![![[83, 3, 82], [81, 137], [180, 152, 165], [58, 65], [96, 66, 156], [10, 156, 1], []], ![[11, 70, 113, 151], [30, 15], [70, 128, 101, 63], [136, 99], [151, 102, 51, 120], [168, 80, 131, 2], [161, 133]], ![[37, 8, 31, 123], [30, 168], [71, 0, 75, 78], [39, 144], [161, 112, 49, 2], [91, 31, 35, 71], [32, 133]]]
 h' := ![![[120, 74, 26], [46, 6, 156], [16, 36, 104], [119, 46, 76], [93, 75, 80], [21, 42, 86], [0, 0, 1], [0, 1]], ![[36, 106, 155], [15, 80, 40], [155, 8, 14], [168, 29, 21], [57, 54, 113], [180, 132, 72], [59, 58, 106], [120, 74, 26]], ![[0, 1], [29, 95, 166], [131, 137, 63], [0, 106, 84], [172, 52, 169], [177, 7, 23], [60, 123, 74], [36, 106, 155]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 65], []]
 b := ![[], [128, 95, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [16, 72, 25, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1329988, 99731, 5249]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7348, 551, 29]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [152, 188, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 72, 104], [17, 118, 87], [0, 1]]
 g := ![![[10, 99, 160], [49, 180, 120], [124, 0, 69], [46, 187, 5], [88, 102, 184], [55, 25, 1], []], ![[15, 3, 184, 5], [114, 87, 169, 60], [159, 158, 148, 115], [12, 157, 3, 23], [147, 164, 79, 72], [25, 83, 122, 125], [22, 120]], ![[53, 94, 75, 62], [21, 7, 19, 145], [159, 21, 99, 175], [53, 92, 160, 132], [118, 136, 45, 176], [15, 185, 143, 57], [39, 120]]]
 h' := ![![[8, 72, 104], [1, 1, 55], [61, 76, 87], [75, 18, 159], [185, 66, 177], [44, 185, 152], [0, 0, 1], [0, 1]], ![[17, 118, 87], [104, 144, 100], [90, 33, 25], [129, 122, 6], [29, 108, 55], [137, 83, 122], [158, 168, 118], [8, 72, 104]], ![[0, 1], [57, 46, 36], [102, 82, 79], [143, 51, 26], [33, 17, 150], [22, 114, 108], [91, 23, 72], [17, 118, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 187], []]
 b := ![[], [109, 72, 169], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [152, 188, 166, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-229009, 44503, 1146]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1199, 233, 6]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-29, 27, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-29, 27, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![164, 27, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-29, 27, 1], ![182, -43, 27], ![4914, -196, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-164, -27, 193]], ![![-1, 0, 1], ![-22, -4, 27], ![62, 5, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [76, 190, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 192], [0, 1]]
 g := ![![[99, 54], [190], [36], [186], [32], [50], [3, 1]], ![[68, 139], [190], [36], [186], [32], [50], [6, 192]]]
 h' := ![![[3, 192], [77, 61], [87, 169], [182, 6], [187, 46], [127, 15], [158, 126], [0, 1]], ![[0, 1], [67, 132], [15, 24], [7, 187], [132, 147], [172, 178], [150, 67], [3, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [17, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [76, 190, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![804, 862, 325]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-272, -41, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-27, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-27, 1, 0]] 
 ![![193, 0, 0], ![166, 1, 0], ![43, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-27, 1, 0], ![0, -27, 1], ![182, -14, -27]]]
  hmulB := by decide  
  f := ![![![4186, -155, 0], ![29915, 0, 0]], ![![3592, -133, 0], ![25670, 0, 0]], ![![922, -34, 0], ![6589, 1, 0]]]
  g := ![![![1, 0, 0], ![-166, 193, 0], ![-43, 0, 193]], ![![-1, 1, 0], ![23, -27, 1], ![19, -14, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-29, 27, 1]] ![![193, 0, 0], ![-27, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-5211, 193, 0]], ![![-5597, 5211, 193], ![965, -772, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-27, 1, 0]]], ![![![-29, 27, 1]], ![![5, -4, 0]]]]
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


lemma PB270I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB270I3 : PrimesBelowBoundCertificateInterval O 137 193 270 where
  m := 11
  g := ![1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB270I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![32041, 179]
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
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
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
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
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
  β := ![I149N0, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I167N0, I167N1, I167N2, I179N1, I193N1]
  Il := ![[], [I149N0, I149N1, I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [I167N0, I167N1, I167N2], [], [I179N1], [], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
