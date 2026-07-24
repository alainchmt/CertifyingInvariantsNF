
import IdealArithmetic.Examples.NF3_1_329427_1.RI3_1_329427_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![25, 50, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![25, 50, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![25, 50, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![25, 50, 1], ![112, 85, 99], ![5488, 551, -14]]]
  hmulB := by decide  
  f := ![![![-24, -50, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -50, 139]], ![![0, 0, 1], ![-17, -35, 99], ![42, 9, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [118, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 138], [0, 1]]
 g := ![![[64, 86], [13, 100], [81], [115, 67], [67], [31], [1]], ![[0, 53], [0, 39], [81], [91, 72], [67], [31], [1]]]
 h' := ![![[93, 138], [134, 15], [96, 129], [52, 9], [0, 22], [119, 117], [21, 93], [0, 1]], ![[0, 1], [0, 124], [0, 10], [55, 130], [100, 117], [19, 22], [52, 46], [93, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [83, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [118, 46, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![454, 491, -43]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 19, -43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![40, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![40, 1, 0]] 
 ![![139, 0, 0], ![40, 1, 0], ![14, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![40, 1, 0], ![0, 41, 2], ![112, 10, 39]]]
  hmulB := by decide  
  f := ![![![1961, 49, 0], ![-6811, 0, 0]], ![![520, 13, 0], ![-1806, 0, 0]], ![![186, -16, -1], ![-646, 70, 0]]]
  g := ![![![1, 0, 0], ![-40, 139, 0], ![-14, 0, 139]], ![![0, 1, 0], ![-12, 41, 2], ![-6, 10, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![25, 50, 1]] ![![139, 0, 0], ![40, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![5560, 139, 0]], ![![3475, 6950, 139], ![1112, 2085, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![40, 1, 0]]], ![![![25, 50, 1]], ![![8, 15, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-11, -52, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-11, -52, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![138, 97, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-11, -52, 1], ![112, -53, -105], ![-5936, -469, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-138, -97, 149]], ![![-1, -1, 1], ![98, 68, -105], ![-88, -37, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [147, 21, 1] where
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
 g := ![![[64, 76], [127], [], [130], [130, 125], [143], [1]], ![[107, 73], [127], [], [130], [38, 24], [143], [1]]]
 h' := ![![[128, 148], [105, 15], [0, 53], [65], [111, 117], [141, 42], [2, 128], [0, 1]], ![[0, 1], [88, 134], [79, 96], [65], [38, 32], [4, 107], [145, 21], [128, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [64, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [147, 21, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-769, 916, 246]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-233, -154, 246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-44, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-44, 1, 0]] 
 ![![149, 0, 0], ![105, 1, 0], ![97, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-44, 1, 0], ![0, -43, 2], ![112, 10, -45]]]
  hmulB := by decide  
  f := ![![![5061, -115, 0], ![17135, 0, 0]], ![![3521, -80, 0], ![11921, 0, 0]], ![![3329, -54, -1], ![11271, 75, 0]]]
  g := ![![![1, 0, 0], ![-105, 149, 0], ![-97, 0, 149]], ![![-1, 1, 0], ![29, -43, 2], ![23, 10, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-11, -52, 1]] ![![149, 0, 0], ![-44, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-6556, 149, 0]], ![![-1639, -7748, 149], ![596, 2235, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-44, 1, 0]]], ![![![-11, -52, 1]], ![![4, 15, -1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![57, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![57, 1, 0]] 
 ![![151, 0, 0], ![57, 1, 0], ![8, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![57, 1, 0], ![0, 58, 2], ![112, 10, 56]]]
  hmulB := by decide  
  f := ![![![1084, 19, 0], ![-2869, 0, 0]], ![![342, 6, 0], ![-905, 0, 0]], ![![-46, -30, -1], ![122, 76, 0]]]
  g := ![![![1, 0, 0], ![-57, 151, 0], ![-8, 0, 151]], ![![0, 1, 0], ![-22, 58, 2], ![-6, 10, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-29, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-29, 1, 0]] 
 ![![151, 0, 0], ![122, 1, 0], ![47, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-29, 1, 0], ![0, -28, 2], ![112, 10, -30]]]
  hmulB := by decide  
  f := ![![![3684, -127, 0], ![19177, 0, 0]], ![![2988, -103, 0], ![15554, 0, 0]], ![![1192, -27, -1], ![6205, 76, 0]]]
  g := ![![![1, 0, 0], ![-122, 151, 0], ![-47, 0, 151]], ![![-1, 1, 0], ![22, -28, 2], ![2, 10, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-28, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-28, 1, 0]] 
 ![![151, 0, 0], ![123, 1, 0], ![75, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-28, 1, 0], ![0, -27, 2], ![112, 10, -29]]]
  hmulB := by decide  
  f := ![![![981, -35, 0], ![5285, 0, 0]], ![![841, -30, 0], ![4531, 0, 0]], ![![521, -5, -1], ![2807, 76, 0]]]
  g := ![![![1, 0, 0], ![-123, 151, 0], ![-75, 0, 151]], ![![-1, 1, 0], ![21, -27, 2], ![7, 10, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![57, 1, 0]] ![![151, 0, 0], ![-29, 1, 0]]
  ![![151, 0, 0], ![4, -61, 1]] where
 M := ![![![22801, 0, 0], ![-4379, 151, 0]], ![![8607, 151, 0], ![-1653, 29, 2]]]
 hmul := by decide  
 g := ![![![![147, 61, -1], ![151, 0, 0]], ![![-29, 1, 0], ![0, 0, 0]]], ![![![53, 62, -1], ![151, 0, 0]], ![![-11, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![4, -61, 1]] ![![151, 0, 0], ![-28, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-4228, 151, 0]], ![![604, -9211, 151], ![0, 1661, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-28, 1, 0]]], ![![![4, -61, 1]], ![![0, 11, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-71, 76, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-71, 76, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![86, 76, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-71, 76, 1], ![112, 15, 151], ![8400, 811, -136]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -76, 157]], ![![-1, 0, 1], ![-82, -73, 151], ![128, 71, -136]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [130, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 156], [0, 1]]
 g := ![![[129, 93], [81], [120, 47], [88, 11], [27, 145], [56], [1]], ![[0, 64], [81], [70, 110], [93, 146], [150, 12], [56], [1]]]
 h' := ![![[29, 156], [98, 67], [100, 9], [21, 19], [101, 110], [43, 50], [27, 29], [0, 1]], ![[0, 1], [0, 90], [47, 148], [101, 138], [151, 47], [80, 107], [83, 128], [29, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [49, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [130, 128, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4078, 51, 11]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -5, 11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![6, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![6, 1, 0]] 
 ![![157, 0, 0], ![6, 1, 0], ![136, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![6, 1, 0], ![0, 7, 2], ![112, 10, 5]]]
  hmulB := by decide  
  f := ![![![763, 127, 0], ![-19939, 0, 0]], ![![18, 3, 0], ![-470, 0, 0]], ![![664, 107, -1], ![-17352, 79, 0]]]
  g := ![![![1, 0, 0], ![-6, 157, 0], ![-136, 0, 157]], ![![0, 1, 0], ![-2, 7, 2], ![-4, 10, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-71, 76, 1]] ![![157, 0, 0], ![6, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![942, 157, 0]], ![![-11147, 11932, 157], ![-314, 471, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![6, 1, 0]]], ![![![-71, 76, 1]], ![![-2, 3, 1]]]]
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


lemma PB163I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 162 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 162 (by omega)

def PB163I3 : PrimesBelowBoundCertificateInterval O 137 162 163 where
  m := 4
  g := ![2, 2, 3, 2]
  P := ![139, 149, 151, 157]
  hP := PB163I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
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
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
