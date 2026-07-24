
import IdealArithmetic.Examples.NF3_1_244068_1.RI3_1_244068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![176898, -284495, -32709]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![176898, -284495, -32709]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![176898, -284495, -32709], ![-1026916, 612001, -1674261], ![-3590422, 6062636, 1180991]]]
  hmulB := by decide  
  f := ![![![10873202684987, 137683273621, 496336823904]], ![![3612041040949, 45737916360, 164881408911]], ![![-2014238028077, -25505538119, -91945357261]]]
  g := ![![![88449, -284495, -32709], ![-513458, 612001, -1674261], ![-1795211, 6062636, 1180991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3311557, 41933, 151165]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![3311557, 41933, 151165]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3311557, 41933, 151165], ![2200176, 27860, 100433], ![-1226918, -15536, -56006]]]
  hmulB := by decide  
  f := ![![![-72, 158, 89]], ![![745, -857, 474]], ![![572, -1471, -1094]]]
  g := ![![![1634812, 41933, 151165], ![1086158, 27860, 100433], ![-605691, -15536, -56006]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![176898, -284495, -32709]] ![![3311557, 41933, 151165]]
  ![![-72, 158, 89]] where
 M := ![![![-72, 158, 89]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-72, 158, 89]] ![![3311557, 41933, 151165]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![15, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![15, 0, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![15, 0, 1], ![14, -7, -1], ![-12, 6, -7]]]
  hmulB := by decide  
  f := ![![![0, -7, -2], ![3, -3, 0]], ![![-5, -2, -1], ![2, -1, 0]], ![![-5, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![0, 0, 3]], ![![5, 0, 1], ![7, -7, -1], ![-6, 6, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-14, -1, -1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-14, -1, -1]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-14, -1, -1], ![-16, 7, -5], ![-2, 16, 9]]]
  hmulB := by decide  
  f := ![![![5, -32, -18], ![0, 0, 6]], ![![1, -5, -3], ![0, 0, 1]], ![![-3, -11, -6], ![-1, 0, 2]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![-4, -1, -1], ![-6, 7, -5], ![-9, 16, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![-14, -1, -1]]
  ![![3, 0, 0], ![1, 1, 0]] where
 M := ![![![9, 0, 0], ![-42, -3, -3]], ![![45, 0, 3], ![-212, 1, -6]]]
 hmul := by decide  
 g := ![![![![2, -1, 0], ![3, 0, 0]], ![![-13, 0, -1], ![-3, 0, 0]]], ![![![13, -2, 1], ![6, 0, 0]], ![![-65, 6, -2], ![-17, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![-14, -1, -1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-42, -3, -3]], ![![3, 3, 0], ![-30, 6, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-14, -1, -1]]], ![![![1, 1, 0]], ![![-10, 2, -2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![15, -2, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![15, -2, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 3, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![15, -2, 1], ![10, -9, -13], ![-40, 50, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -3, 5]], ![![3, -1, 1], ![2, 6, -13], ![-8, 13, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4], [0, 1]]
 g := ![![[4, 1], [1]], ![[0, 4], [1]]]
 h' := ![![[1, 4], [4, 1], [0, 1]], ![[0, 1], [0, 4], [1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-575, 294, -1022]
  a := ![2, 0, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-115, 672, -1022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![2, -1, 6], ![14, -22, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![2, -1, 5], ![1, -4, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![1, -1, 6], ![16, -22, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![15, -2, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![75, -10, 5], ![-20, -5, -15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-2, 1, 0]]], ![![![15, -2, 1]], ![![-4, -1, -3]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [2, 0, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 2], [0, 1]]
 g := ![![[], [1]], ![[], [1]], ![[], [1]]]
 h' := ![![[0, 4], [5], [0, 1]], ![[0, 2], [5], [0, 4]], ![[0, 1], [5], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [0, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [2, 0, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5334927087, -595334922, -15466636829]
  a := ![-129, -64, -323]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-762132441, -85047846, -2209519547]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀


def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![245, 456, 1479]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![245, 456, 1479]] 
 ![![11, 0, 0], ![2, 1, 0], ![3, 0, 1]] where
  M :=![![![245, 456, 1479], ![21618, -31837, 1257], ![-11364, -1158, -32749]]]
  hmulB := by decide  
  f := ![![![1044085519, 13220862, 47660115]], ![![252895852, 3202325, 11544117]], ![![249584295, 3160392, 11392952]]]
  g := ![![![-464, 456, 1479], ![7411, -31837, 1257], ![8109, -1158, -32749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601907, -448248, 820776]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![601907, -448248, 820776]] 
 ![![11, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![601907, -448248, 820776], ![10594368, -17903413, -3510264], ![-16124784, 14786112, -17006917]]]
  hmulB := by decide  
  f := ![![![356385015561289, 4512769331496, 16268160525960]], ![![345511812876302, 4375086057875, 15771823702056]], ![![117590991506780, 1489010471712, 5367759705683]]]
  g := ![![![163753, -448248, 820776], ![18515414, -17903413, -3510264], ![-8723476, 14786112, -17006917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![245, 456, 1479]] ![![601907, -448248, 820776]]
  ![![-18870056513, 13594882560, -26552820507]] where
 M := ![![![-18870056513, 13594882560, -26552820507]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-18870056513, 13594882560, -26552820507]] ![![601907, -448248, 820776]]
  ![![11, 0, 0]] where
 M := ![![![560829664917997277, -627549309998736840, 388371898139336991]]]
 hmul := by decide  
 g := ![![![![50984514992545207, -57049937272612440, 35306536194485181]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![18, 3, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![18, 3, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![5, 3, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![18, 3, 1], ![20, -1, 17], ![30, -60, -7]]]
  hmulB := by decide  
  f := ![![![-17, -3, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -3, 13]], ![![1, 0, 1], ![-5, -4, 17], ![5, -3, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[4, 12], [3], [4, 1]], ![[0, 1], [3], [8, 12]]]
 h' := ![![[4, 12], [6, 5], [4, 4], [0, 1]], ![[0, 1], [0, 8], [7, 9], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-924, 158, -2244]
  a := ![-3, -1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![792, 530, -2244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-4, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-4, 1, 0]] 
 ![![13, 0, 0], ![9, 1, 0], ![7, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-4, 1, 0], ![2, -3, 6], ![14, -22, -5]]]
  hmulB := by decide  
  f := ![![![-13, 26, -54], ![13, 117, 0]], ![![-7, 17, -36], ![14, 78, 0]], ![![-7, 14, -29], ![7, 63, 0]]]
  g := ![![![1, 0, 0], ![-9, 13, 0], ![-7, 0, 13]], ![![-1, 1, 0], ![-1, -3, 6], ![19, -22, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![18, 3, 1]] ![![13, 0, 0], ![-4, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-52, 13, 0]], ![![234, 39, 13], ![-52, -13, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-4, 1, 0]]], ![![![18, 3, 1]], ![![-4, -1, 1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [2, 0, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12, 6], [2, 4, 11], [0, 1]]
 g := ![![[3, 2, 8], [0, 1], [13, 1], []], ![[10, 11, 10, 3], [6, 1], [10, 16], [0, 2]], ![[4, 14, 4, 7], [], [1, 8], [12, 2]]]
 h' := ![![[11, 12, 6], [13, 0, 5], [8, 15, 16], [0, 0, 1], [0, 1]], ![[2, 4, 11], [6, 8, 3], [1, 5, 1], [2, 5, 4], [11, 12, 6]], ![[0, 1], [15, 9, 9], [7, 14], [14, 12, 12], [2, 4, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 7], []]
 b := ![[], [8, 0, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [2, 0, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-101949, -38828, -344811]
  a := ![-3, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5997, -2284, -20283]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![9, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![9, 1, 0]] 
 ![![19, 0, 0], ![9, 1, 0], ![17, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![9, 1, 0], ![2, 10, 6], ![14, -22, 8]]]
  hmulB := by decide  
  f := ![![![358, 2533, 1530], ![323, -4845, 0]], ![![168, 1192, 720], ![153, -2280, 0]], ![![326, 2267, 1369], ![277, -4335, 0]]]
  g := ![![![1, 0, 0], ![-9, 19, 0], ![-17, 0, 19]], ![![0, 1, 0], ![-10, 10, 6], ![4, -22, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-5, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-5, 1, 0]] 
 ![![19, 0, 0], ![14, 1, 0], ![16, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-5, 1, 0], ![2, -4, 6], ![14, -22, -6]]]
  hmulB := by decide  
  f := ![![![141, -298, 450], ![-38, -1425, 0]], ![![101, -218, 330], ![-37, -1045, 0]], ![![119, -251, 379], ![-31, -1200, 0]]]
  g := ![![![1, 0, 0], ![-14, 19, 0], ![-16, 0, 19]], ![![-1, 1, 0], ![-2, -4, 6], ![22, -22, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-4, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-4, 1, 0]] 
 ![![19, 0, 0], ![15, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-4, 1, 0], ![2, -3, 6], ![14, -22, -5]]]
  hmulB := by decide  
  f := ![![![293, -458, 924], ![-76, -2926, 0]], ![![231, -360, 726], ![-56, -2299, 0]], ![![169, -265, 535], ![-47, -1694, 0]]]
  g := ![![![1, 0, 0], ![-15, 19, 0], ![-11, 0, 19]], ![![-1, 1, 0], ![-1, -3, 6], ![21, -22, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![9, 1, 0]] ![![19, 0, 0], ![-5, 1, 0]]
  ![![19, 0, 0], ![15, 4, 1]] where
 M := ![![![361, 0, 0], ![-95, 19, 0]], ![![171, 19, 0], ![-43, 5, 6]]]
 hmul := by decide  
 g := ![![![![4, -4, -1], ![19, 0, 0]], ![![-5, 1, 0], ![0, 0, 0]]], ![![![-6, -3, -1], ![19, 0, 0]], ![![-7, -1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![15, 4, 1]] ![![19, 0, 0], ![-4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-76, 19, 0]], ![![285, 76, 19], ![-38, -19, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-4, 1, 0]]], ![![![15, 4, 1]], ![![-2, -1, 1]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [1, 18, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 20, 22], [19, 2, 1], [0, 1]]
 g := ![![[21, 2, 18], [20, 8, 13], [9, 21, 1], []], ![[13, 15, 21, 21], [2, 19, 18, 15], [7, 11, 14, 19], [4, 1]], ![[5, 3, 10, 8], [11, 14, 16, 16], [3, 20, 19, 9], [2, 1]]]
 h' := ![![[2, 20, 22], [3, 12, 15], [14, 1, 17], [0, 0, 1], [0, 1]], ![[19, 2, 1], [4, 0, 18], [16, 1, 10], [0, 7, 2], [2, 20, 22]], ![[0, 1], [4, 11, 13], [18, 21, 19], [14, 16, 20], [19, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 7], []]
 b := ![[], [12, 9, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [1, 18, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17747996, 53877615, 144513922]
  a := ![23, 21, 68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![771652, 2342505, 6283214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-12, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-12, 1, 0]] 
 ![![29, 0, 0], ![17, 1, 0], ![17, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-12, 1, 0], ![2, -11, 6], ![14, -22, -13]]]
  hmulB := by decide  
  f := ![![![457, -3158, 1728], ![-290, -8352, 0]], ![![265, -1842, 1008], ![-173, -4872, 0]], ![![277, -1852, 1013], ![-148, -4896, 0]]]
  g := ![![![1, 0, 0], ![-17, 29, 0], ![-17, 0, 29]], ![![-1, 1, 0], ![3, -11, 6], ![21, -22, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-10, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-10, 1, 0]] 
 ![![29, 0, 0], ![19, 1, 0], ![24, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-10, 1, 0], ![2, -9, 6], ![14, -22, -11]]]
  hmulB := by decide  
  f := ![![![839, -4431, 2964], ![-435, -14326, 0]], ![![557, -2898, 1938], ![-260, -9367, 0]], ![![694, -3667, 2453], ![-361, -11856, 0]]]
  g := ![![![1, 0, 0], ![-19, 29, 0], ![-24, 0, 29]], ![![-1, 1, 0], ![1, -9, 6], ![24, -22, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-7, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-7, 1, 0]] 
 ![![29, 0, 0], ![22, 1, 0], ![3, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-7, 1, 0], ![2, -6, 6], ![14, -22, -8]]]
  hmulB := by decide  
  f := ![![![-194, 645, -648], ![87, 3132, 0]], ![![-147, 484, -486], ![59, 2349, 0]], ![![-15, 66, -67], ![30, 324, 0]]]
  g := ![![![1, 0, 0], ![-22, 29, 0], ![-3, 0, 29]], ![![-1, 1, 0], ![4, -6, 6], ![18, -22, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-12, 1, 0]] ![![29, 0, 0], ![-10, 1, 0]]
  ![![29, 0, 0], ![1, 11, 1]] where
 M := ![![![841, 0, 0], ![-290, 29, 0]], ![![-348, 29, 0], ![122, -21, 6]]]
 hmul := by decide  
 g := ![![![![28, -11, -1], ![29, 0, 0]], ![![-11, -10, -1], ![29, 0, 0]]], ![![![-12, 1, 0], ![0, 0, 0]], ![![4, -3, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![1, 11, 1]] ![![29, 0, 0], ![-7, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-203, 29, 0]], ![![29, 319, 29], ![29, -87, 58]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-7, 1, 0]]], ![![![1, 11, 1]], ![![1, -3, 2]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![8, -13, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![8, -13, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![8, 18, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![8, -13, 1], ![-12, -27, -79], ![-194, 292, -1]]]
  hmulB := by decide  
  f := ![![![-7, 13, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -18, 31]], ![![0, -1, 1], ![20, 45, -79], ![-6, 10, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [1, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30], [0, 1]]
 g := ![![[23, 1], [23, 1], [23, 1], [8, 1]], ![[0, 30], [0, 30], [0, 30], [16, 30]]]
 h' := ![![[8, 30], [8, 30], [8, 30], [23, 1], [0, 1]], ![[0, 1], [0, 1], [0, 1], [0, 30], [8, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [27, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [1, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123, 134, -120]
  a := ![-1, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27, 74, -120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-14, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-14, 1, 0]] 
 ![![31, 0, 0], ![17, 1, 0], ![1, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-14, 1, 0], ![2, -13, 6], ![14, -22, -15]]]
  hmulB := by decide  
  f := ![![![395, -3281, 1518], ![-248, -7843, 0]], ![![221, -1790, 828], ![-123, -4278, 0]], ![![15, -106, 49], ![-3, -253, 0]]]
  g := ![![![1, 0, 0], ![-17, 31, 0], ![-1, 0, 31]], ![![-1, 1, 0], ![7, -13, 6], ![13, -22, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![8, -13, 1]] ![![31, 0, 0], ![-14, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-434, 31, 0]], ![![248, -403, 31], ![-124, 155, -93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-14, 1, 0]]], ![![![8, -13, 1]], ![![-4, 5, -3]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB140I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB140I0 : PrimesBelowBoundCertificateInterval O 1 31 140 where
  m := 11
  g := ![3, 3, 2, 1, 3, 2, 1, 3, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB140I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I13N1, I19N0, I19N1, I19N2, I29N0, I29N1, I29N2, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N1, I3N1], [I5N0, I5N1], [], [I11N0, I11N1, I11N1], [I13N1], [], [I19N0, I19N1, I19N2], [], [I29N0, I29N1, I29N2], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
