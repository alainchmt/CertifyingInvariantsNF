
import IdealArithmetic.Examples.NF3_3_658476_1.RI3_3_658476_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 1, 2], ![1, 43, -1]]]
  hmulB := by decide  
  f := ![![![-87, 1, 2]], ![![1, 0, 0]], ![![-44, 1, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 2], ![1, 43, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![304, 14676, 2839]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![304, 14676, 2839]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![304, 14676, 2839], ![2839, 137057, 26513], ![11837, 571449, 110544]]]
  hmulB := by decide  
  f := ![![![1671, -33, -35]], ![![818, 50, -33]], ![![1, -342, 82]]]
  g := ![![![-7186, 14676, 2839], ![-67109, 137057, 26513], ![-279806, 571449, 110544]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![304, 14676, 2839]]
  ![![2839, 137057, 26513]] where
 M := ![![![2839, 137057, 26513]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2839, 137057, 26513]] ![![304, 14676, 2839]]
  ![![2, 0, 0]] where
 M := ![![![703802260, 33977113750, 6572705234]]]
 hmul := by decide  
 g := ![![![![351901130, 16988556875, 3286352617]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -79, 19]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-2, -79, 19]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![-2, -79, 19], ![19, 736, -177], ![-98, -3796, 913]]]
  hmulB := by decide  
  f := ![![![76, 3, -1]], ![![25, 13, 2]], ![![52, 52, 9]]]
  g := ![![![13, -79, 19], ![-121, 736, -177], ![624, -3796, 913]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-2, -79, 19]] ![![-2, -79, 19]]
  ![![-3359, -130110, 31292]] where
 M := ![![![-3359, -130110, 31292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-3359, -130110, 31292]] ![![-2, -79, 19]]
  ![![3, 0, 0]] where
 M := ![![![-5531988, -214280031, 51535245]]]
 hmul := by decide  
 g := ![![![![-1843996, -71426677, 17178415]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 4, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 4], [0, 4, 1], [0, 1]]
 g := ![![[2, 4, 1], []], ![[3, 2, 3, 4], [4, 1]], ![[0, 1], [2, 1]]]
 h' := ![![[4, 0, 4], [0, 0, 1], [0, 1]], ![[0, 4, 1], [4, 1, 4], [4, 0, 4]], ![[0, 1], [4, 4], [0, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [4, 0, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 4, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-595, -52060, -50920]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119, -10412, -10184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -62, -12]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1, -62, -12]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![-1, -62, -12], ![-12, -579, -112], ![-50, -2414, -467]]]
  hmulB := by decide  
  f := ![![![25, 14, -4]], ![![3, -17, 4]], ![![24, 110, -27]]]
  g := ![![![19, -62, -12], ![177, -579, -112], ![738, -2414, -467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, -608, 144]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![71, -608, 144]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![71, -608, 144], ![144, 5655, -1360], ![-752, -29168, 7015]]]
  hmulB := by decide  
  f := ![![![1345, 64928, 12560]], ![![2755, 132999, 25728]], ![![8634, 416816, 80631]]]
  g := ![![![321, -608, 144], ![-2853, 5655, -1360], ![14714, -29168, 7015]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1, -62, -12]] ![![-1, -62, -12]]
  ![![1345, 64928, 12560]] where
 M := ![![![1345, 64928, 12560]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![1345, 64928, 12560]] ![![71, -608, 144]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40103, -450, -922]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![40103, -450, -922]] 
 ![![11, 0, 0], ![5, 1, 0], ![7, 0, 1]] where
  M :=![![![40103, -450, -922], ![-922, 7, 22], ![472, 12, -15]]]
  hmulB := by decide  
  f := ![![![369, 17814, 3446]], ![![481, 23221, 4492]], ![![1541, 74394, 14391]]]
  g := ![![![4437, -450, -922], ![-101, 7, 22], ![47, 12, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1696, -19, -39]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![1696, -19, -39]] 
 ![![11, 0, 0], ![7, 1, 0], ![5, 0, 1]] where
  M :=![![![1696, -19, -39], ![-39, 0, 1], ![20, 2, -1]]]
  hmulB := by decide  
  f := ![![![-2, -97, -19]], ![![-3, -145, -28]], ![![-8, -387, -76]]]
  g := ![![![184, -19, -39], ![-4, 0, 1], ![1, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -342, 82]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![1, -342, 82]] 
 ![![11, 0, 0], ![10, 1, 0], ![0, 0, 1]] where
  M :=![![![1, -342, 82], ![82, 3185, -766], ![-424, -16428, 3951]]]
  hmulB := by decide  
  f := ![![![87, 4146, 802]], ![![152, 7289, 1410]], ![![304, 14676, 2839]]]
  g := ![![![311, -342, 82], ![-2888, 3185, -766], ![14896, -16428, 3951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![40103, -450, -922]] ![![1696, -19, -39]]
  ![![68013798, -763801, -1563545]] where
 M := ![![![68013798, -763801, -1563545]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![68013798, -763801, -1563545]] ![![1, -342, 82]]
  ![![11, 0, 0]] where
 M := ![![![668325196, -7507841, -15363293]]]
 hmul := by decide  
 g := ![![![![60756836, -682531, -1396663]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1221, 14, 28]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1221, 14, 28]] 
 ![![13, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![-1221, 14, 28], ![28, -3, 0], ![-14, 14, -3]]]
  hmulB := by decide  
  f := ![![![-9, -434, -84]], ![![-12, -579, -112]], ![![-29, -1400, -271]]]
  g := ![![![-109, 14, 28], ![4, -3, 0], ![-9, 14, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -5, -1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![0, -5, -1]] 
 ![![13, 0, 0], ![9, 1, 0], ![7, 0, 1]] where
  M :=![![![0, -5, -1], ![-1, -48, -9], ![-4, -194, -39]]]
  hmulB := by decide  
  f := ![![![126, -1, -3]], ![![87, -1, -2]], ![![68, 1, -2]]]
  g := ![![![4, -5, -1], ![38, -48, -9], ![155, -194, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1221, 14, 28]] ![![0, -5, -1]]
  ![![-126, 1, 3]] where
 M := ![![![-126, 1, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-126, 1, 3]] ![![0, -5, -1]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [7, 13, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 2], [10, 15, 15], [0, 1]]
 g := ![![[8, 5, 1], [12, 8], [5, 1], []], ![[16, 9, 5, 8], [0, 4], [9, 4], [7, 4]], ![[1, 13, 16, 15], [14, 9], [8, 1], [11, 4]]]
 h' := ![![[12, 1, 2], [2, 0, 16], [16, 13, 12], [0, 0, 1], [0, 1]], ![[10, 15, 15], [9, 10, 2], [3, 12, 2], [10, 7, 15], [12, 1, 2]], ![[0, 1], [13, 7, 16], [14, 9, 3], [6, 10, 1], [10, 15, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 8], []]
 b := ![[], [12, 12, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [7, 13, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2125, -26996, 128350]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, -1588, 7550]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2622599, 29452, 60290]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-2622599, 29452, 60290]] 
 ![![19, 0, 0], ![0, 19, 0], ![3, 7, 1]] where
  M :=![![![-2622599, 29452, 60290], ![60290, -677, -1386], ![-30838, 346, 709]]]
  hmulB := by decide  
  f := ![![![23, 1112, 218]], ![![218, 10509, 2006]], ![![131, 6323, 1221]]]
  g := ![![![-147551, -20662, 60290], ![3392, 475, -1386], ![-1735, -243, 709]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 18], [0, 1]]
 g := ![![[11, 17], [9, 7], [16], [1]], ![[0, 2], [0, 12], [16], [1]]]
 h' := ![![[15, 18], [14, 13], [13, 8], [10, 15], [0, 1]], ![[0, 1], [0, 6], [0, 11], [7, 4], [15, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [9, 4, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3848, -21, 168]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![176, -63, 168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -1112, -218]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-23, -1112, -218]] 
 ![![19, 0, 0], ![6, 1, 0], ![17, 0, 1]] where
  M :=![![![-23, -1112, -218], ![-218, -10509, -2006], ![-894, -43238, -8503]]]
  hmulB := by decide  
  f := ![![![2622599, -29452, -60290]], ![![825016, -9265, -18966]], ![![2348159, -26370, -53981]]]
  g := ![![![545, -1112, -218], ![5102, -10509, -2006], ![21215, -43238, -8503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-2622599, 29452, 60290]] ![![-23, -1112, -218]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [1, 11, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22, 9], [3, 0, 14], [0, 1]]
 g := ![![[21, 12, 12], [14, 1, 12], [14, 5, 1], []], ![[6, 6, 14, 9], [20, 2, 17, 18], [3, 18], [19, 12]], ![[9, 11, 1, 22], [20, 19, 11, 7], [15, 9, 3, 14], [14, 12]]]
 h' := ![![[2, 22, 9], [9, 18, 14], [9, 2, 14], [0, 0, 1], [0, 1]], ![[3, 0, 14], [19, 6, 1], [10, 22, 18], [8, 5], [2, 22, 9]], ![[0, 1], [16, 22, 8], [14, 22, 14], [18, 18, 22], [3, 0, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 19], []]
 b := ![[], [2, 9, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [1, 11, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1495, -45862, -214222]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![65, -1994, -9314]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![152, 7387, 1429]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![152, 7387, 1429]] 
 ![![29, 0, 0], ![0, 29, 0], ![19, 28, 1]] where
  M :=![![![152, 7387, 1429], ![1429, 68986, 13345], ![5958, 287632, 55641]]]
  hmulB := by decide  
  f := ![![![-34, -209, 51]], ![![51, 1950, -469]], ![![18, 1399, -336]]]
  g := ![![![-931, -1125, 1429], ![-8694, -10506, 13345], ![-36249, -43804, 55641]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [9, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 28], [0, 1]]
 g := ![![[18, 13], [22], [25, 13], [12, 1]], ![[0, 16], [22], [7, 16], [24, 28]]]
 h' := ![![[12, 28], [25, 10], [7, 15], [8, 19], [0, 1]], ![[0, 1], [0, 19], [13, 14], [4, 10], [12, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [13, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [9, 17, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12, 297, 341]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-223, -319, 341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, 209, -51]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![34, 209, -51]] 
 ![![29, 0, 0], ![3, 1, 0], ![23, 0, 1]] where
  M :=![![![34, 209, -51], ![-51, -1950, 469], ![260, 10058, -2419]]]
  hmulB := by decide  
  f := ![![![-152, -7387, -1429]], ![![-65, -3143, -608]], ![![-326, -15777, -3052]]]
  g := ![![![20, 209, -51], ![-172, -1950, 469], ![887, 10058, -2419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![152, 7387, 1429]] ![![34, 209, -51]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -108, -22]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![51, -108, -22]] 
 ![![31, 0, 0], ![19, 1, 0], ![27, 0, 1]] where
  M :=![![![51, -108, -22], ![-22, -1003, -194], ![-86, -4182, -809]]]
  hmulB := by decide  
  f := ![![![-119, -4632, 1114]], ![![-37, -1447, 348]], ![![-289, -11214, 2697]]]
  g := ![![![87, -108, -22], ![783, -1003, -194], ![3265, -4182, -809]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 10, 2]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-3, 10, 2]] 
 ![![31, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![-3, 10, 2], ![2, 93, 18], ![8, 388, 75]]]
  hmulB := by decide  
  f := ![![![-9, 26, -6]], ![![-6, 9, -2]], ![![-1, 46, -11]]]
  g := ![![![-7, 10, 2], ![-64, 93, 18], ![-267, 388, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8832, -99, -203]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![8832, -99, -203]] 
 ![![31, 0, 0], ![23, 1, 0], ![3, 0, 1]] where
  M :=![![![8832, -99, -203], ![-203, 4, 5], ![104, 6, -1]]]
  hmulB := by decide  
  f := ![![![-34, -1317, 317]], ![![-15, -581, 140]], ![![-56, -2169, 522]]]
  g := ![![![378, -99, -203], ![-10, 4, 5], ![-1, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![51, -108, -22]] ![![-3, 10, 2]]
  ![![-545, -18070, -3492]] where
 M := ![![![-545, -18070, -3492]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-545, -18070, -3492]] ![![8832, -99, -203]]
  ![![31, 0, 0]] where
 M := ![![![-1508398, -39277, 23777]]]
 hmul := by decide  
 g := ![![![![-48658, -1267, 767]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB181I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB181I0 : PrimesBelowBoundCertificateInterval O 1 31 181 where
  m := 11
  g := ![3, 3, 1, 3, 3, 3, 1, 2, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB181I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![31, 31, 31]
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
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I19N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1, I13N1], [], [I19N1], [], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
