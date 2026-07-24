
import IdealArithmetic.Examples.NF3_3_816696_1.RI3_3_816696_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1082, 25, -26]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1082, 25, -26]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![1082, 25, -26], ![-1871, -61, 49], ![917, 87, -37]]]
  hmulB := by decide  
  f := ![![![2006, 1337, 361]], ![![12147, 8096, 2186]], ![![54423, 36273, 9794]]]
  g := ![![![554, 25, -26], ![-960, -61, 49], ![477, 87, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![591, 347, -90]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![591, 347, -90]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![591, 347, -90], ![-6737, -3626, 951], ![21667, 11501, -3022]]]
  hmulB := by decide  
  f := ![![![20321, 13544, 3657]], ![![133212, 88786, 23973]], ![![551313, 367451, 99215]]]
  g := ![![![167, 347, -90], ![-2031, -3626, 951], ![6594, 11501, -3022]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1082, 25, -26]] ![![591, 347, -90]]
  ![![-92305, -14222, 4967]] where
 M := ![![![-92305, -14222, 4967]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-92305, -14222, 4967]] ![![591, 347, -90]]
  ![![2, 0, 0]] where
 M := ![![![148881348, 76664604, -20227946]]]
 hmul := by decide  
 g := ![![![![74440674, 38332302, -10113973]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-222, -118, 31]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-222, -118, 31]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-222, -118, 31], ![2319, 1229, -323], ![-7355, -3896, 1024]]]
  hmulB := by decide  
  f := ![![![88, 56, 15]], ![![395, 263, 71]], ![![1549, 1030, 278]]]
  g := ![![![-16, -118, 31], ![169, 1229, -323], ![-537, -3896, 1024]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-222, -118, 31]] ![![-222, -118, 31]]
  ![![-452363, -239602, 62976]] where
 M := ![![![-452363, -239602, 62976]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-452363, -239602, 62976]] ![![-222, -118, 31]]
  ![![3, 0, 0]] where
 M := ![![![-918400932, -486446520, 127855617]]]
 hmul := by decide  
 g := ![![![![-306133644, -162148840, 42618539]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 0, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 4], [3, 2, 1], [0, 1]]
 g := ![![[4, 2, 1], []], ![[4, 1, 2, 1], [3, 1]], ![[0, 1, 3, 4], [1, 1]]]
 h' := ![![[4, 2, 4], [0, 0, 1], [0, 1]], ![[3, 2, 1], [4, 2, 2], [4, 2, 4]], ![[0, 1], [0, 3, 2], [3, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 3], []]
 b := ![[], [2, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 0, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-110260, -87210, -51840]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22052, -17442, -10368]
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

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![184, -2, -3]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![184, -2, -3]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 3, 1]] where
  M :=![![![184, -2, -3], ![-211, 57, -9], ![-241, -200, 50]]]
  hmulB := by decide  
  f := ![![![-150, -100, -27]], ![![-1817, -1211, -327]], ![![-2006, -1337, -361]]]
  g := ![![![28, 1, -3], ![-25, 12, -9], ![-63, -50, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3590, -1023, 2795]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2110, -1344, 2795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150, 100, 27]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![150, 100, 27]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![150, 100, 27], ![1817, 1211, 327], ![7991, 5326, 1438]]]
  hmulB := by decide  
  f := ![![![-184, 2, 3]], ![![-75, -7, 3]], ![![-97, 30, -5]]]
  g := ![![![-55, 100, 27], ![-666, 1211, 327], ![-2929, 5326, 1438]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![184, -2, -3]] ![![150, 100, 27]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [4, 7, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 6], [2, 8, 5], [0, 1]]
 g := ![![[5, 4, 5], [9, 4, 1], []], ![[1, 3, 4, 2], [6, 0, 1, 10], [3, 3]], ![[0, 8, 5, 9], [6, 6, 7, 9], [4, 3]]]
 h' := ![![[2, 2, 6], [8, 9, 4], [0, 0, 1], [0, 1]], ![[2, 8, 5], [5, 6, 9], [3, 8, 8], [2, 2, 6]], ![[0, 1], [0, 7, 9], [10, 3, 2], [2, 8, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 5], []]
 b := ![[], [1, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [4, 7, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1163777857, -941963484, -597509297]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105797987, -85633044, -54319027]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 6, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 3, 5], [3, 9, 8], [0, 1]]
 g := ![![[8, 3, 1], [10, 4], [1]], ![[4, 8, 10, 8], [5, 1], [11, 0, 7, 8]], ![[2, 5, 0, 2], [4, 9], [7, 12, 9, 5]]]
 h' := ![![[12, 3, 5], [1, 6, 12], [8, 7, 2], [0, 1]], ![[3, 9, 8], [4, 5, 8], [9, 8, 1], [12, 3, 5]], ![[0, 1], [5, 2, 6], [5, 11, 10], [3, 9, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 3], []]
 b := ![[], [11, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 6, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![199381, -268788, -900952]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15337, -20676, -69304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -4, -1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-6, -4, -1]] 
 ![![17, 0, 0], ![4, 1, 0], ![7, 0, 1]] where
  M :=![![![-6, -4, -1], ![-67, -45, -13], ![-317, -210, -54]]]
  hmulB := by decide  
  f := ![![![300, 6, -7]], ![![41, 1, -1]], ![![135, 2, -3]]]
  g := ![![![1, -4, -1], ![12, -45, -13], ![53, -210, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -74, -20]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-111, -74, -20]] 
 ![![17, 0, 0], ![5, 1, 0], ![10, 0, 1]] where
  M :=![![![-111, -74, -20], ![-1346, -897, -242], ![-5914, -3942, -1065]]]
  hmulB := by decide  
  f := ![![![1341, 30, -32]], ![![259, 5, -6]], ![![852, 22, -21]]]
  g := ![![![27, -74, -20], ![327, -897, -242], ![1438, -3942, -1065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 6, 3]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![8, 6, 3]] 
 ![![17, 0, 0], ![8, 1, 0], ![15, 0, 1]] where
  M :=![![![8, 6, 3], ![207, 131, 21], ![525, 372, 146]]]
  hmulB := by decide  
  f := ![![![11314, 240, -267]], ![![4195, 89, -99]], ![![10467, 222, -247]]]
  g := ![![![-5, 6, 3], ![-68, 131, 21], ![-273, 372, 146]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-6, -4, -1]] ![![-111, -74, -20]]
  ![![11964, 7974, 2153]] where
 M := ![![![11964, 7974, 2153]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![11964, 7974, 2153]] ![![8, 6, 3]]
  ![![17, 0, 0]] where
 M := ![![![2876655, 1917294, 517684]]]
 hmul := by decide  
 g := ![![![![169215, 112782, 30452]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244, 90, 21]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![244, 90, 21]] 
 ![![19, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![244, 90, 21], ![1401, 1057, 291], ![7083, 4668, 1258]]]
  hmulB := by decide  
  f := ![![![-28682, -15192, 3993]], ![![625, 331, -87]], ![![-70969, -37590, 9880]]]
  g := ![![![-50, 90, 21], ![-697, 1057, 291], ![-3011, 4668, 1258]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72, -48, -13]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-72, -48, -13]] 
 ![![19, 0, 0], ![18, 1, 0], ![18, 0, 1]] where
  M :=![![![-72, -48, -13], ![-875, -583, -157], ![-3837, -2558, -692]]]
  hmulB := by decide  
  f := ![![![-1830, -38, 43]], ![![-1571, -33, 37]], ![![-1801, -36, 42]]]
  g := ![![![54, -48, -13], ![655, -583, -157], ![2877, -2558, -692]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![244, 90, 21]] ![![244, 90, 21]]
  ![![334369, 215118, 57732]] where
 M := ![![![334369, 215118, 57732]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![334369, 215118, 57732]] ![![-72, -48, -13]]
  ![![19, 0, 0]] where
 M := ![![![-433820502, -289141962, -78070867]]]
 hmul := by decide  
 g := ![![![![-22832658, -15217998, -4108993]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [4, 0, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 1, 19], [0, 21, 4], [0, 1]]
 g := ![![[7, 10, 8], [21, 1, 12], [2, 18, 1], []], ![[9, 14, 2, 11], [19, 16, 16, 17], [9, 1, 4, 7], [4, 16]], ![[0, 4, 10, 13], [4, 4, 4, 13], [12, 3, 18, 4], [19, 16]]]
 h' := ![![[18, 1, 19], [8, 14, 10], [15, 20, 9], [0, 0, 1], [0, 1]], ![[0, 21, 4], [5, 10, 16], [19, 21, 17], [9, 18, 21], [18, 1, 19]], ![[0, 1], [7, 22, 20], [21, 5, 20], [16, 5, 1], [0, 21, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 22], []]
 b := ![[], [4, 13, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [4, 0, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-109664, -86526, -51060]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4768, -3762, -2220]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5323, -3548, -958]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-5323, -3548, -958]] 
 ![![29, 0, 0], ![0, 29, 0], ![16, 10, 1]] where
  M :=![![![-5323, -3548, -958], ![-64470, -42969, -11602], ![-283522, -188968, -51023]]]
  hmulB := by decide  
  f := ![![![-19, -60, 14]], ![![1054, 643, -166]], ![![222, 118, -31]]]
  g := ![![![345, 208, -958], ![4178, 2519, -11602], ![18374, 11078, -51023]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 28], [0, 1]]
 g := ![![[22, 7], [20], [7, 25], [1, 1]], ![[0, 22], [20], [3, 4], [2, 28]]]
 h' := ![![[1, 28], [23, 6], [28, 7], [4, 5], [0, 1]], ![[0, 1], [0, 23], [6, 22], [9, 24], [1, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [12, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [25, 28, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10426, 6944, 1924]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-702, -424, 1924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -60, 14]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-19, -60, 14]] 
 ![![29, 0, 0], ![27, 1, 0], ![17, 0, 1]] where
  M :=![![![-19, -60, 14], ![1054, 643, -166], ![-3798, -2048, 537]]]
  hmulB := by decide  
  f := ![![![-5323, -3548, -958]], ![![-7179, -4785, -1292]], ![![-12897, -8596, -2321]]]
  g := ![![![47, -60, 14], ![-465, 643, -166], ![1461, -2048, 537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-5323, -3548, -958]] ![![-19, -60, 14]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [17, 24, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 8, 24], [20, 22, 7], [0, 1]]
 g := ![![[16, 21, 8], [4, 10, 5], [2, 4, 16], [1]], ![[24, 4, 5, 15], [2, 3, 2, 27], [24, 6, 4, 26], [20, 19, 6, 29]], ![[6, 12, 29, 1], [6, 10, 5, 16], [15, 24, 20, 8], [11, 28, 2, 2]]]
 h' := ![![[7, 8, 24], [25, 22, 16], [28, 18, 6], [14, 7, 27], [0, 1]], ![[20, 22, 7], [16, 24, 12], [27, 25, 6], [3, 1, 18], [7, 8, 24]], ![[0, 1], [23, 16, 3], [13, 19, 19], [1, 23, 17], [20, 22, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 23], []]
 b := ![[], [14, 19, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [17, 24, 4, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![322958, 139996, -118172]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10418, 4516, -3812]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB201I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB201I0 : PrimesBelowBoundCertificateInterval O 1 31 201 where
  m := 11
  g := ![3, 3, 1, 2, 1, 1, 3, 3, 1, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB201I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
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
    · exact ![49, 7]
    · exact ![1331]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![29791]
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
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
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I17N0, I17N1, I17N2, I19N0, I19N1, I29N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N1], [], [], [I17N0, I17N1, I17N2], [I19N0, I19N0, I19N1], [], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
