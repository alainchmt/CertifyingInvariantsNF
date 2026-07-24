
import IdealArithmetic.Examples.NF3_1_186731_1.RI3_1_186731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![0, 3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![0, 3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 3, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![0, 3, 1], ![-74, 4, 26], ![-222, -15, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, -2, -1], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -3, 37]], ![![0, 0, 1], ![-2, -2, 26], ![-6, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [12, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 36], [0, 1]]
 g := ![![[17, 34], [33], [26, 4], [28], [1]], ![[0, 3], [33], [24, 33], [28], [1]]]
 h' := ![![[18, 36], [8, 16], [21, 25], [30, 35], [25, 18], [0, 1]], ![[0, 1], [0, 21], [27, 12], [31, 2], [16, 19], [18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [25, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [12, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2109, -1455, -411]
  a := ![-4, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -6, -411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![3, 13, 9], ![-83, -2, 10]]]
  hmulB := by decide  
  f := ![![![2226, 10855, 7533], ![962, -30969, 0]], ![![656, 3216, 2232], ![297, -9176, 0]], ![![291, 1466, 1018], ![163, -4185, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-5, 0, 37]], ![![0, 1, 0], ![-5, 13, 9], ![-3, -2, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![0, 3, 1]] ![![37, 0, 0], ![11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![407, 37, 0]], ![![0, 111, 37], ![-74, 37, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![11, 1, 0]]], ![![![0, 3, 1]], ![![-2, 1, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![16, -6, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![16, -6, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![16, 35, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![16, -6, 1], ![-101, 2, -55], ![525, 3, 20]]]
  hmulB := by decide  
  f := ![![![-15, 6, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -35, 41]], ![![0, -1, 1], ![19, 47, -55], ![5, -17, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 40], [0, 1]]
 g := ![![[14, 21], [2], [1], [13, 5], [1]], ![[0, 20], [2], [1], [37, 36], [1]]]
 h' := ![![[13, 40], [33, 29], [18, 24], [15, 40], [39, 13], [0, 1]], ![[0, 1], [0, 12], [2, 17], [2, 1], [3, 28], [13, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [23, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 28, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![389, -1545, 114]
  a := ![4, 2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -135, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![3, 16, 9], ![-83, -2, 13]]]
  hmulB := by decide  
  f := ![![![41, 287, 162], ![41, -738, 0]], ![![4, 95, 54], ![42, -246, 0]], ![![21, 147, 83], ![21, -378, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-10, 16, 9], ![-8, -2, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![16, -6, 1]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![656, -246, 41], ![123, -82, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![14, 1, 0]]], ![![![16, -6, 1]], ![![3, -2, -1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![2, -14, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![2, -14, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![2, 29, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![2, -14, 1], ![-125, -28, -127], ![1189, 19, 14]]]
  hmulB := by decide  
  f := ![![![-1, 14, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -29, 43]], ![![0, -1, 1], ![3, 85, -127], ![27, -9, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 42], [0, 1]]
 g := ![![[37, 10], [39, 21], [36], [40, 21], [1]], ![[0, 33], [0, 22], [36], [1, 22], [1]]]
 h' := ![![[35, 42], [9, 28], [21, 8], [39, 6], [30, 35], [0, 1]], ![[0, 1], [0, 15], [0, 35], [34, 37], [8, 8], [35, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [28, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [13, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3761684, -2599902, -323683]
  a := ![-194, -129, -518]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72426, 157835, -323683]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-2, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-2, 1, 0]] 
 ![![43, 0, 0], ![41, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-2, 1, 0], ![3, 0, 9], ![-83, -2, -3]]]
  hmulB := by decide  
  f := ![![![944, 1, 2835], ![-43, -13545, 0]], ![![901, 0, 2700], ![1, -12900, 0]], ![![638, 0, 1912], ![0, -9135, 0]]]
  g := ![![![1, 0, 0], ![-41, 43, 0], ![-29, 0, 43]], ![![-1, 1, 0], ![-6, 0, 9], ![2, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![2, -14, 1]] ![![43, 0, 0], ![-2, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-86, 43, 0]], ![![86, -602, 43], ![-129, 0, -129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-2, 1, 0]]], ![![![2, -14, 1]], ![![-3, 0, -3]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1853, -345, -110]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1853, -345, -110]] 
 ![![47, 0, 0], ![29, 1, 0], ![31, 0, 1]] where
  M :=![![![-1853, -345, -110], ![8095, -2323, -2995], ![25665, 1680, -1288]]]
  hmulB := by decide  
  f := ![![![-8023624, 629160, -777745]], ![![-3537123, 277358, -342860]], ![![-6850037, 537135, -663987]]]
  g := ![![![246, -345, -110], ![3581, -2323, -2995], ![359, 1680, -1288]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-15, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-15, 1, 0]] 
 ![![47, 0, 0], ![32, 1, 0], ![10, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-15, 1, 0], ![3, -13, 9], ![-83, -2, -16]]]
  hmulB := by decide  
  f := ![![![541, -2596, 1800], ![-188, -9400, 0]], ![![364, -1765, 1224], ![-140, -6392, 0]], ![![125, -553, 383], ![-9, -2000, 0]]]
  g := ![![![1, 0, 0], ![-32, 47, 0], ![-10, 0, 47]], ![![-1, 1, 0], ![7, -13, 9], ![3, -2, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1853, -345, -110]] ![![47, 0, 0], ![-15, 1, 0]]
  ![![47, 0, 0], ![-1, 7, 1]] where
 M := ![![![-87091, -16215, -5170], ![35890, 2852, -1345]]]
 hmul := by decide  
 g := ![![![![-1853, -345, -110], ![0, 0, 0]], ![![764, 58, -29], ![18, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-1, 7, 1]] ![![47, 0, 0], ![-15, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-705, 47, 0]], ![![-47, 329, 47], ![-47, -94, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-15, 1, 0]]], ![![![-1, 7, 1]], ![![-1, -2, 1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-21, 16, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-21, 16, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![32, 16, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-21, 16, 1], ![-35, 9, 143], ![-1301, -41, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -16, 53]], ![![-1, 0, 1], ![-87, -43, 143], ![-1, 11, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [45, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 52], [0, 1]]
 g := ![![[35, 6], [1], [23, 25], [17], [15, 1]], ![[19, 47], [1], [27, 28], [17], [30, 52]]]
 h' := ![![[15, 52], [50, 18], [25, 52], [14, 48], [14, 21], [0, 1]], ![[0, 1], [2, 35], [10, 1], [45, 5], [11, 32], [15, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [18, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [45, 38, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1149, -2562, -975]
  a := ![-5, -3, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![567, 246, -975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![16, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![16, 1, 0]] 
 ![![53, 0, 0], ![16, 1, 0], ![39, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![16, 1, 0], ![3, 18, 9], ![-83, -2, 15]]]
  hmulB := by decide  
  f := ![![![-833, -5574, -2790], ![-318, 16430, 0]], ![![-247, -1672, -837], ![-105, 4929, 0]], ![![-619, -4102, -2053], ![-214, 12090, 0]]]
  g := ![![![1, 0, 0], ![-16, 53, 0], ![-39, 0, 53]], ![![0, 1, 0], ![-12, 18, 9], ![-12, -2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-21, 16, 1]] ![![53, 0, 0], ![16, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![848, 53, 0]], ![![-1113, 848, 53], ![-371, 265, 159]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![16, 1, 0]]], ![![![-21, 16, 1]], ![![-7, 5, 3]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [15, 51, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16, 2], [30, 42, 57], [0, 1]]
 g := ![![[47, 40, 25], [8, 52, 7], [40, 20], [38, 3, 27], [1]], ![[26, 14, 34, 13], [41, 49, 43, 11], [6, 1], [11, 43, 22, 38], [42, 46, 43, 8]], ![[44, 9, 50, 57], [16, 14, 44, 46], [36, 48], [54, 39, 22, 45], [33, 51, 4, 51]]]
 h' := ![![[3, 16, 2], [57, 49, 54], [36, 28, 40], [20, 12, 43], [44, 8, 33], [0, 1]], ![[30, 42, 57], [50, 21, 6], [54, 3, 25], [47, 16, 1], [46, 19, 45], [3, 16, 2]], ![[0, 1], [50, 48, 58], [7, 28, 53], [55, 31, 15], [14, 32, 40], [30, 42, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 28], []]
 b := ![[], [52, 51, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [15, 51, 26, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1411280, -70800, 35931]
  a := ![-4, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23920, -1200, 609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![5, -28, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![5, -28, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![5, 33, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![5, -28, 1], ![-167, -53, -253], ![2351, 47, 31]]]
  hmulB := by decide  
  f := ![![![-4, 28, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -33, 61]], ![![0, -1, 1], ![18, 136, -253], ![36, -16, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [10, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 60], [0, 1]]
 g := ![![[48, 45], [42], [46, 60], [48, 49], [8, 1]], ![[42, 16], [42], [38, 1], [13, 12], [16, 60]]]
 h' := ![![[8, 60], [59, 17], [28, 15], [8, 11], [42, 54], [0, 1]], ![[0, 1], [12, 44], [26, 46], [35, 50], [47, 7], [8, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [41, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [10, 53, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-131133, -52665, -1973]
  a := ![25, 23, 74]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1988, 204, -1973]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![9, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![9, 1, 0]] 
 ![![61, 0, 0], ![9, 1, 0], ![30, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![9, 1, 0], ![3, 11, 9], ![-83, -2, 8]]]
  hmulB := by decide  
  f := ![![![196, 747, 612], ![61, -4148, 0]], ![![21, 109, 90], ![62, -610, 0]], ![![93, 367, 301], ![53, -2040, 0]]]
  g := ![![![1, 0, 0], ![-9, 61, 0], ![-30, 0, 61]], ![![0, 1, 0], ![-6, 11, 9], ![-5, -2, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![5, -28, 1]] ![![61, 0, 0], ![9, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![549, 61, 0]], ![![305, -1708, 61], ![-122, -305, -244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![9, 1, 0]]], ![![![5, -28, 1]], ![![-2, -5, -4]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [16, 18, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 64, 49], [7, 2, 18], [0, 1]]
 g := ![![[20, 46, 36], [45, 30, 55], [34, 39], [57, 9], [22, 1], []], ![[34, 1, 38, 54], [61, 53, 5, 16], [51, 6], [9, 59], [30, 4], [0, 56]], ![[34, 22, 43, 5], [31, 56, 63, 61], [60, 25], [44, 29], [44, 9], [31, 56]]]
 h' := ![![[15, 64, 49], [17, 16, 6], [57, 5, 16], [47, 41, 21], [50, 57, 64], [0, 0, 1], [0, 1]], ![[7, 2, 18], [66, 66, 59], [47, 21, 9], [27, 8, 41], [29, 40, 40], [24, 19, 2], [15, 64, 49]], ![[0, 1], [60, 52, 2], [42, 41, 42], [59, 18, 5], [48, 37, 30], [22, 48, 64], [7, 2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 6], []]
 b := ![[], [57, 36, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [16, 18, 45, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-367763, -40468, -7973]
  a := ![-3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5489, -604, -119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7345, -576, 712]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![7345, -576, 712]] 
 ![![71, 0, 0], ![0, 71, 0], ![16, 67, 1]] where
  M :=![![![7345, -576, 712], ![-60824, 4769, -5896], ![67032, -5256, 6497]]]
  hmulB := by decide  
  f := ![![![-73, 0, 8]], ![![-664, -89, -8]], ![![-640, -85, -7]]]
  g := ![![![-57, -680, 712], ![472, 5631, -5896], ![-520, -6205, 6497]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [31, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 70], [0, 1]]
 g := ![![[61, 37], [45, 25], [26, 16], [50], [37], [1]], ![[29, 34], [56, 46], [16, 55], [50], [37], [1]]]
 h' := ![![[26, 70], [25, 26], [46, 5], [31, 67], [27, 60], [40, 26], [0, 1]], ![[0, 1], [62, 45], [34, 66], [69, 4], [25, 11], [6, 45], [26, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [25, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [31, 45, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5053, -4044, 372]
  a := ![7, 5, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-155, -408, 372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 0, 8]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-73, 0, 8]] 
 ![![71, 0, 0], ![37, 1, 0], ![53, 0, 1]] where
  M :=![![![-73, 0, 8], ![-664, -89, -8], ![216, -72, -89]]]
  hmulB := by decide  
  f := ![![![7345, -576, 712]], ![![2971, -233, 288]], ![![6427, -504, 623]]]
  g := ![![![-7, 0, 8], ![43, -89, -8], ![107, -72, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![7345, -576, 712]] ![![-73, 0, 8]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [3, 40, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 34, 35], [58, 38, 38], [0, 1]]
 g := ![![[33, 29, 18], [40, 65], [16, 64], [49, 52, 57], [32, 1], []], ![[27, 60, 26, 49], [63, 54], [63, 35], [58, 50, 64, 19], [45, 57], [43, 57]], ![[13, 61, 7, 67], [51, 16], [42, 54], [24, 33, 55, 3], [9, 61], [40, 57]]]
 h' := ![![[47, 34, 35], [45, 50, 23], [26, 6, 49], [72, 19, 8], [50, 31, 35], [0, 0, 1], [0, 1]], ![[58, 38, 38], [11, 33, 69], [28, 55, 28], [12, 63, 20], [66, 9, 6], [36, 64, 38], [47, 34, 35]], ![[0, 1], [31, 63, 54], [44, 12, 69], [43, 64, 45], [48, 33, 32], [32, 9, 34], [58, 38, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 7], []]
 b := ![[], [17, 68, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [3, 40, 41, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51110147, -1828650, 1460000]
  a := ![-15, -10, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-700139, -25050, 20000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [47, 64, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 29, 3], [50, 49, 76], [0, 1]]
 g := ![![[3, 18, 51], [31, 26, 9], [1, 78, 22], [41, 8, 1], [67, 1], []], ![[51, 65, 61, 37], [16, 69, 20, 7], [21, 29, 61, 56], [58, 53], [63, 31], [66, 9]], ![[54, 70, 74, 2], [58, 57, 5, 64], [44, 72, 0, 49], [22, 6, 27, 76], [6, 51], [72, 9]]]
 h' := ![![[17, 29, 3], [44, 30, 50], [32, 75, 3], [48, 44, 38], [11, 10, 1], [0, 0, 1], [0, 1]], ![[50, 49, 76], [50, 73, 12], [57, 40, 56], [78, 13, 19], [54, 26], [31, 52, 49], [17, 29, 3]], ![[0, 1], [4, 55, 17], [24, 43, 20], [19, 22, 22], [22, 43, 78], [64, 27, 29], [50, 49, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 12], []]
 b := ![[], [12, 44, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [47, 64, 12, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72759, -5056, 10112]
  a := ![2, -2, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![921, -64, 128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB123I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB123I1 : PrimesBelowBoundCertificateInterval O 31 79 123 where
  m := 11
  g := ![2, 2, 2, 3, 2, 1, 2, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB123I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N0, I47N1, I53N1, I61N1, I71N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N0, I47N1, I47N1], [I53N1], [], [I61N1], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
