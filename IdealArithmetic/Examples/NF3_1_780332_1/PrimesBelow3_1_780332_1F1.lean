
import IdealArithmetic.Examples.NF3_1_780332_1.RI3_1_780332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-90, -21, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-90, -21, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![21, 16, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-90, -21, 1], ![558, 34, -21], ![-11718, -2046, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -16, 37]], ![![-3, -1, 1], ![27, 10, -21], ![-336, -70, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [15, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 36], [0, 1]]
 g := ![![[28, 3], [27], [6, 36], [21], [1]], ![[26, 34], [27], [19, 1], [21], [1]]]
 h' := ![![[24, 36], [36, 22], [21, 8], [21, 6], [22, 24], [0, 1]], ![[0, 1], [9, 15], [28, 29], [17, 31], [6, 13], [24, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [25, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [15, 13, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1131, 793, 112]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -27, 112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-16, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-16, 1, 0]] 
 ![![37, 0, 0], ![21, 1, 0], ![3, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-16, 1, 0], ![0, -16, 1], ![558, 124, -16]]]
  hmulB := by decide  
  f := ![![![209, -13, 0], ![481, 0, 0]], ![![129, -8, 0], ![297, 0, 0]], ![![23, -1, 0], ![53, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 37, 0], ![-3, 0, 37]], ![![-1, 1, 0], ![9, -16, 1], ![-54, 124, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-90, -21, 1]] ![![37, 0, 0], ![-16, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-592, 37, 0]], ![![-3330, -777, 37], ![1998, 370, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-16, 1, 0]]], ![![![-90, -21, 1]], ![![54, 10, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [12, 36, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6, 18], [40, 34, 23], [0, 1]]
 g := ![![[27, 15, 23], [8, 40], [33, 16], [14, 3, 1], []], ![[38, 7, 27, 1], [31, 39], [16, 18], [36, 22, 16, 21], [40, 37]], ![[11, 15, 12, 40], [8, 4], [19, 32], [37, 39, 35, 8], [35, 37]]]
 h' := ![![[4, 6, 18], [25, 29, 33], [30, 29, 32], [37, 34, 4], [0, 0, 1], [0, 1]], ![[40, 34, 23], [40, 20, 4], [17, 11, 11], [39, 35, 10], [28, 9, 34], [4, 6, 18]], ![[0, 1], [27, 33, 4], [0, 1, 39], [8, 13, 27], [32, 32, 6], [40, 34, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 20], []]
 b := ![[], [40, 40, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [12, 36, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4431649, 3048924, 428573]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108089, 74364, 10453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-72, 3, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-72, 3, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![14, 3, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-72, 3, 1], ![558, 52, 3], ![1674, 930, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -3, 43]], ![![-2, 0, 1], ![12, 1, 3], ![22, 18, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [13, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 42], [0, 1]]
 g := ![![[2, 10], [13, 31], [6], [42, 31], [1]], ![[0, 33], [24, 12], [6], [10, 12], [1]]]
 h' := ![![[17, 42], [3, 15], [5, 26], [13, 7], [30, 17], [0, 1]], ![[0, 1], [0, 28], [17, 17], [3, 36], [18, 26], [17, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [34, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [13, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1329, 208, 227]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -11, 227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, 1, 0]] 
 ![![43, 0, 0], ![40, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, 1, 0], ![0, -3, 1], ![558, 124, -3]]]
  hmulB := by decide  
  f := ![![![94, -31, 0], ![1333, 0, 0]], ![![88, -29, 0], ![1248, 0, 0]], ![![76, -25, 0], ![1078, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 43, 0], ![-34, 0, 43]], ![![-1, 1, 0], ![2, -3, 1], ![-100, 124, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-72, 3, 1]] ![![43, 0, 0], ![-3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-129, 43, 0]], ![![-3096, 129, 43], ![774, 43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-3, 1, 0]]], ![![![-72, 3, 1]], ![![18, 1, 0]]]]
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
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [28, 45, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 44, 19], [36, 2, 28], [0, 1]]
 g := ![![[16, 17, 6], [11, 24, 21], [44, 6, 21], [29, 11, 1], []], ![[15, 22, 18, 22], [11, 10, 12, 23], [15, 20, 44, 10], [27, 17, 44, 29], [3, 32]], ![[27, 0, 19, 36], [41, 36], [2, 29, 29, 25], [28, 12, 12, 17], [41, 32]]]
 h' := ![![[22, 44, 19], [21, 14, 10], [37, 42, 16], [34, 32, 31], [0, 0, 1], [0, 1]], ![[36, 2, 28], [5, 31, 4], [29, 19, 31], [25, 41, 12], [24, 12, 2], [22, 44, 19]], ![[0, 1], [31, 2, 33], [16, 33], [40, 21, 4], [7, 35, 44], [36, 2, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 32], []]
 b := ![[], [42, 19, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [28, 45, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6668548, -3159152, -357999]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-141884, -67216, -7617]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![2, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![2, 1, 0]] 
 ![![53, 0, 0], ![2, 1, 0], ![49, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![2, 1, 0], ![0, 2, 1], ![558, 124, 2]]]
  hmulB := by decide  
  f := ![![![51, 25, 0], ![-1325, 0, 0]], ![![-2, -1, 0], ![54, 0, 0]], ![![47, 23, 0], ![-1221, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 53, 0], ![-49, 0, 53]], ![![0, 1, 0], ![-1, 2, 1], ![4, 124, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![0, 10, 1], ![558, 124, 10]]]
  hmulB := by decide  
  f := ![![![141, 14, 0], ![-742, 0, 0]], ![![10, 1, 0], ![-52, 0, 0]], ![![2, 0, 0], ![-10, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-6, 0, 53]], ![![0, 1, 0], ![-2, 10, 1], ![-14, 124, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-12, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-12, 1, 0]] 
 ![![53, 0, 0], ![41, 1, 0], ![15, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-12, 1, 0], ![0, -12, 1], ![558, 124, -12]]]
  hmulB := by decide  
  f := ![![![445, -37, 0], ![1961, 0, 0]], ![![361, -30, 0], ![1591, 0, 0]], ![![135, -11, 0], ![595, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 53, 0], ![-15, 0, 53]], ![![-1, 1, 0], ![9, -12, 1], ![-82, 124, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![2, 1, 0]] ![![53, 0, 0], ![10, 1, 0]]
  ![![53, 0, 0], ![-86, 12, 1]] where
 M := ![![![2809, 0, 0], ![530, 53, 0]], ![![106, 53, 0], ![20, 12, 1]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![10, 1, 0], ![0, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-86, 12, 1]] ![![53, 0, 0], ![-12, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-636, 53, 0]], ![![-4558, 636, 53], ![1590, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-12, 1, 0]]], ![![![-86, 12, 1]], ![![30, -2, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-71, -17, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-71, -17, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![47, 42, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-71, -17, 1], ![558, 53, -17], ![-9486, -1550, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -42, 59]], ![![-2, -1, 1], ![23, 13, -17], ![-203, -64, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [46, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 58], [0, 1]]
 g := ![![[20, 9], [1, 27], [9], [49, 1], [24, 1]], ![[0, 50], [0, 32], [9], [14, 58], [48, 58]]]
 h' := ![![[24, 58], [13, 56], [25, 26], [47, 3], [17, 58], [0, 1]], ![[0, 1], [0, 3], [0, 33], [1, 56], [52, 1], [24, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [41, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [46, 35, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1162, 771, 90]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -51, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, 1, 0]] 
 ![![59, 0, 0], ![17, 1, 0], ![6, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, 1, 0], ![0, 17, 1], ![558, 124, 17]]]
  hmulB := by decide  
  f := ![![![86, 5, 0], ![-295, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-12, -1, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 59, 0], ![-6, 0, 59]], ![![0, 1, 0], ![-5, 17, 1], ![-28, 124, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-71, -17, 1]] ![![59, 0, 0], ![17, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1003, 59, 0]], ![![-4189, -1003, 59], ![-649, -236, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![17, 1, 0]]], ![![![-71, -17, 1]], ![![-11, -4, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [24, 0, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 2, 17], [43, 58, 44], [0, 1]]
 g := ![![[32, 48, 19], [9, 9], [22, 45, 56], [52, 38, 49], [1]], ![[34, 37, 9, 21], [58, 14], [53, 28, 9, 18], [60, 30, 31, 55], [55, 10, 13, 33]], ![[19, 52, 22, 51], [25, 27], [7, 37, 32, 44], [38, 37, 31, 23], [51, 40, 35, 28]]]
 h' := ![![[25, 2, 17], [42, 40, 18], [21, 9, 58], [33, 30, 42], [37, 0, 7], [0, 1]], ![[43, 58, 44], [7, 8, 16], [22, 30, 40], [15, 14, 18], [31, 33, 40], [25, 2, 17]], ![[0, 1], [19, 13, 27], [58, 22, 24], [1, 17, 1], [20, 28, 14], [43, 58, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11], []]
 b := ![[], [9, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [24, 0, 54, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9291337, 2772145, 209230]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![152317, 45445, 3430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [1, 16, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 38, 29], [31, 28, 38], [0, 1]]
 g := ![![[14, 45, 19], [21, 54, 59], [32, 1], [40, 25], [17, 1], []], ![[15, 44, 28, 19], [40, 46, 18, 47], [63, 54], [14, 25], [40, 47], [19, 37]], ![[45, 4, 55, 32], [31, 32, 40, 50], [2, 10], [], [8, 37], [10, 37]]]
 h' := ![![[53, 38, 29], [46, 48, 32], [61, 6, 27], [48, 41, 1], [50, 62, 5], [0, 0, 1], [0, 1]], ![[31, 28, 38], [13, 12, 10], [66, 14, 59], [53, 19, 11], [0, 21, 62], [43, 2, 28], [53, 38, 29]], ![[0, 1], [7, 7, 25], [62, 47, 48], [59, 7, 55], [27, 51], [13, 65, 38], [31, 28, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 46], []]
 b := ![[], [66, 48, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [1, 16, 50, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![169108, -20703, -7370]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2524, -309, -110]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![3, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![3, 1, 0]] 
 ![![71, 0, 0], ![3, 1, 0], ![62, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![3, 1, 0], ![0, 3, 1], ![558, 124, 3]]]
  hmulB := by decide  
  f := ![![![67, 22, 0], ![-1562, 0, 0]], ![![-3, -1, 0], ![72, 0, 0]], ![![58, 19, 0], ![-1352, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 71, 0], ![-62, 0, 71]], ![![0, 1, 0], ![-1, 3, 1], ![0, 124, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![26, 1, 0]] 
 ![![71, 0, 0], ![26, 1, 0], ![34, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![26, 1, 0], ![0, 26, 1], ![558, 124, 26]]]
  hmulB := by decide  
  f := ![![![651, 25, 0], ![-1775, 0, 0]], ![![234, 9, 0], ![-638, 0, 0]], ![![270, 10, 0], ![-736, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 71, 0], ![-34, 0, 71]], ![![0, 1, 0], ![-10, 26, 1], ![-50, 124, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-29, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-29, 1, 0]] 
 ![![71, 0, 0], ![42, 1, 0], ![11, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-29, 1, 0], ![0, -29, 1], ![558, 124, -29]]]
  hmulB := by decide  
  f := ![![![1770, -61, 0], ![4331, 0, 0]], ![![1074, -37, 0], ![2628, 0, 0]], ![![302, -10, 0], ![739, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 71, 0], ![-11, 0, 71]], ![![-1, 1, 0], ![17, -29, 1], ![-61, 124, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![3, 1, 0]] ![![71, 0, 0], ![26, 1, 0]]
  ![![71, 0, 0], ![-64, 29, 1]] where
 M := ![![![5041, 0, 0], ![1846, 71, 0]], ![![213, 71, 0], ![78, 29, 1]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![26, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-64, 29, 1]] ![![71, 0, 0], ![-29, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2059, 71, 0]], ![![-4544, 2059, 71], ![2414, -781, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-29, 1, 0]]], ![![![-64, 29, 1]], ![![34, -11, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [45, 70, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 24, 58], [29, 48, 15], [0, 1]]
 g := ![![[61, 1, 18], [58, 1], [50, 35], [19, 12, 8], [58, 1], []], ![[67, 36, 69, 15], [34, 41], [48, 23], [22, 61, 18, 5], [34, 41], [66, 6]], ![[24, 59, 53, 21], [51, 65], [45, 49], [68, 46, 68, 39], [51, 65], [36, 6]]]
 h' := ![![[29, 24, 58], [55, 56, 50], [16, 0, 72], [21, 60, 20], [18, 56, 9], [0, 0, 1], [0, 1]], ![[29, 48, 15], [57, 38, 27], [28, 67, 25], [61, 27, 60], [1, 11, 30], [61, 6, 48], [29, 24, 58]], ![[0, 1], [32, 52, 69], [65, 6, 49], [51, 59, 66], [33, 6, 34], [24, 67, 24], [29, 48, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 19], []]
 b := ![[], [63, 35, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [45, 70, 15, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3355299, 1336046, 138043]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45963, 18302, 1891]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-102, -38, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-102, -38, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![56, 41, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-102, -38, 1], ![558, 22, -38], ![-21204, -4154, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -41, 79]], ![![-2, -1, 1], ![34, 20, -38], ![-284, -64, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [64, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 78], [0, 1]]
 g := ![![[63, 21], [77, 52], [35, 38], [66, 22], [9], [1]], ![[0, 58], [0, 27], [0, 41], [0, 57], [9], [1]]]
 h' := ![![[76, 78], [49, 69], [51, 17], [42, 14], [44, 41], [15, 76], [0, 1]], ![[0, 1], [0, 10], [0, 62], [0, 65], [0, 38], [24, 3], [76, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [24, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [64, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22246, -2798, 610]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-714, -352, 610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![38, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![38, 1, 0]] 
 ![![79, 0, 0], ![38, 1, 0], ![57, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![38, 1, 0], ![0, 38, 1], ![558, 124, 38]]]
  hmulB := by decide  
  f := ![![![913, 24, 0], ![-1896, 0, 0]], ![![418, 11, 0], ![-868, 0, 0]], ![![627, 16, 0], ![-1302, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 79, 0], ![-57, 0, 79]], ![![0, 1, 0], ![-19, 38, 1], ![-80, 124, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-102, -38, 1]] ![![79, 0, 0], ![38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![3002, 79, 0]], ![![-8058, -3002, 79], ![-3318, -1422, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![38, 1, 0]]], ![![![-102, -38, 1]], ![![-42, -18, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB250I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB250I1 : PrimesBelowBoundCertificateInterval O 31 79 250 where
  m := 11
  g := ![2, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB250I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![389017]
    · exact ![6241, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I53N0, I53N1, I53N2, I59N1, I71N0, I71N1, I71N2, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N0, I53N1, I53N2], [I59N1], [], [], [I71N0, I71N1, I71N2], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
