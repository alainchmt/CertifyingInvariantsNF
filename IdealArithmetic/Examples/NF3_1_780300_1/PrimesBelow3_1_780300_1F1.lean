
import IdealArithmetic.Examples.NF3_1_780300_1.RI3_1_780300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![1, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![1, 1, 0]] 
 ![![37, 0, 0], ![1, 1, 0], ![22, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![1, 1, 0], ![0, 1, 5], ![170, 0, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -2], ![22, 15, 0]]]
  g := ![![![1, 0, 0], ![-1, 37, 0], ![-22, 0, 37]], ![![0, 1, 0], ![-3, 1, 5], ![4, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![10, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![10, 1, 0]] 
 ![![37, 0, 0], ![10, 1, 0], ![17, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![10, 1, 0], ![0, 10, 5], ![170, 0, 10]]]
  hmulB := by decide  
  f := ![![![161, 16, 0], ![-592, 0, 0]], ![![30, 3, 0], ![-110, 0, 0]], ![![61, 2, -2], ![-224, 15, 0]]]
  g := ![![![1, 0, 0], ![-10, 37, 0], ![-17, 0, 37]], ![![0, 1, 0], ![-5, 10, 5], ![0, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![35, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![0, -11, 5], ![170, 0, -11]]]
  hmulB := by decide  
  f := ![![![342, -31, 0], ![1147, 0, 0]], ![![254, -23, 0], ![852, 0, 0]], ![![336, -26, -2], ![1127, 15, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-35, 0, 37]], ![![-1, 1, 0], ![3, -11, 5], ![15, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![1, 1, 0]] ![![37, 0, 0], ![10, 1, 0]]
  ![![37, 0, 0], ![2, 17, 1]] where
 M := ![![![1369, 0, 0], ![370, 37, 0]], ![![37, 37, 0], ![10, 11, 5]]]
 hmul := by decide  
 g := ![![![![35, -17, -1], ![37, 0, 0]], ![![8, -16, -1], ![37, 0, 0]]], ![![![-1, -16, -1], ![37, 0, 0]], ![![0, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![2, 17, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![74, 629, 37], ![148, -185, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![2, 17, 1]], ![![4, -5, 2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-1, 7, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-1, 7, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![40, 7, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-1, 7, 1], ![170, -1, 35], ![1190, 34, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -7, 41]], ![![-1, 0, 1], ![-30, -6, 35], ![30, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 40], [0, 1]]
 g := ![![[28, 4], [31], [36], [9, 8], [1]], ![[0, 37], [31], [36], [35, 33], [1]]]
 h' := ![![[34, 40], [14, 2], [14, 21], [8, 35], [10, 34], [0, 1]], ![[0, 1], [0, 39], [31, 20], [9, 6], [18, 7], [34, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [40, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [31, 7, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![371, 27, -2]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 1, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![6, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![6, 1, 0]] 
 ![![41, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![6, 1, 0], ![0, 6, 5], ![170, 0, 6]]]
  hmulB := by decide  
  f := ![![![31, 5, 0], ![-205, 0, 0]], ![![-6, -1, 0], ![42, 0, 0]], ![![-1, -5, -4], ![7, 33, 0]]]
  g := ![![![1, 0, 0], ![-6, 41, 0], ![-1, 0, 41]], ![![0, 1, 0], ![-1, 6, 5], ![4, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-1, 7, 1]] ![![41, 0, 0], ![6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![246, 41, 0]], ![![-41, 287, 41], ![164, 41, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![6, 1, 0]]], ![![![-1, 7, 1]], ![![4, 1, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [1, 10, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 33, 28], [20, 9, 15], [0, 1]]
 g := ![![[23, 10, 13], [31, 18, 17], [39, 35], [42, 40, 1], []], ![[13, 33, 16, 12], [27, 14, 9, 32], [17, 6], [28, 29, 36, 32], [12, 10]], ![[22, 25, 33, 21], [1, 12, 42, 38], [0, 16], [36, 15, 26, 38], [25, 10]]]
 h' := ![![[20, 33, 28], [12, 41, 20], [5, 31, 24], [1, 13, 32], [0, 0, 1], [0, 1]], ![[20, 9, 15], [35, 41, 38], [4, 42, 9], [35, 24, 7], [1, 29, 9], [20, 33, 28]], ![[0, 1], [33, 4, 28], [36, 13, 10], [6, 6, 4], [31, 14, 33], [20, 9, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 39], []]
 b := ![[], [25, 42, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [1, 10, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149253, 6106, -9159]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3471, 142, -213]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-1, 13, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-1, 13, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![46, 13, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-1, 13, 1], ![170, -1, 65], ![2210, 34, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -13, 47]], ![![-1, 0, 1], ![-60, -18, 65], ![48, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [26, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 46], [0, 1]]
 g := ![![[40, 2], [27, 24], [5, 6], [2, 36], [1]], ![[28, 45], [24, 23], [16, 41], [21, 11], [1]]]
 h' := ![![[41, 46], [3, 40], [11, 27], [42, 10], [21, 41], [0, 1]], ![[0, 1], [45, 7], [37, 20], [29, 37], [10, 6], [41, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [7, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [26, 6, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3398, -88, 127]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -37, 127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-18, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-18, 1, 0]] 
 ![![47, 0, 0], ![29, 1, 0], ![1, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-18, 1, 0], ![0, -18, 5], ![170, 0, -18]]]
  hmulB := by decide  
  f := ![![![757, -42, 0], ![1974, 0, 0]], ![![451, -25, 0], ![1176, 0, 0]], ![![23, 6, -2], ![60, 19, 0]]]
  g := ![![![1, 0, 0], ![-29, 47, 0], ![-1, 0, 47]], ![![-1, 1, 0], ![11, -18, 5], ![4, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-1, 13, 1]] ![![47, 0, 0], ![-18, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-846, 47, 0]], ![![-47, 611, 47], ![188, -235, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-18, 1, 0]]], ![![![-1, 13, 1]], ![![4, -5, 1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-20, -7, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-20, -7, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![33, 46, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-20, -7, 1], ![170, -20, -35], ![-1190, 34, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -46, 53]], ![![-1, -1, 1], ![25, 30, -35], ![-10, 18, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [11, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 52], [0, 1]]
 g := ![![[31, 29], [9], [6, 9], [38], [30, 1]], ![[0, 24], [9], [11, 44], [38], [7, 52]]]
 h' := ![![[30, 52], [17, 33], [40, 3], [44, 50], [41, 41], [0, 1]], ![[0, 1], [0, 20], [24, 50], [7, 3], [52, 12], [30, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [17, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [11, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-985, 331, -70]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 67, -70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![20, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![0, -18, 5], ![170, 0, -18]]]
  hmulB := by decide  
  f := ![![![91, -5, 0], ![265, 0, 0]], ![![73, -4, 0], ![213, 0, 0]], ![![52, 8, -3], ![152, 32, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-20, 0, 53]], ![![-1, 1, 0], ![10, -18, 5], ![10, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-20, -7, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![-1060, -371, 53], ![530, 106, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![-20, -7, 1]], ![![10, 2, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -4, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![21, -4, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![21, 55, 1]] where
  M :=![![![21, -4, 1], ![170, 21, -20], ![-680, 34, 21]]]
  hmulB := by decide  
  f := ![![![19, 2, 1]], ![![170, 19, 10]], ![![171, 19, 10]]]
  g := ![![![0, -1, 1], ![10, 19, -20], ![-19, -19, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [22, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 58], [0, 1]]
 g := ![![[8, 51], [14, 45], [36], [8, 28], [1, 1]], ![[0, 8], [0, 14], [36], [36, 31], [2, 58]]]
 h' := ![![[1, 58], [46, 13], [35, 24], [1, 53], [37, 38], [0, 1]], ![[0, 1], [0, 46], [0, 35], [54, 6], [16, 21], [1, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [40, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [22, 58, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![362, -24, -53]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 49, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -2, -1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-19, -2, -1]] 
 ![![59, 0, 0], ![20, 1, 0], ![38, 0, 1]] where
  M :=![![![-19, -2, -1], ![-170, -19, -10], ![-340, -34, -19]]]
  hmulB := by decide  
  f := ![![![-21, 4, -1]], ![![-10, 1, 0]], ![![-2, 2, -1]]]
  g := ![![![1, -2, -1], ![10, -19, -10], ![18, -34, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![21, -4, 1]] ![![-19, -2, -1]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [52, 12, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 25, 7], [53, 35, 54], [0, 1]]
 g := ![![[8, 13, 19], [42, 45], [46, 23, 5], [16, 16, 9], [1]], ![[40, 60, 52, 44], [10, 19], [3, 38, 15, 11], [40, 57, 59, 37], [21, 33, 7, 38]], ![[8, 43, 33, 50], [24, 1], [40, 18, 58, 40], [32, 39, 33, 55], [3, 55, 29, 23]]]
 h' := ![![[11, 25, 7], [59, 8, 43], [48, 17, 17], [22, 33, 26], [9, 49, 3], [0, 1]], ![[53, 35, 54], [49, 44, 36], [9, 3, 43], [25, 54, 43], [56, 31, 21], [11, 25, 7]], ![[0, 1], [58, 9, 43], [5, 41, 1], [33, 35, 53], [3, 42, 37], [53, 35, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 52], []]
 b := ![[], [23, 45, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [52, 12, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6230113, 188673, 119926]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102133, 3093, 1966]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [39, 59, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 22, 51], [66, 44, 16], [0, 1]]
 g := ![![[43, 10, 14], [12, 65, 16], [18, 33], [6, 21], [64, 1], []], ![[5, 8, 58, 18], [2, 58, 47, 66], [8, 4], [25, 62], [29, 60], [2, 55]], ![[3, 54, 35, 40], [45, 22, 27, 21], [36, 64], [48, 23], [18, 15], [37, 55]]]
 h' := ![![[65, 22, 51], [1, 55, 9], [45, 56, 4], [55, 31, 57], [50, 4, 17], [0, 0, 1], [0, 1]], ![[66, 44, 16], [29, 17, 52], [39, 2, 17], [63, 5, 2], [57, 53, 14], [60, 61, 44], [65, 22, 51]], ![[0, 1], [33, 62, 6], [50, 9, 46], [39, 31, 8], [54, 10, 36], [32, 6, 22], [66, 44, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 2], []]
 b := ![[], [56, 21, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [39, 59, 3, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17152, -4422, 1474]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![256, -66, 22]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-31, -24, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-31, -24, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![40, 47, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-31, -24, 1], ![170, -31, -120], ![-4080, 34, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -47, 71]], ![![-1, -1, 1], ![70, 79, -120], ![-40, 21, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [12, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 70], [0, 1]]
 g := ![![[44, 6], [16, 64], [40, 37], [64], [38], [1]], ![[0, 65], [20, 7], [29, 34], [64], [38], [1]]]
 h' := ![![[40, 70], [21, 19], [17, 63], [16, 26], [43, 63], [59, 40], [0, 1]], ![[0, 1], [0, 52], [52, 8], [62, 45], [7, 8], [26, 31], [40, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [67, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [12, 31, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![692, 167, 67]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -42, 67]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-22, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-22, 1, 0]] 
 ![![71, 0, 0], ![49, 1, 0], ![31, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-22, 1, 0], ![0, -22, 5], ![170, 0, -22]]]
  hmulB := by decide  
  f := ![![![1145, -52, 0], ![3692, 0, 0]], ![![815, -37, 0], ![2628, 0, 0]], ![![521, -6, -4], ![1680, 57, 0]]]
  g := ![![![1, 0, 0], ![-49, 71, 0], ![-31, 0, 71]], ![![-1, 1, 0], ![13, -22, 5], ![12, 0, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-31, -24, 1]] ![![71, 0, 0], ![-22, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1562, 71, 0]], ![![-2201, -1704, 71], ![852, 497, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-22, 1, 0]]], ![![![-31, -24, 1]], ![![12, 7, -2]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [62, 65, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 23, 70], [71, 49, 3], [0, 1]]
 g := ![![[14, 34, 55], [14, 12], [44, 35], [65, 18, 38], [6, 1], []], ![[3, 6], [52, 27], [65, 16], [9, 47, 5, 27], [10, 65], [62, 9]], ![[10, 56, 60, 19], [0, 2], [38, 37], [66, 14, 34, 9], [48, 18], [56, 9]]]
 h' := ![![[8, 23, 70], [11, 69, 37], [52, 65, 31], [58, 37, 53], [66, 59, 44], [0, 0, 1], [0, 1]], ![[71, 49, 3], [60, 61], [46, 31, 10], [34, 60, 4], [1, 2, 8], [16, 14, 49], [8, 23, 70]], ![[0, 1], [37, 16, 36], [16, 50, 32], [67, 49, 16], [72, 12, 21], [36, 59, 23], [71, 49, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 67], []]
 b := ![[], [50, 5, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [62, 65, 67, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1299692, 108478, 16790]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17804, 1486, 230]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [68, 69, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 14, 64], [8, 64, 15], [0, 1]]
 g := ![![[10, 60, 49], [12, 63, 5], [26, 56, 19], [61, 68, 31], [39, 1], []], ![[9, 4, 0, 18], [30, 8, 32, 51], [13, 37, 6, 9], [55, 36, 41, 72], [58, 67], [60, 67]], ![[53, 42, 63, 63], [34, 27, 7, 61], [25, 58, 6, 17], [65, 68, 31, 6], [19, 38], [30, 67]]]
 h' := ![![[31, 14, 64], [53, 54, 7], [49, 27, 59], [39, 65, 16], [34, 6, 30], [0, 0, 1], [0, 1]], ![[8, 64, 15], [39, 75, 33], [66, 44, 53], [24, 8, 49], [28, 32, 13], [41, 72, 64], [31, 14, 64]], ![[0, 1], [4, 29, 39], [48, 8, 46], [69, 6, 14], [52, 41, 36], [78, 7, 14], [8, 64, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 59], []]
 b := ![[], [38, 65, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [68, 69, 40, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12008, 1580, 1501]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-152, 20, 19]
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



lemma PB250I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB250I1 : PrimesBelowBoundCertificateInterval O 31 79 250 where
  m := 11
  g := ![3, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB250I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
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
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I53N1, I59N1, I71N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [I53N1], [I59N1], [], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
