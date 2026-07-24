
import IdealArithmetic.Examples.NF3_1_894348_3.RI3_1_894348_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [12, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 8, 5], [7, 28, 32], [0, 1]]
 g := ![![[16, 15, 28], [15, 12], [7, 31, 7], [0, 1], []], ![[17, 14, 20, 15], [29, 28], [8, 2, 10, 22], [26, 7], [6, 25]], ![[26, 28, 13, 29], [15, 10], [9, 0, 3, 20], [19, 27], [16, 25]]]
 h' := ![![[30, 8, 5], [31, 22, 18], [27, 9, 7], [0, 25, 28], [0, 0, 1], [0, 1]], ![[7, 28, 32], [18, 2, 22], [25, 29, 19], [32, 28, 21], [14, 15, 28], [30, 8, 5]], ![[0, 1], [16, 13, 34], [14, 36, 11], [19, 21, 25], [5, 22, 8], [7, 28, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 23], []]
 b := ![[], [25, 4, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [12, 9, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5994, -555, -555]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-162, -15, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-13, -2, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-13, -2, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![28, 39, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-13, -2, 1], ![182, -13, -14], ![-364, 26, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -39, 41]], ![![-1, -1, 1], ![14, 13, -14], ![0, 13, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [25, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[39, 23], [33], [16], [33, 40], [1]], ![[0, 18], [33], [16], [24, 1], [1]]]
 h' := ![![[9, 40], [31, 33], [35, 22], [36, 4], [16, 9], [0, 1]], ![[0, 1], [0, 8], [28, 19], [31, 37], [15, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [6, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [25, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2190, 174, 118]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-134, -108, 118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![0, 14, 7], ![182, 0, 14]]]
  hmulB := by decide  
  f := ![![![15, 1, 0], ![-41, 0, 0]], ![![-14, -1, 0], ![42, 0, 0]], ![![-13, -3, -1], ![39, 6, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-13, 0, 41]], ![![0, 1, 0], ![-7, 14, 7], ![0, 0, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-13, -2, 1]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![-533, -82, 41], ![0, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![14, 1, 0]]], ![![![-13, -2, 1]], ![![0, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![21, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![21, 1, 0]] 
 ![![43, 0, 0], ![21, 1, 0], ![23, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![21, 1, 0], ![0, 21, 7], ![182, 0, 21]]]
  hmulB := by decide  
  f := ![![![190, 9, 0], ![-387, 0, 0]], ![![84, 4, 0], ![-171, 0, 0]], ![![86, 7, 1], ![-175, -6, 0]]]
  g := ![![![1, 0, 0], ![-21, 43, 0], ![-23, 0, 43]], ![![0, 1, 0], ![-14, 21, 7], ![-7, 0, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![9, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -18, 7], ![182, 0, -18]]]
  hmulB := by decide  
  f := ![![![361, -20, 0], ![860, 0, 0]], ![![199, -11, 0], ![474, 0, 0]], ![![99, 10, -6], ![236, 37, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-9, 0, 43]], ![![-1, 1, 0], ![9, -18, 7], ![8, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, 1, 0]] 
 ![![43, 0, 0], ![40, 1, 0], ![11, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, 1, 0], ![0, -3, 7], ![182, 0, -3]]]
  hmulB := by decide  
  f := ![![![94, -31, 0], ![1333, 0, 0]], ![![88, -29, 0], ![1248, 0, 0]], ![![26, -6, -6], ![369, 37, 0]]]
  g := ![![![1, 0, 0], ![-40, 43, 0], ![-11, 0, 43]], ![![-1, 1, 0], ![1, -3, 7], ![5, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![21, 1, 0]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0], ![-11, -18, 1]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![903, 43, 0], ![-378, 3, 7]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![-7, 19, -1], ![43, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![-7, 3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-11, -18, 1]] ![![43, 0, 0], ![-3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-129, 43, 0]], ![![-473, -774, 43], ![215, 43, -129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-3, 1, 0]]], ![![![-11, -18, 1]], ![![5, 1, -3]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-11, 19, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-11, 19, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![36, 19, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-11, 19, 1], ![182, -11, 133], ![3458, 26, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -19, 47]], ![![-1, 0, 1], ![-98, -54, 133], ![82, 5, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [2, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 46], [0, 1]]
 g := ![![[42, 24], [6, 37], [28, 16], [20, 6], [1]], ![[0, 23], [0, 10], [0, 31], [33, 41], [1]]]
 h' := ![![[10, 46], [35, 20], [38, 15], [7, 4], [45, 10], [0, 1]], ![[0, 1], [0, 27], [0, 32], [0, 43], [4, 37], [10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [42, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [2, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1366, -65, 98]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46, -41, 98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 1, 0]] 
 ![![47, 0, 0], ![8, 1, 0], ![11, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 1, 0], ![0, 8, 7], ![182, 0, 8]]]
  hmulB := by decide  
  f := ![![![33, 4, 0], ![-188, 0, 0]], ![![-8, -1, 0], ![48, 0, 0]], ![![5, -4, -4], ![-28, 27, 0]]]
  g := ![![![1, 0, 0], ![-8, 47, 0], ![-11, 0, 47]], ![![0, 1, 0], ![-3, 8, 7], ![2, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-11, 19, 1]] ![![47, 0, 0], ![8, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![376, 47, 0]], ![![-517, 893, 47], ![94, 141, 141]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![8, 1, 0]]], ![![![-11, 19, 1]], ![![2, 3, 3]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![16, -5, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![16, -5, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![16, 48, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![16, -5, 1], ![182, 16, -35], ![-910, 26, 16]]]
  hmulB := by decide  
  f := ![![![-15, 5, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -48, 53]], ![![0, -1, 1], ![14, 32, -35], ![-22, -14, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [25, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 52], [0, 1]]
 g := ![![[39, 17], [40], [9, 11], [11], [32, 1]], ![[0, 36], [40], [43, 42], [11], [11, 52]]]
 h' := ![![[32, 52], [17, 21], [40, 26], [15, 8], [48, 45], [0, 1]], ![[0, 1], [0, 32], [24, 27], [6, 45], [4, 8], [32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [6, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [25, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1045, 257, -62]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 61, -62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![37, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![0, -18, 7], ![182, 0, -18]]]
  hmulB := by decide  
  f := ![![![91, -5, 0], ![265, 0, 0]], ![![73, -4, 0], ![213, 0, 0]], ![![71, 9, -5], ![207, 38, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-37, 0, 53]], ![![-1, 1, 0], ![7, -18, 7], ![16, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![16, -5, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![848, -265, 53], ![-106, 106, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![16, -5, 1]], ![![-2, 2, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, -14, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, -14, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![15, 45, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, -14, 1], ![182, 15, -98], ![-2548, 26, 15]]]
  hmulB := by decide  
  f := ![![![-14, 14, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -45, 59]], ![![0, -1, 1], ![28, 75, -98], ![-47, -11, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [30, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 58], [0, 1]]
 g := ![![[48, 46], [34, 15], [26], [34, 48], [35, 1]], ![[6, 13], [28, 44], [26], [3, 11], [11, 58]]]
 h' := ![![[35, 58], [42, 39], [40, 30], [42, 12], [12, 15], [0, 1]], ![[0, 1], [50, 20], [28, 29], [49, 47], [6, 44], [35, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [31, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [30, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![394, 2, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 13, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-20, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-20, 1, 0]] 
 ![![59, 0, 0], ![39, 1, 0], ![44, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-20, 1, 0], ![0, -20, 7], ![182, 0, -20]]]
  hmulB := by decide  
  f := ![![![101, -5, 0], ![295, 0, 0]], ![![81, -4, 0], ![237, 0, 0]], ![![76, 2, -2], ![222, 17, 0]]]
  g := ![![![1, 0, 0], ![-39, 59, 0], ![-44, 0, 59]], ![![-1, 1, 0], ![8, -20, 7], ![18, 0, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![15, -14, 1]] ![![59, 0, 0], ![-20, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1180, 59, 0]], ![![885, -826, 59], ![-118, 295, -118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-20, 1, 0]]], ![![![15, -14, 1]], ![![-2, 5, -2]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [35, 60, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 48, 14], [20, 12, 47], [0, 1]]
 g := ![![[58, 32, 39], [33, 5], [22, 20, 12], [21, 33, 9], [1]], ![[48, 37, 26, 34], [33, 14], [3, 53, 9, 56], [19, 38, 2, 47], [43, 24, 39, 60]], ![[18, 60, 45, 48], [31, 25], [21, 42, 35, 39], [18, 47, 56, 19], [27, 50, 44, 1]]]
 h' := ![![[44, 48, 14], [45, 11, 10], [23, 2, 35], [58, 30, 16], [26, 1, 3], [0, 1]], ![[20, 12, 47], [49, 15, 30], [17, 39, 21], [0, 58, 2], [48, 10, 50], [44, 48, 14]], ![[0, 1], [1, 35, 21], [54, 20, 5], [16, 34, 43], [40, 50, 8], [20, 12, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 3], []]
 b := ![[], [16, 60, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [35, 60, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9165128, 202093, 164700]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![150248, 3313, 2700]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![30, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![30, 1, 0]] 
 ![![67, 0, 0], ![30, 1, 0], ![15, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![30, 1, 0], ![0, 30, 7], ![182, 0, 30]]]
  hmulB := by decide  
  f := ![![![601, 20, 0], ![-1340, 0, 0]], ![![270, 9, 0], ![-602, 0, 0]], ![![105, -18, -5], ![-234, 48, 0]]]
  g := ![![![1, 0, 0], ![-30, 67, 0], ![-15, 0, 67]], ![![0, 1, 0], ![-15, 30, 7], ![-4, 0, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-29, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-29, 1, 0]] 
 ![![67, 0, 0], ![38, 1, 0], ![33, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-29, 1, 0], ![0, -29, 7], ![182, 0, -29]]]
  hmulB := by decide  
  f := ![![![1480, -51, 0], ![3417, 0, 0]], ![![842, -29, 0], ![1944, 0, 0]], ![![748, -5, -5], ![1727, 48, 0]]]
  g := ![![![1, 0, 0], ![-38, 67, 0], ![-33, 0, 67]], ![![-1, 1, 0], ![13, -29, 7], ![17, 0, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-1, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-1, 1, 0]] 
 ![![67, 0, 0], ![66, 1, 0], ![19, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-1, 1, 0], ![0, -1, 7], ![182, 0, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![201, 0, 0]], ![![2, -1, 0], ![68, 0, 0]], ![![2, -1, -5], ![115, 48, 0]]]
  g := ![![![1, 0, 0], ![-66, 67, 0], ![-19, 0, 67]], ![![-1, 1, 0], ![-1, -1, 7], ![3, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![30, 1, 0]] ![![67, 0, 0], ![-29, 1, 0]]
  ![![67, 0, 0], ![-19, -19, 1]] where
 M := ![![![4489, 0, 0], ![-1943, 67, 0]], ![![2010, 67, 0], ![-870, 1, 7]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![-10, 20, -1], ![67, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![-11, 2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-19, -19, 1]] ![![67, 0, 0], ![-1, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-67, 67, 0]], ![![-1273, -1273, 67], ![201, 0, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-1, 1, 0]]], ![![![-19, -19, 1]], ![![3, 0, -2]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![14, 12, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![14, 12, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![14, 12, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![14, 12, 1], ![182, 14, 84], ![2184, 26, 14]]]
  hmulB := by decide  
  f := ![![![-13, -12, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -12, 71]], ![![0, 0, 1], ![-14, -14, 84], ![28, -2, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [17, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 70], [0, 1]]
 g := ![![[35, 1], [6, 40], [15, 60], [15], [19], [1]], ![[8, 70], [62, 31], [28, 11], [15], [19], [1]]]
 h' := ![![[44, 70], [40, 70], [29, 53], [49, 29], [37, 50], [54, 44], [0, 1]], ![[0, 1], [67, 1], [18, 18], [47, 42], [36, 21], [2, 27], [44, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [2, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [17, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1101, 101, 38]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -5, 38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-13, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-13, 1, 0]] 
 ![![71, 0, 0], ![58, 1, 0], ![57, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-13, 1, 0], ![0, -13, 7], ![182, 0, -13]]]
  hmulB := by decide  
  f := ![![![196, -15, 0], ![1065, 0, 0]], ![![170, -13, 0], ![924, 0, 0]], ![![172, -2, -6], ![935, 61, 0]]]
  g := ![![![1, 0, 0], ![-58, 71, 0], ![-57, 0, 71]], ![![-1, 1, 0], ![5, -13, 7], ![13, 0, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![14, 12, 1]] ![![71, 0, 0], ![-13, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-923, 71, 0]], ![![994, 852, 71], ![0, -142, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-13, 1, 0]]], ![![![14, 12, 1]], ![![0, -2, 1]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [71, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 26, 63], [20, 46, 10], [0, 1]]
 g := ![![[63, 6, 25], [4, 48], [42, 69], [50, 61, 9], [0, 1], []], ![[69, 69, 2, 42], [60, 67], [29, 27], [14, 38, 64, 20], [29, 72], [64, 27]], ![[17, 8, 30, 51], [23, 38], [51, 38], [59, 55, 42, 60], [9, 19], [44, 27]]]
 h' := ![![[53, 26, 63], [35, 14, 68], [10, 33, 62], [27, 45, 54], [0, 2, 70], [0, 0, 1], [0, 1]], ![[20, 46, 10], [35, 49, 68], [39, 19, 40], [45, 46, 63], [55, 9, 61], [17, 63, 46], [53, 26, 63]], ![[0, 1], [65, 10, 10], [47, 21, 44], [50, 55, 29], [36, 62, 15], [50, 10, 26], [20, 46, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 58], []]
 b := ![[], [49, 64, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [71, 3, 0, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39201, 1095, 2190]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![537, 15, 30]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![12, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![12, 1, 0]] 
 ![![79, 0, 0], ![12, 1, 0], ![2, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![12, 1, 0], ![0, 12, 7], ![182, 0, 12]]]
  hmulB := by decide  
  f := ![![![325, 27, 0], ![-2133, 0, 0]], ![![36, 3, 0], ![-236, 0, 0]], ![![-10, -6, -3], ![66, 34, 0]]]
  g := ![![![1, 0, 0], ![-12, 79, 0], ![-2, 0, 79]], ![![0, 1, 0], ![-2, 12, 7], ![2, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![28, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![28, 1, 0]] 
 ![![79, 0, 0], ![28, 1, 0], ![46, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![28, 1, 0], ![0, 28, 7], ![182, 0, 28]]]
  hmulB := by decide  
  f := ![![![785, 28, 0], ![-2212, 0, 0]], ![![252, 9, 0], ![-710, 0, 0]], ![![450, 4, -3], ![-1268, 34, 0]]]
  g := ![![![1, 0, 0], ![-28, 79, 0], ![-46, 0, 79]], ![![0, 1, 0], ![-14, 28, 7], ![-14, 0, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![39, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![39, 1, 0]] 
 ![![79, 0, 0], ![39, 1, 0], ![31, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![39, 1, 0], ![0, 39, 7], ![182, 0, 39]]]
  hmulB := by decide  
  f := ![![![664, 17, 0], ![-1343, 0, 0]], ![![312, 8, 0], ![-631, 0, 0]], ![![226, -11, -3], ![-457, 34, 0]]]
  g := ![![![1, 0, 0], ![-39, 79, 0], ![-31, 0, 79]], ![![0, 1, 0], ![-22, 39, 7], ![-13, 0, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![12, 1, 0]] ![![79, 0, 0], ![28, 1, 0]]
  ![![79, 0, 0], ![-31, 17, 1]] where
 M := ![![![6241, 0, 0], ![2212, 79, 0]], ![![948, 79, 0], ![336, 40, 7]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![28, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![7, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-31, 17, 1]] ![![79, 0, 0], ![39, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![3081, 79, 0]], ![![-2449, 1343, 79], ![-1027, 632, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![39, 1, 0]]], ![![![-31, 17, 1]], ![![-13, 8, 2]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB268I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB268I1 : PrimesBelowBoundCertificateInterval O 31 79 268 where
  m := 11
  g := ![1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB268I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
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
      exact NI67N1
      exact NI67N2
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
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I59N1, I67N0, I67N1, I67N2, I71N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [I71N1], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
