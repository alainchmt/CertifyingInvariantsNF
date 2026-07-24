
import IdealArithmetic.Examples.NF3_1_780300_2.RI3_1_780300_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 8, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 10], [33, 27, 27], [0, 1]]
 g := ![![[30, 33, 33], [11, 16], [32, 25, 27], [0, 1], []], ![[0, 14, 35, 36], [1, 30], [0, 15, 3, 28], [34, 26], [32, 26]], ![[3, 16, 28, 11], [8, 21], [35, 13, 22, 12], [1, 7], [15, 26]]]
 h' := ![![[4, 9, 10], [20, 6, 12], [24, 31, 33], [0, 10, 29], [0, 0, 1], [0, 1]], ![[33, 27, 27], [6, 4, 14], [25, 12, 17], [16, 0, 32], [3, 2, 27], [4, 9, 10]], ![[0, 1], [27, 27, 11], [13, 31, 24], [1, 27, 13], [18, 35, 9], [33, 27, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 17], []]
 b := ![[], [32, 16, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 8, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14763, -518, -518]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-399, -14, -14]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, -11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, -11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![37, 30, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, -11, 1], ![170, -4, -22], ![-1870, 85, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -30, 41]], ![![-1, -1, 1], ![24, 16, -22], ![-42, 5, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [17, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 40], [0, 1]]
 g := ![![[2, 18], [31], [32], [23, 8], [1]], ![[5, 23], [31], [32], [38, 33], [1]]]
 h' := ![![[7, 40], [39, 31], [22, 20], [19, 27], [24, 7], [0, 1]], ![[0, 1], [10, 10], [39, 21], [3, 14], [32, 34], [7, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [32, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [17, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2056, 701, 104]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144, -59, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-19, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-19, 1, 0]] 
 ![![41, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-19, 1, 0], ![0, -19, 2], ![170, 0, -19]]]
  hmulB := by decide  
  f := ![![![400, -21, 0], ![861, 0, 0]], ![![210, -11, 0], ![452, 0, 0]], ![![52, 7, -1], ![112, 21, 0]]]
  g := ![![![1, 0, 0], ![-22, 41, 0], ![-4, 0, 41]], ![![-1, 1, 0], ![10, -19, 2], ![6, 0, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-4, -11, 1]] ![![41, 0, 0], ![-19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-779, 41, 0]], ![![-164, -451, 41], ![246, 205, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-19, 1, 0]]], ![![![-4, -11, 1]], ![![6, 5, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![13, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![13, 1, 0]] 
 ![![43, 0, 0], ![13, 1, 0], ![23, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![13, 1, 0], ![0, 13, 2], ![170, 0, 13]]]
  hmulB := by decide  
  f := ![![![105, 8, 0], ![-344, 0, 0]], ![![13, 1, 0], ![-42, 0, 0]], ![![61, -2, -1], ![-200, 22, 0]]]
  g := ![![![1, 0, 0], ![-13, 43, 0], ![-23, 0, 43]], ![![0, 1, 0], ![-5, 13, 2], ![-3, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-8, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-8, 1, 0]] 
 ![![43, 0, 0], ![35, 1, 0], ![11, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-8, 1, 0], ![0, -8, 2], ![170, 0, -8]]]
  hmulB := by decide  
  f := ![![![249, -31, 0], ![1333, 0, 0]], ![![209, -26, 0], ![1119, 0, 0]], ![![73, -5, -1], ![391, 22, 0]]]
  g := ![![![1, 0, 0], ![-35, 43, 0], ![-11, 0, 43]], ![![-1, 1, 0], ![6, -8, 2], ![6, 0, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-5, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-5, 1, 0]] 
 ![![43, 0, 0], ![38, 1, 0], ![9, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-5, 1, 0], ![0, -5, 2], ![170, 0, -5]]]
  hmulB := by decide  
  f := ![![![151, -30, 0], ![1290, 0, 0]], ![![136, -27, 0], ![1162, 0, 0]], ![![33, -4, -1], ![282, 22, 0]]]
  g := ![![![1, 0, 0], ![-38, 43, 0], ![-9, 0, 43]], ![![-1, 1, 0], ![4, -5, 2], ![5, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![13, 1, 0]] ![![43, 0, 0], ![-8, 1, 0]]
  ![![43, 0, 0], ![-9, -19, 1]] where
 M := ![![![1849, 0, 0], ![-344, 43, 0]], ![![559, 43, 0], ![-104, 5, 2]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![1, 20, -1], ![43, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-9, -19, 1]] ![![43, 0, 0], ![-5, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-215, 43, 0]], ![![-387, -817, 43], ![215, 86, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-5, 1, 0]]], ![![![-9, -19, 1]], ![![5, 2, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-22, -6, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-22, -6, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![25, 41, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-22, -6, 1], ![170, -22, -12], ![-1020, 85, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -41, 47]], ![![-1, -1, 1], ![10, 10, -12], ![-10, 21, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [35, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 46], [0, 1]]
 g := ![![[12, 34], [27, 27], [3, 37], [5, 9], [1]], ![[20, 13], [14, 20], [20, 10], [32, 38], [1]]]
 h' := ![![[3, 46], [42, 9], [36, 11], [13, 32], [12, 3], [0, 1]], ![[0, 1], [22, 38], [22, 36], [15, 15], [21, 44], [3, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [5, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [35, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![975, 1, 86]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -75, 86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 1, 0]] 
 ![![47, 0, 0], ![12, 1, 0], ![22, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 1, 0], ![0, 12, 2], ![170, 0, 12]]]
  hmulB := by decide  
  f := ![![![25, 2, 0], ![-94, 0, 0]], ![![-12, -1, 0], ![48, 0, 0]], ![![2, -6, -1], ![-6, 24, 0]]]
  g := ![![![1, 0, 0], ![-12, 47, 0], ![-22, 0, 47]], ![![0, 1, 0], ![-4, 12, 2], ![-2, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-22, -6, 1]] ![![47, 0, 0], ![12, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![564, 47, 0]], ![![-1034, -282, 47], ![-94, -94, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![12, 1, 0]]], ![![![-22, -6, 1]], ![![-2, -2, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, -17, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, -17, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![48, 36, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, -17, 1], ![170, -5, -34], ![-2890, 85, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -36, 53]], ![![-1, -1, 1], ![34, 23, -34], ![-50, 5, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [3, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 52], [0, 1]]
 g := ![![[46, 40], [17], [10, 29], [37], [21, 1]], ![[38, 13], [17], [36, 24], [37], [42, 52]]]
 h' := ![![[21, 52], [1, 27], [23, 32], [42, 20], [43, 14], [0, 1]], ![[0, 1], [38, 26], [6, 21], [38, 33], [19, 39], [21, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [36, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [3, 32, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-984, 799, -100]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![72, 83, -100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, 1, 0]] 
 ![![53, 0, 0], ![34, 1, 0], ![5, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, 1, 0], ![0, -19, 2], ![170, 0, -19]]]
  hmulB := by decide  
  f := ![![![419, -22, 0], ![1166, 0, 0]], ![![286, -15, 0], ![796, 0, 0]], ![![51, 7, -1], ![142, 27, 0]]]
  g := ![![![1, 0, 0], ![-34, 53, 0], ![-5, 0, 53]], ![![-1, 1, 0], ![12, -19, 2], ![5, 0, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-5, -17, 1]] ![![53, 0, 0], ![-19, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1007, 53, 0]], ![![-265, -901, 53], ![265, 318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-19, 1, 0]]], ![![![-5, -17, 1]], ![![5, 6, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-4, 23, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-4, 23, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![55, 23, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-4, 23, 1], ![170, -4, 46], ![3910, 85, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -23, 59]], ![![-1, 0, 1], ![-40, -18, 46], ![70, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [15, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[9, 4], [41, 51], [25], [24, 28], [42, 1]], ![[0, 55], [0, 8], [25], [20, 31], [25, 58]]]
 h' := ![![[42, 58], [34, 2], [15, 46], [53, 5], [19, 38], [0, 1]], ![[0, 1], [0, 57], [0, 13], [27, 54], [22, 21], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [53, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [15, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![355, 68, -15]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, 7, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![13, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![13, 1, 0]] 
 ![![59, 0, 0], ![13, 1, 0], ![4, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![13, 1, 0], ![0, 13, 2], ![170, 0, 13]]]
  hmulB := by decide  
  f := ![![![417, 32, 0], ![-1888, 0, 0]], ![![91, 7, 0], ![-412, 0, 0]], ![![8, -6, -1], ![-36, 30, 0]]]
  g := ![![![1, 0, 0], ![-13, 59, 0], ![-4, 0, 59]], ![![0, 1, 0], ![-3, 13, 2], ![2, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-4, 23, 1]] ![![59, 0, 0], ![13, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![767, 59, 0]], ![![-236, 1357, 59], ![118, 295, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![13, 1, 0]]], ![![![-4, 23, 1]], ![![2, 5, 1]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [28, 12, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 20, 50], [16, 40, 11], [0, 1]]
 g := ![![[7, 26, 39], [27, 5], [16, 46, 27], [38, 16, 9], [1]], ![[11, 32, 30, 53], [26, 41], [60, 18, 13, 31], [18, 9, 33, 28], [60, 46, 34, 11]], ![[31, 12, 13, 18], [29, 9], [22, 20, 60, 18], [50, 4, 35, 50], [4, 26, 30, 50]]]
 h' := ![![[48, 20, 50], [51, 29, 10], [40, 42, 35], [34, 2, 37], [33, 49, 3], [0, 1]], ![[16, 40, 11], [49, 20, 20], [44, 39, 23], [23, 42, 55], [27, 19, 8], [48, 20, 50]], ![[0, 1], [51, 12, 31], [3, 41, 3], [45, 17, 30], [19, 54, 50], [16, 40, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 54], []]
 b := ![[], [34, 9, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [28, 12, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2740669, 191784, 53863]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44929, 3144, 883]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![10, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![10, 1, 0]] 
 ![![67, 0, 0], ![10, 1, 0], ![17, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![10, 1, 0], ![0, 10, 2], ![170, 0, 10]]]
  hmulB := by decide  
  f := ![![![371, 37, 0], ![-2479, 0, 0]], ![![50, 5, 0], ![-334, 0, 0]], ![![81, 3, -1], ![-541, 34, 0]]]
  g := ![![![1, 0, 0], ![-10, 67, 0], ![-17, 0, 67]], ![![0, 1, 0], ![-2, 10, 2], ![0, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![22, 1, 0]] 
 ![![67, 0, 0], ![22, 1, 0], ![26, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![22, 1, 0], ![0, 22, 2], ![170, 0, 22]]]
  hmulB := by decide  
  f := ![![![573, 26, 0], ![-1742, 0, 0]], ![![198, 9, 0], ![-602, 0, 0]], ![![202, -2, -1], ![-614, 34, 0]]]
  g := ![![![1, 0, 0], ![-22, 67, 0], ![-26, 0, 67]], ![![0, 1, 0], ![-8, 22, 2], ![-6, 0, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-32, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-32, 1, 0]] 
 ![![67, 0, 0], ![35, 1, 0], ![24, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-32, 1, 0], ![0, -32, 2], ![170, 0, -32]]]
  hmulB := by decide  
  f := ![![![1793, -56, 0], ![3752, 0, 0]], ![![993, -31, 0], ![2078, 0, 0]], ![![648, -4, -1], ![1356, 34, 0]]]
  g := ![![![1, 0, 0], ![-35, 67, 0], ![-24, 0, 67]], ![![-1, 1, 0], ![16, -32, 2], ![14, 0, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![10, 1, 0]] ![![67, 0, 0], ![22, 1, 0]]
  ![![67, 0, 0], ![-24, 16, 1]] where
 M := ![![![4489, 0, 0], ![1474, 67, 0]], ![![670, 67, 0], ![220, 32, 2]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![22, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-24, 16, 1]] ![![67, 0, 0], ![-32, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2144, 67, 0]], ![![-1608, 1072, 67], ![938, -536, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-32, 1, 0]]], ![![![-24, 16, 1]], ![![14, -8, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![32, -4, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![32, -4, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![32, 67, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![32, -4, 1], ![170, 32, -8], ![-680, 85, 32]]]
  hmulB := by decide  
  f := ![![![-31, 4, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -67, 71]], ![![0, -1, 1], ![6, 8, -8], ![-24, -29, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [67, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 70], [0, 1]]
 g := ![![[49, 16], [41, 43], [45, 38], [64], [5], [1]], ![[61, 55], [20, 28], [38, 33], [64], [5], [1]]]
 h' := ![![[54, 70], [22, 67], [38, 55], [61, 40], [36, 63], [4, 54], [0, 1]], ![[0, 1], [19, 4], [26, 16], [20, 31], [30, 8], [9, 17], [54, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [33, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [67, 17, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-969, 130, 3]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -1, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![8, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![8, 1, 0]] 
 ![![71, 0, 0], ![8, 1, 0], ![39, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![8, 1, 0], ![0, 8, 2], ![170, 0, 8]]]
  hmulB := by decide  
  f := ![![![57, 7, 0], ![-497, 0, 0]], ![![-8, -1, 0], ![72, 0, 0]], ![![25, -1, -1], ![-217, 36, 0]]]
  g := ![![![1, 0, 0], ![-8, 71, 0], ![-39, 0, 71]], ![![0, 1, 0], ![-2, 8, 2], ![-2, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![32, -4, 1]] ![![71, 0, 0], ![8, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![568, 71, 0]], ![![2272, -284, 71], ![426, 0, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![8, 1, 0]]], ![![![32, -4, 1]], ![![6, 0, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [57, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 27, 54], [1, 45, 19], [0, 1]]
 g := ![![[41, 59, 36], [28, 64], [28, 72], [29, 9, 4], [0, 1], []], ![[68, 8, 55, 38], [22, 35], [2, 4], [33, 41, 42, 8], [28, 54], [69, 69]], ![[2, 36, 43, 27], [15, 71], [5, 38], [10, 2, 65, 9], [27, 72], [31, 69]]]
 h' := ![![[72, 27, 54], [48, 11, 6], [29, 20, 8], [26, 13, 46], [0, 16, 71], [0, 0, 1], [0, 1]], ![[1, 45, 19], [24, 2, 61], [16, 25, 53], [35, 36, 71], [37, 68, 44], [10, 36, 45], [72, 27, 54]], ![[0, 1], [48, 60, 6], [10, 28, 12], [52, 24, 29], [44, 62, 31], [59, 37, 27], [1, 45, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 54], []]
 b := ![[], [5, 50, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [57, 2, 0, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![115997, 1022, 2044]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1589, 14, 28]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [14, 21, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 62, 25], [78, 16, 54], [0, 1]]
 g := ![![[39, 63, 23], [6, 74, 49], [66, 78, 25], [74, 73, 67], [6, 1], []], ![[68, 55, 19, 22], [13, 24, 7, 51], [74, 24, 24, 44], [34, 2, 49, 44], [30, 19], [56, 72]], ![[45, 10, 30, 70], [20, 62, 67, 12], [33, 34, 35, 78], [8, 74, 19, 48], [45, 52], [27, 72]]]
 h' := ![![[7, 62, 25], [74, 46, 55], [24, 52, 7], [70, 56, 5], [74, 18, 15], [0, 0, 1], [0, 1]], ![[78, 16, 54], [24, 71, 55], [62, 16, 69], [26, 52, 58], [77, 20, 58], [55, 27, 16], [7, 62, 25]], ![[0, 1], [70, 41, 48], [19, 11, 3], [25, 50, 16], [10, 41, 6], [18, 52, 62], [78, 16, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 47], []]
 b := ![[], [63, 72, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [14, 21, 73, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-761244, 125610, -3950]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9636, 1590, -50]
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
  g := ![1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB250I1_primes
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
    · exact ![493039]
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
  β := ![I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I59N1, I67N0, I67N1, I67N2, I71N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
