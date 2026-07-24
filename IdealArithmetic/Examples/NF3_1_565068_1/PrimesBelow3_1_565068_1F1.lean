
import IdealArithmetic.Examples.NF3_1_565068_1.RI3_1_565068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, 1, 0]] 
 ![![37, 0, 0], ![15, 1, 0], ![26, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, 1, 0], ![0, 16, 5], ![-45, -29, 15]]]
  hmulB := by decide  
  f := ![![![46, 3, 0], ![-111, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![38, -4, -2], ![-92, 15, 0]]]
  g := ![![![1, 0, 0], ![-15, 37, 0], ![-26, 0, 37]], ![![0, 1, 0], ![-10, 16, 5], ![0, -29, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-15, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-15, 1, 0]] 
 ![![37, 0, 0], ![22, 1, 0], ![32, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-15, 1, 0], ![0, -14, 5], ![-45, -29, -15]]]
  hmulB := by decide  
  f := ![![![166, -11, 0], ![407, 0, 0]], ![![106, -7, 0], ![260, 0, 0]], ![![146, -4, -2], ![358, 15, 0]]]
  g := ![![![1, 0, 0], ![-22, 37, 0], ![-32, 0, 37]], ![![-1, 1, 0], ![4, -14, 5], ![29, -29, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-1, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-1, 1, 0]] 
 ![![37, 0, 0], ![36, 1, 0], ![0, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-1, 1, 0], ![0, 0, 5], ![-45, -29, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![0, 15, 0]]]
  g := ![![![1, 0, 0], ![-36, 37, 0], ![0, 0, 37]], ![![-1, 1, 0], ![0, 0, 5], ![27, -29, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, 1, 0]] ![![37, 0, 0], ![-15, 1, 0]]
  ![![37, 0, 0], ![29, 15, 1]] where
 M := ![![![1369, 0, 0], ![-555, 37, 0]], ![![555, 37, 0], ![-225, 1, 5]]]
 hmul := by decide  
 g := ![![![![8, -15, -1], ![37, 0, 0]], ![![-15, 1, 0], ![0, 0, 0]]], ![![![-14, -14, -1], ![37, 0, 0]], ![![-10, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![29, 15, 1]] ![![37, 0, 0], ![-1, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-37, 37, 0]], ![![1073, 555, 37], ![-74, 0, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-1, 1, 0]]], ![![![29, 15, 1]], ![![-2, 0, 2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, -17, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, -17, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![15, 24, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, -17, 1], ![-45, -31, -85], ![774, 484, -14]]]
  hmulB := by decide  
  f := ![![![-14, 17, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -24, 41]], ![![0, -1, 1], ![30, 49, -85], ![24, 20, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [9, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40], [0, 1]]
 g := ![![[7, 32], [20], [23], [39, 33], [1]], ![[0, 9], [20], [23], [10, 8], [1]]]
 h' := ![![[19, 40], [20, 27], [35, 26], [18, 33], [32, 19], [0, 1]], ![[0, 1], [0, 14], [37, 15], [30, 8], [24, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [21, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [9, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-882, -1813, -2527]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![903, 1435, -2527]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![3, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![3, 1, 0]] 
 ![![41, 0, 0], ![3, 1, 0], ![14, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![3, 1, 0], ![0, 4, 5], ![-45, -29, 3]]]
  hmulB := by decide  
  f := ![![![31, 10, 0], ![-410, 0, 0]], ![![-3, -1, 0], ![42, 0, 0]], ![![10, 0, -4], ![-132, 33, 0]]]
  g := ![![![1, 0, 0], ![-3, 41, 0], ![-14, 0, 41]], ![![0, 1, 0], ![-2, 4, 5], ![0, -29, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![15, -17, 1]] ![![41, 0, 0], ![3, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![123, 41, 0]], ![![615, -697, 41], ![0, -82, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![3, 1, 0]]], ![![![15, -17, 1]], ![![0, -2, -2]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [25, 27, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 11, 29], [38, 31, 14], [0, 1]]
 g := ![![[23, 39, 41], [5, 41, 35], [42, 23], [27, 22, 1], []], ![[29, 12, 30, 28], [25, 40, 42, 28], [32, 31], [18, 22, 27, 5], [5, 24]], ![[25, 6], [34, 27, 25, 6], [0, 21], [35, 25, 38, 17], [20, 24]]]
 h' := ![![[27, 11, 29], [4, 12, 16], [22, 39, 32], [13, 11, 18], [0, 0, 1], [0, 1]], ![[38, 31, 14], [16, 26, 27], [21, 2, 16], [2, 34, 17], [2, 31, 31], [27, 11, 29]], ![[0, 1], [41, 5], [21, 2, 38], [8, 41, 8], [41, 12, 11], [38, 31, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 7], []]
 b := ![[], [12, 42, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [25, 27, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![237618, 285735, 256323]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5526, 6645, 5961]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 11, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 11, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![12, 11, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 11, 1], ![-45, -6, 55], ![-486, -328, -17]]]
  hmulB := by decide  
  f := ![![![-11, -11, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -11, 47]], ![![0, 0, 1], ![-15, -13, 55], ![-6, -3, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [9, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 46], [0, 1]]
 g := ![![[41, 21], [2, 17], [39, 21], [29, 2], [1]], ![[0, 26], [27, 30], [45, 26], [43, 45], [1]]]
 h' := ![![[7, 46], [29, 16], [25, 8], [21, 31], [38, 7], [0, 1]], ![[0, 1], [0, 31], [34, 39], [3, 16], [40, 40], [7, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [15, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [9, 40, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1554, -9, 59]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, -14, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-8, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-8, 1, 0]] 
 ![![47, 0, 0], ![39, 1, 0], ![17, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-8, 1, 0], ![0, -7, 5], ![-45, -29, -8]]]
  hmulB := by decide  
  f := ![![![113, -14, 0], ![658, 0, 0]], ![![89, -11, 0], ![518, 0, 0]], ![![47, -3, -2], ![274, 19, 0]]]
  g := ![![![1, 0, 0], ![-39, 47, 0], ![-17, 0, 47]], ![![-1, 1, 0], ![4, -7, 5], ![26, -29, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![12, 11, 1]] ![![47, 0, 0], ![-8, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-376, 47, 0]], ![![564, 517, 47], ![-141, -94, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-8, 1, 0]]], ![![![12, 11, 1]], ![![-3, -2, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![41, 14, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![41, 14, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 14, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![41, 14, 1], ![-45, 26, 70], ![-621, -415, 12]]]
  hmulB := by decide  
  f := ![![![-40, -14, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -14, 53]], ![![0, 0, 1], ![-55, -18, 70], ![-21, -11, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [26, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 52], [0, 1]]
 g := ![![[18, 37], [29], [27, 1], [4], [9, 1]], ![[33, 16], [29], [36, 52], [4], [18, 52]]]
 h' := ![![[9, 52], [51, 39], [40, 33], [9, 1], [31, 2], [0, 1]], ![[0, 1], [31, 14], [19, 20], [18, 52], [49, 51], [9, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [48, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [26, 44, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-820, -2453, -3995]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3075, 1009, -3995]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-17, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-17, 1, 0]] 
 ![![53, 0, 0], ![36, 1, 0], ![41, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-17, 1, 0], ![0, -16, 5], ![-45, -29, -17]]]
  hmulB := by decide  
  f := ![![![494, -29, 0], ![1537, 0, 0]], ![![324, -19, 0], ![1008, 0, 0]], ![![386, -13, -3], ![1201, 32, 0]]]
  g := ![![![1, 0, 0], ![-36, 53, 0], ![-41, 0, 53]], ![![-1, 1, 0], ![7, -16, 5], ![32, -29, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![41, 14, 1]] ![![53, 0, 0], ![-17, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-901, 53, 0]], ![![2173, 742, 53], ![-742, -212, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-17, 1, 0]]], ![![![41, 14, 1]], ![![-14, -4, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![2, 25, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![2, 25, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![2, 25, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![2, 25, 1], ![-45, -2, 125], ![-1116, -734, -27]]]
  hmulB := by decide  
  f := ![![![-1, -25, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -25, 59]], ![![0, 0, 1], ![-5, -53, 125], ![-18, -1, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [55, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 58], [0, 1]]
 g := ![![[58, 22], [16, 7], [7], [2, 46], [55, 1]], ![[29, 37], [47, 52], [7], [54, 13], [51, 58]]]
 h' := ![![[55, 58], [5, 50], [33, 40], [8, 19], [43, 20], [0, 1]], ![[0, 1], [41, 9], [50, 19], [50, 40], [22, 39], [55, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [22, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [55, 4, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-836, -1777, -2365]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 972, -2365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-7, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-7, 1, 0]] 
 ![![59, 0, 0], ![52, 1, 0], ![27, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-7, 1, 0], ![0, -6, 5], ![-45, -29, -7]]]
  hmulB := by decide  
  f := ![![![134, -19, 0], ![1121, 0, 0]], ![![120, -17, 0], ![1004, 0, 0]], ![![72, -9, -1], ![603, 12, 0]]]
  g := ![![![1, 0, 0], ![-52, 59, 0], ![-27, 0, 59]], ![![-1, 1, 0], ![3, -6, 5], ![28, -29, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![2, 25, 1]] ![![59, 0, 0], ![-7, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-413, 59, 0]], ![![118, 1475, 59], ![-59, -177, 118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-7, 1, 0]]], ![![![2, 25, 1]], ![![-1, -3, 2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![13, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![13, 1, 0]] 
 ![![61, 0, 0], ![13, 1, 0], ![49, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![13, 1, 0], ![0, 14, 5], ![-45, -29, 13]]]
  hmulB := by decide  
  f := ![![![378, 29, 0], ![-1769, 0, 0]], ![![78, 6, 0], ![-365, 0, 0]], ![![316, 13, -4], ![-1479, 49, 0]]]
  g := ![![![1, 0, 0], ![-13, 61, 0], ![-49, 0, 61]], ![![0, 1, 0], ![-7, 14, 5], ![-5, -29, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![17, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![17, 1, 0]] 
 ![![61, 0, 0], ![17, 1, 0], ![12, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![17, 1, 0], ![0, 18, 5], ![-45, -29, 17]]]
  hmulB := by decide  
  f := ![![![239, 14, 0], ![-854, 0, 0]], ![![51, 3, 0], ![-182, 0, 0]], ![![42, -12, -4], ![-150, 49, 0]]]
  g := ![![![1, 0, 0], ![-17, 61, 0], ![-12, 0, 61]], ![![0, 1, 0], ![-6, 18, 5], ![4, -29, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![30, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![30, 1, 0]] 
 ![![61, 0, 0], ![30, 1, 0], ![58, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![30, 1, 0], ![0, 31, 5], ![-45, -29, 30]]]
  hmulB := by decide  
  f := ![![![1711, 57, 0], ![-3477, 0, 0]], ![![810, 27, 0], ![-1646, 0, 0]], ![![1618, 60, 1], ![-3288, -12, 0]]]
  g := ![![![1, 0, 0], ![-30, 61, 0], ![-58, 0, 61]], ![![0, 1, 0], ![-20, 31, 5], ![-15, -29, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![13, 1, 0]] ![![61, 0, 0], ![17, 1, 0]]
  ![![61, 0, 0], ![32, -6, 1]] where
 M := ![![![3721, 0, 0], ![1037, 61, 0]], ![![793, 61, 0], ![221, 31, 5]]]
 hmul := by decide  
 g := ![![![![29, 6, -1], ![61, 0, 0]], ![![-15, 7, -1], ![61, 0, 0]]], ![![![-19, 7, -1], ![61, 0, 0]], ![![1, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![32, -6, 1]] ![![61, 0, 0], ![30, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1830, 61, 0]], ![![1952, -366, 61], ![915, -183, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![30, 1, 0]]], ![![![32, -6, 1]], ![![15, -3, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [10, 65, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 39, 57], [0, 27, 10], [0, 1]]
 g := ![![[32, 16, 24], [20, 2, 59], [3, 26], [58, 6], [15, 1], []], ![[29, 48, 39, 42], [14, 58, 64, 2], [20, 17], [26, 17], [55, 59], [50, 33]], ![[0, 22, 58, 55], [1, 52, 49, 14], [44, 24], [58, 64], [13, 47], [30, 33]]]
 h' := ![![[15, 39, 57], [1, 60, 15], [24, 30, 40], [11, 19, 48], [51, 20, 26], [0, 0, 1], [0, 1]], ![[0, 27, 10], [59, 25, 6], [60, 44, 43], [27, 33, 34], [35, 28, 33], [60, 2, 27], [15, 39, 57]], ![[0, 1], [57, 49, 46], [17, 60, 51], [16, 15, 52], [23, 19, 8], [35, 65, 39], [0, 27, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 60], []]
 b := ![[], [12, 63, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [10, 65, 52, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![583682627, 591745407, 409615287]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8711681, 8832021, 6113661]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-1, 9, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-1, 9, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![70, 9, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-1, 9, 1], ![-45, -21, 45], ![-396, -270, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -9, 71]], ![![-1, 0, 1], ![-45, -6, 45], ![24, 0, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 70], [0, 1]]
 g := ![![[64, 32], [19, 45], [2, 1], [1], [4], [1]], ![[0, 39], [0, 26], [0, 70], [1], [4], [1]]]
 h' := ![![[69, 70], [46, 23], [31, 51], [69, 70], [36, 1], [51, 69], [0, 1]], ![[0, 1], [0, 48], [0, 20], [0, 1], [34, 70], [55, 2], [69, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [43, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [20, 2, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-800, -1249, -1401]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1370, 160, -1401]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![26, 1, 0]] 
 ![![71, 0, 0], ![26, 1, 0], ![30, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![26, 1, 0], ![0, 27, 5], ![-45, -29, 26]]]
  hmulB := by decide  
  f := ![![![547, 21, 0], ![-1491, 0, 0]], ![![182, 7, 0], ![-496, 0, 0]], ![![226, -13, -4], ![-616, 57, 0]]]
  g := ![![![1, 0, 0], ![-26, 71, 0], ![-30, 0, 71]], ![![0, 1, 0], ![-12, 27, 5], ![-1, -29, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-1, 9, 1]] ![![71, 0, 0], ![26, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1846, 71, 0]], ![![-71, 639, 71], ![-71, 213, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![26, 1, 0]]], ![![![-1, 9, 1]], ![![-1, 3, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![14, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![14, 1, 0]] 
 ![![73, 0, 0], ![14, 1, 0], ![31, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![14, 1, 0], ![0, 15, 5], ![-45, -29, 14]]]
  hmulB := by decide  
  f := ![![![519, 37, 0], ![-2701, 0, 0]], ![![98, 7, 0], ![-510, 0, 0]], ![![197, 5, -3], ![-1025, 44, 0]]]
  g := ![![![1, 0, 0], ![-14, 73, 0], ![-31, 0, 73]], ![![0, 1, 0], ![-5, 15, 5], ![-1, -29, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![18, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![18, 1, 0]] 
 ![![73, 0, 0], ![18, 1, 0], ![63, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![18, 1, 0], ![0, 19, 5], ![-45, -29, 18]]]
  hmulB := by decide  
  f := ![![![811, 45, 0], ![-3285, 0, 0]], ![![198, 11, 0], ![-802, 0, 0]], ![![693, 27, -3], ![-2807, 44, 0]]]
  g := ![![![1, 0, 0], ![-18, 73, 0], ![-63, 0, 73]], ![![0, 1, 0], ![-9, 19, 5], ![-9, -29, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-33, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-33, 1, 0]] 
 ![![73, 0, 0], ![40, 1, 0], ![37, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-33, 1, 0], ![0, -32, 5], ![-45, -29, -33]]]
  hmulB := by decide  
  f := ![![![1288, -39, 0], ![2847, 0, 0]], ![![694, -21, 0], ![1534, 0, 0]], ![![670, -1, -3], ![1481, 44, 0]]]
  g := ![![![1, 0, 0], ![-40, 73, 0], ![-37, 0, 73]], ![![-1, 1, 0], ![15, -32, 5], ![32, -29, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![14, 1, 0]] ![![73, 0, 0], ![18, 1, 0]]
  ![![73, 0, 0], ![-8, -8, 1]] where
 M := ![![![5329, 0, 0], ![1314, 73, 0]], ![![1022, 73, 0], ![252, 33, 5]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![18, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-8, -8, 1]] ![![73, 0, 0], ![-33, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2409, 73, 0]], ![![-584, -584, 73], ![219, 219, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-33, 1, 0]]], ![![![-8, -8, 1]], ![![3, 3, -1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [43, 6, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 59, 76], [2, 19, 3], [0, 1]]
 g := ![![[6, 66, 62], [5, 70, 5], [43, 49, 9], [33, 23, 20], [60, 1], []], ![[67, 64, 52, 19], [66, 58, 38, 49], [30, 73, 28, 26], [72, 78, 75, 21], [21, 45], [28, 9]], ![[48, 78, 12, 68], [77, 15, 21, 78], [53, 20, 16, 74], [43, 25, 65, 35], [8, 5], [22, 9]]]
 h' := ![![[58, 59, 76], [22, 38, 33], [47, 14, 20], [3, 16, 76], [27, 71, 39], [0, 0, 1], [0, 1]], ![[2, 19, 3], [36, 34, 39], [56, 48, 22], [60, 10, 53], [63, 57, 54], [27, 48, 19], [58, 59, 76]], ![[0, 1], [59, 7, 7], [37, 17, 37], [17, 53, 29], [8, 30, 65], [6, 31, 59], [2, 19, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 18], []]
 b := ![[], [55, 73, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [43, 6, 19, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2652820, 2804421, 2091288]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33580, 35499, 26472]
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



lemma PB213I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB213I1 : PrimesBelowBoundCertificateInterval O 31 79 213 where
  m := 11
  g := ![3, 2, 1, 2, 2, 2, 3, 1, 2, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB213I1_primes
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
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
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
      exact NI61N1
      exact NI61N2
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
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I53N1, I59N1, I61N0, I61N1, I61N2, I71N1, I73N0, I73N1, I73N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [], [I71N1], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
