
import IdealArithmetic.Examples.NF3_1_126635_1.RI3_1_126635_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [2, 33, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 27, 7], [35, 9, 30], [0, 1]]
 g := ![![[35, 7, 9], [], [10, 2, 27], [2, 1], []], ![[9, 7, 1, 4], [22, 36], [15, 22, 30, 26], [2, 7], [32, 12]], ![[21, 26, 11, 4], [27, 36], [32, 9, 10, 4], [14, 26], [9, 12]]]
 h' := ![![[4, 27, 7], [30, 29, 3], [17, 15], [33, 6, 8], [0, 0, 1], [0, 1]], ![[35, 9, 30], [2, 4, 8], [3, 35, 31], [6, 21, 3], [26, 24, 9], [4, 27, 7]], ![[0, 1], [4, 4, 26], [24, 24, 6], [20, 10, 26], [23, 13, 27], [35, 9, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 17], []]
 b := ![[], [12, 1, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [2, 33, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-189070, 22348, 6771]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5110, 604, 183]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-5, 13, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-5, 13, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![36, 13, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-5, 13, 1], ![-72, 15, 39], ![-912, 67, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -13, 41]], ![![-1, 0, 1], ![-36, -12, 39], ![-24, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [5, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 40], [0, 1]]
 g := ![![[37, 33], [31], [21], [10, 31], [1]], ![[0, 8], [31], [21], [15, 10], [1]]]
 h' := ![![[20, 40], [11, 22], [17, 21], [32, 29], [36, 20], [0, 1]], ![[0, 1], [0, 19], [27, 20], [38, 12], [26, 21], [20, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [13, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [5, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135, -510, 273]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-243, -99, 273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![2, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![2, 1, 0]] 
 ![![41, 0, 0], ![2, 1, 0], ![39, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![2, 1, 0], ![0, 3, 3], ![-72, 7, 2]]]
  hmulB := by decide  
  f := ![![![39, 19, 0], ![-779, 0, 0]], ![![-2, -1, 0], ![42, 0, 0]], ![![37, 17, -1], ![-739, 14, 0]]]
  g := ![![![1, 0, 0], ![-2, 41, 0], ![-39, 0, 41]], ![![0, 1, 0], ![-3, 3, 3], ![-4, 7, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-5, 13, 1]] ![![41, 0, 0], ![2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![82, 41, 0]], ![![-205, 533, 41], ![-82, 41, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![2, 1, 0]]], ![![![-5, 13, 1]], ![![-2, 1, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, 1, 0]] 
 ![![43, 0, 0], ![23, 1, 0], ![31, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, 1, 0], ![0, -19, 3], ![-72, 7, -20]]]
  hmulB := by decide  
  f := ![![![761, -38, 0], ![1634, 0, 0]], ![![421, -21, 0], ![904, 0, 0]], ![![557, -15, -2], ![1196, 29, 0]]]
  g := ![![![1, 0, 0], ![-23, 43, 0], ![-31, 0, 43]], ![![-1, 1, 0], ![8, -19, 3], ![9, 7, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-12, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-12, 1, 0]] 
 ![![43, 0, 0], ![31, 1, 0], ![42, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-12, 1, 0], ![0, -11, 3], ![-72, 7, -12]]]
  hmulB := by decide  
  f := ![![![241, -20, 0], ![860, 0, 0]], ![![181, -15, 0], ![646, 0, 0]], ![![246, -13, -2], ![878, 29, 0]]]
  g := ![![![1, 0, 0], ![-31, 43, 0], ![-42, 0, 43]], ![![-1, 1, 0], ![5, -11, 3], ![5, 7, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-20, 1, 0]] ![![43, 0, 0], ![-12, 1, 0]]
  ![![43, 0, 0], ![-6, 4, 1]] where
 M := ![![![1849, 0, 0], ![-516, 43, 0]], ![![-860, 43, 0], ![240, -31, 3]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![-6, -3, -1], ![43, 0, 0]]], ![![![-14, -3, -1], ![43, 0, 0]], ![![6, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-6, 4, 1]] ![![43, 0, 0], ![-12, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-516, 43, 0]], ![![-258, 172, 43], ![0, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-12, 1, 0]]], ![![![-6, 4, 1]], ![![0, -1, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-22, -16, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-22, -16, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![25, 31, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-22, -16, 1], ![-72, -31, -48], ![1176, -136, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -31, 47]], ![![-1, -1, 1], ![24, 31, -48], ![33, 7, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [20, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[29, 24], [37, 6], [31, 16], [22, 21], [1]], ![[21, 23], [35, 41], [10, 31], [15, 26], [1]]]
 h' := ![![[31, 46], [12, 27], [38, 37], [30, 4], [27, 31], [0, 1]], ![[0, 1], [3, 20], [10, 10], [13, 43], [1, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [17, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [20, 16, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3116, -24, 119]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -79, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![1, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![1, 1, 0]] 
 ![![47, 0, 0], ![1, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![1, 1, 0], ![0, 2, 3], ![-72, 7, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![15, 16, 0]]]
  g := ![![![1, 0, 0], ![-1, 47, 0], ![-15, 0, 47]], ![![0, 1, 0], ![-1, 2, 3], ![-2, 7, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-22, -16, 1]] ![![47, 0, 0], ![1, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![47, 47, 0]], ![![-1034, -752, 47], ![-94, -47, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![1, 1, 0]]], ![![![-22, -16, 1]], ![![-2, -1, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 9, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 9, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![15, 9, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 9, 1], ![-72, 31, 27], ![-624, 39, 22]]]
  hmulB := by decide  
  f := ![![![-14, -9, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -9, 53]], ![![0, 0, 1], ![-9, -4, 27], ![-18, -3, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [18, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 52], [0, 1]]
 g := ![![[41, 37], [10], [6, 37], [4], [4, 1]], ![[30, 16], [10], [48, 16], [4], [8, 52]]]
 h' := ![![[4, 52], [36, 39], [51, 40], [24, 39], [34, 51], [0, 1]], ![[0, 1], [33, 14], [52, 13], [21, 14], [26, 2], [4, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [34, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [18, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-772, -1078, -2]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -20, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![26, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![26, 1, 0]] 
 ![![53, 0, 0], ![26, 1, 0], ![31, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![26, 1, 0], ![0, 27, 3], ![-72, 7, 26]]]
  hmulB := by decide  
  f := ![![![1275, 49, 0], ![-2597, 0, 0]], ![![598, 23, 0], ![-1218, 0, 0]], ![![733, 19, -1], ![-1493, 18, 0]]]
  g := ![![![1, 0, 0], ![-26, 53, 0], ![-31, 0, 53]], ![![0, 1, 0], ![-15, 27, 3], ![-20, 7, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![15, 9, 1]] ![![53, 0, 0], ![26, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1378, 53, 0]], ![![795, 477, 53], ![318, 265, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![26, 1, 0]]], ![![![15, 9, 1]], ![![6, 5, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![16, 28, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![16, 28, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![16, 28, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![16, 28, 1], ![-72, 51, 84], ![-1992, 172, 23]]]
  hmulB := by decide  
  f := ![![![-15, -28, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -28, 59]], ![![0, 0, 1], ![-24, -39, 84], ![-40, -8, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [3, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 58], [0, 1]]
 g := ![![[28, 20], [35, 25], [41], [27, 21], [34, 1]], ![[0, 39], [0, 34], [41], [33, 38], [9, 58]]]
 h' := ![![[34, 58], [13, 43], [7, 5], [37, 49], [16, 32], [0, 1]], ![[0, 1], [0, 16], [0, 54], [51, 10], [42, 27], [34, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [22, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [3, 25, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-837, -506, 62]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, -38, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-25, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-25, 1, 0]] 
 ![![59, 0, 0], ![34, 1, 0], ![36, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-25, 1, 0], ![0, -24, 3], ![-72, 7, -25]]]
  hmulB := by decide  
  f := ![![![1001, -40, 0], ![2360, 0, 0]], ![![576, -23, 0], ![1358, 0, 0]], ![![604, -16, -1], ![1424, 20, 0]]]
  g := ![![![1, 0, 0], ![-34, 59, 0], ![-36, 0, 59]], ![![-1, 1, 0], ![12, -24, 3], ![10, 7, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![16, 28, 1]] ![![59, 0, 0], ![-25, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1475, 59, 0]], ![![944, 1652, 59], ![-472, -649, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-25, 1, 0]]], ![![![16, 28, 1]], ![![-8, -11, 1]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 28, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 36, 24], [48, 24, 37], [0, 1]]
 g := ![![[0, 0, 22], [18, 22], [14, 5, 34], [23, 56, 47], [1]], ![[47, 21, 0, 55], [11, 19], [21, 5, 53, 18], [52, 34, 34, 11], [34, 6, 43, 38]], ![[52, 59, 32, 23], [15, 36], [21, 7, 43, 23], [5, 53, 5, 30], [46, 45, 59, 23]]]
 h' := ![![[0, 36, 24], [55, 44, 49], [13, 28, 49], [17, 31, 20], [14, 33, 48], [0, 1]], ![[48, 24, 37], [31, 24, 36], [50, 58, 18], [57, 56, 4], [49, 47, 53], [0, 36, 24]], ![[0, 1], [42, 54, 37], [25, 36, 55], [4, 35, 37], [33, 42, 21], [48, 24, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 60], []]
 b := ![[], [38, 10, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 28, 13, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76869089, -21691600, -963678]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1260149, -355600, -15798]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 1, 0]] 
 ![![67, 0, 0], ![11, 1, 0], ![23, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 1, 0], ![0, 12, 3], ![-72, 7, 11]]]
  hmulB := by decide  
  f := ![![![562, 51, 0], ![-3417, 0, 0]], ![![88, 8, 0], ![-535, 0, 0]], ![![188, 9, -2], ![-1143, 45, 0]]]
  g := ![![![1, 0, 0], ![-11, 67, 0], ![-23, 0, 67]], ![![0, 1, 0], ![-3, 12, 3], ![-6, 7, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![21, 1, 0]] 
 ![![67, 0, 0], ![21, 1, 0], ![47, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![21, 1, 0], ![0, 22, 3], ![-72, 7, 21]]]
  hmulB := by decide  
  f := ![![![127, 6, 0], ![-402, 0, 0]], ![![21, 1, 0], ![-66, 0, 0]], ![![101, -10, -2], ![-320, 45, 0]]]
  g := ![![![1, 0, 0], ![-21, 67, 0], ![-47, 0, 67]], ![![0, 1, 0], ![-9, 22, 3], ![-18, 7, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-33, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-33, 1, 0]] 
 ![![67, 0, 0], ![34, 1, 0], ![50, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-33, 1, 0], ![0, -32, 3], ![-72, 7, -33]]]
  hmulB := by decide  
  f := ![![![2212, -67, 0], ![4489, 0, 0]], ![![1156, -35, 0], ![2346, 0, 0]], ![![1634, -28, -2], ![3316, 45, 0]]]
  g := ![![![1, 0, 0], ![-34, 67, 0], ![-50, 0, 67]], ![![-1, 1, 0], ![14, -32, 3], ![20, 7, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![11, 1, 0]] ![![67, 0, 0], ![21, 1, 0]]
  ![![67, 0, 0], ![10, 11, 1]] where
 M := ![![![4489, 0, 0], ![1407, 67, 0]], ![![737, 67, 0], ![231, 33, 3]]]
 hmul := by decide  
 g := ![![![![57, -11, -1], ![67, 0, 0]], ![![11, -10, -1], ![67, 0, 0]]], ![![![1, -10, -1], ![67, 0, 0]], ![![3, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![10, 11, 1]] ![![67, 0, 0], ![-33, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2211, 67, 0]], ![![670, 737, 67], ![-402, -335, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-33, 1, 0]]], ![![![10, 11, 1]], ![![-6, -5, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [21, 45, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 14, 51], [49, 56, 20], [0, 1]]
 g := ![![[68, 58, 12], [18, 54, 54], [53, 46, 9], [36, 9], [41, 1], []], ![[3, 8, 2, 42], [18, 28, 63, 61], [67, 40, 7, 56], [], [69, 12], [7, 45]], ![[56, 47, 70, 32], [20, 32, 53, 2], [15, 20, 1, 29], [44, 9], [30, 54], [38, 45]]]
 h' := ![![[63, 14, 51], [48, 5, 56], [23, 4, 14], [35, 42, 68], [62, 51, 3], [0, 0, 1], [0, 1]], ![[49, 56, 20], [46, 36, 54], [36, 12, 65], [19, 70, 57], [44, 25], [59, 7, 56], [63, 14, 51]], ![[0, 1], [33, 30, 32], [12, 55, 63], [53, 30, 17], [57, 66, 68], [41, 64, 14], [49, 56, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 48], []]
 b := ![[], [20, 33, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [21, 45, 30, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4757, -12070, 852]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![67, -170, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-28, -20, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-28, -20, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![45, 53, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-28, -20, 1], ![-72, -41, -60], ![1464, -164, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -53, 73]], ![![-1, -1, 1], ![36, 43, -60], ![33, 13, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [60, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 72], [0, 1]]
 g := ![![[30, 72], [6], [3], [40, 16], [41], [1]], ![[5, 1], [6], [3], [2, 57], [41], [1]]]
 h' := ![![[25, 72], [24, 27], [47, 15], [9, 21], [45, 69], [13, 25], [0, 1]], ![[0, 1], [42, 46], [57, 58], [23, 52], [18, 4], [54, 48], [25, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [56, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [60, 48, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1860, -1047, 859]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-555, -638, 859]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-13, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-13, 1, 0]] 
 ![![73, 0, 0], ![60, 1, 0], ![21, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-13, 1, 0], ![0, -12, 3], ![-72, 7, -13]]]
  hmulB := by decide  
  f := ![![![716, -55, 0], ![4015, 0, 0]], ![![586, -45, 0], ![3286, 0, 0]], ![![222, -9, -2], ![1245, 49, 0]]]
  g := ![![![1, 0, 0], ![-60, 73, 0], ![-21, 0, 73]], ![![-1, 1, 0], ![9, -12, 3], ![-3, 7, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-28, -20, 1]] ![![73, 0, 0], ![-13, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-949, 73, 0]], ![![-2044, -1460, 73], ![292, 219, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-13, 1, 0]]], ![![![-28, -20, 1]], ![![4, 3, -1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [49, 78, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 36, 27], [60, 42, 52], [0, 1]]
 g := ![![[23, 69, 11], [59, 65, 5], [10, 36, 50], [14, 31, 46], [39, 1], []], ![[77, 21, 10, 29], [1, 41, 54, 58], [55, 51, 21, 74], [47, 47, 9, 56], [62, 26], [39, 18]], ![[3, 55, 59, 8], [58, 78, 6, 50], [19, 11, 27, 50], [11, 48, 63, 52], [10, 32], [14, 18]]]
 h' := ![![[58, 36, 27], [32, 53, 13], [63, 56, 20], [25, 63, 45], [64, 69, 21], [0, 0, 1], [0, 1]], ![[60, 42, 52], [33, 49, 2], [60, 25, 61], [18, 20, 36], [56, 34, 59], [31, 15, 42], [58, 36, 27]], ![[0, 1], [14, 56, 64], [4, 77, 77], [3, 75, 77], [65, 55, 78], [70, 64, 36], [60, 42, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 5], []]
 b := ![[], [38, 31, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [49, 78, 40, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3246347, 711632, 148836]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41093, 9008, 1884]
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



lemma PB101I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB101I1 : PrimesBelowBoundCertificateInterval O 31 79 101 where
  m := 11
  g := ![1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB101I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
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
    · exact ![357911]
    · exact ![5329, 73]
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
      exact NI43N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N0, I43N1, I47N1, I53N1, I59N1, I67N0, I67N1, I67N2, I73N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N1], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
