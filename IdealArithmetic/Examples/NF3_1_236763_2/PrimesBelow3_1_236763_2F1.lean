
import IdealArithmetic.Examples.NF3_1_236763_2.RI3_1_236763_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![16, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![16, 1, 0]] 
 ![![37, 0, 0], ![16, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![16, 1, 0], ![2, 19, 8], ![47, -19, 13]]]
  hmulB := by decide  
  f := ![![![147, 1991, 840], ![148, -3885, 0]], ![![58, 853, 360], ![75, -1665, 0]], ![![109, 1453, 613], ![104, -2835, 0]]]
  g := ![![![1, 0, 0], ![-16, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-14, 19, 8], ![0, -19, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![23, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![2, -5, 8], ![47, -19, -11]]]
  hmulB := by decide  
  f := ![![![1263, -3326, 5336], ![-333, -24679, 0]], ![![989, -2603, 4176], ![-258, -19314, 0]], ![![789, -2068, 3317], ![-189, -15341, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-23, 0, 37]], ![![-1, 1, 0], ![-1, -5, 8], ![23, -19, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![16, 1, 0]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0], ![12, 6, 1]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![592, 37, 0], ![-126, 11, 8]]]
 hmul := by decide  
 g := ![![![![25, -6, -1], ![37, 0, 0]], ![![-8, 1, 0], ![0, 0, 0]]], ![![![4, -5, -1], ![37, 0, 0]], ![![-6, -1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 6, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![444, 222, 37], ![-37, -37, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![12, 6, 1]], ![![-1, -1, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![25, 6, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![25, 6, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![25, 6, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![25, 6, 1], ![59, 24, 45], ![242, -101, -10]]]
  hmulB := by decide  
  f := ![![![-24, -6, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -6, 41]], ![![0, 0, 1], ![-26, -6, 45], ![12, -1, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[35, 8], [5], [39], [18, 4], [1]], ![[19, 33], [5], [39], [10, 37], [1]]]
 h' := ![![[39, 40], [11, 34], [8, 13], [6, 11], [14, 39], [0, 1]], ![[0, 1], [25, 7], [23, 28], [25, 30], [18, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [15, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40, -313, -2560]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1560, 367, -2560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, 1, 0]] 
 ![![41, 0, 0], ![37, 1, 0], ![10, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, 1, 0], ![2, -1, 8], ![47, -19, -7]]]
  hmulB := by decide  
  f := ![![![-35, 19, -160], ![41, 820, 0]], ![![-31, 17, -144], ![42, 738, 0]], ![![-6, 4, -39], ![36, 200, 0]]]
  g := ![![![1, 0, 0], ![-37, 41, 0], ![-10, 0, 41]], ![![-1, 1, 0], ![-1, -1, 8], ![20, -19, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![25, 6, 1]] ![![41, 0, 0], ![-4, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-164, 41, 0]], ![![1025, 246, 41], ![-41, 0, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-4, 1, 0]]], ![![![25, 6, 1]], ![![-1, 0, 1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [28, 12, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 27, 16], [2, 15, 27], [0, 1]]
 g := ![![[36, 40, 23], [39, 37, 17], [12, 23], [19, 26, 1], []], ![[8, 2, 31, 4], [3, 27, 28, 9], [], [5, 36, 38, 31], [38, 41]], ![[11, 11, 36, 28], [42, 18, 4, 37], [36, 23], [7, 24, 0, 32], [27, 41]]]
 h' := ![![[24, 27, 16], [26, 37, 25], [6, 5, 24], [27, 33, 25], [0, 0, 1], [0, 1]], ![[2, 15, 27], [23, 7, 21], [24, 10, 10], [14, 28], [28, 36, 15], [24, 27, 16]], ![[0, 1], [5, 42, 40], [28, 28, 9], [41, 25, 18], [22, 7, 27], [2, 15, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 4], []]
 b := ![[], [20, 5, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [28, 12, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![513893, -171785, 180385]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11951, -3995, 4195]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-10, 21, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-10, 21, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![37, 21, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-10, 21, 1], ![89, 34, 165], ![947, -386, -90]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -21, 47]], ![![-1, 0, 1], ![-128, -73, 165], ![91, 32, -90]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [7, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 46], [0, 1]]
 g := ![![[42, 27], [39, 17], [10, 25], [38, 3], [1]], ![[0, 20], [23, 30], [39, 22], [2, 44], [1]]]
 h' := ![![[35, 46], [9, 36], [24, 8], [16, 42], [40, 35], [0, 1]], ![[0, 1], [0, 11], [22, 39], [29, 5], [43, 12], [35, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [8, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [7, 12, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117622, -499791, -3587400]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2826626, 1592247, -3587400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![23, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![23, 1, 0]] 
 ![![47, 0, 0], ![23, 1, 0], ![43, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![23, 1, 0], ![2, 26, 8], ![47, -19, 20]]]
  hmulB := by decide  
  f := ![![![669, 12856, 3960], ![658, -23265, 0]], ![![323, 6285, 1936], ![330, -11374, 0]], ![![615, 11762, 3623], ![596, -21285, 0]]]
  g := ![![![1, 0, 0], ![-23, 47, 0], ![-43, 0, 47]], ![![0, 1, 0], ![-20, 26, 8], ![-8, -19, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-10, 21, 1]] ![![47, 0, 0], ![23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![1081, 47, 0]], ![![-470, 987, 47], ![-141, 517, 188]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![23, 1, 0]]], ![![![-10, 21, 1]], ![![-3, 11, 4]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![3, 17, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![3, 17, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![3, 17, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![3, 17, 1], ![81, 35, 133], ![759, -310, -65]]]
  hmulB := by decide  
  f := ![![![-2, -17, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -17, 53]], ![![0, 0, 1], ![-6, -42, 133], ![18, 15, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [7, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 52], [0, 1]]
 g := ![![[9, 38], [44], [35, 38], [10], [43, 1]], ![[0, 15], [44], [26, 15], [10], [33, 52]]]
 h' := ![![[43, 52], [39, 41], [20, 16], [7, 41], [17, 40], [0, 1]], ![[0, 1], [0, 12], [19, 37], [21, 12], [41, 13], [43, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [19, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [7, 10, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1854, 253, -3109]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![141, 1002, -3109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![26, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![26, 1, 0]] 
 ![![53, 0, 0], ![26, 1, 0], ![12, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![26, 1, 0], ![2, 29, 8], ![47, -19, 23]]]
  hmulB := by decide  
  f := ![![![3187, 66501, 18360], ![2862, -121635, 0]], ![![1548, 32598, 9000], ![1432, -59625, 0]], ![![700, 15056, 4157], ![692, -27540, 0]]]
  g := ![![![1, 0, 0], ![-26, 53, 0], ![-12, 0, 53]], ![![0, 1, 0], ![-16, 29, 8], ![5, -19, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![3, 17, 1]] ![![53, 0, 0], ![26, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1378, 53, 0]], ![![159, 901, 53], ![159, 477, 159]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![26, 1, 0]]], ![![![3, 17, 1]], ![![3, 9, 3]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [11, 12, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 16, 47], [51, 42, 12], [0, 1]]
 g := ![![[52, 51, 36], [19, 12, 3], [57, 49], [11, 52, 41], [1]], ![[26, 53, 35, 56], [15, 4, 26, 43], [30, 27], [23, 29, 51, 30], [30, 45, 16, 42]], ![[6, 28, 58, 35], [0, 53, 25, 4], [28, 7], [34, 44, 57, 4], [22, 22, 24, 17]]]
 h' := ![![[18, 16, 47], [27, 11, 53], [31, 33, 48], [56, 7, 7], [48, 47, 10], [0, 1]], ![[51, 42, 12], [9, 10, 29], [52, 27, 27], [21, 50, 33], [15, 6, 33], [18, 16, 47]], ![[0, 1], [53, 38, 36], [35, 58, 43], [44, 2, 19], [13, 6, 16], [51, 42, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 40], []]
 b := ![[], [40, 15, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [11, 12, 49, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-450229, 76464, -670240]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7631, 1296, -11360]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [37, 34, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 36, 3], [2, 24, 58], [0, 1]]
 g := ![![[1, 29, 57], [23, 45], [22, 19, 3], [28, 9, 5], [1]], ![[60, 37, 51, 14], [], [30, 8, 46, 13], [39, 19, 53, 52], [3, 18, 27, 27]], ![[36, 16, 51, 48], [54, 45], [20, 12, 5, 16], [45, 60, 3, 58], [14, 57, 7, 34]]]
 h' := ![![[24, 36, 3], [17, 15, 39], [40, 14, 44], [1, 23, 8], [24, 27, 26], [0, 1]], ![[2, 24, 58], [22, 47, 5], [49, 26], [0, 59, 17], [49, 13, 34], [24, 36, 3]], ![[0, 1], [19, 60, 17], [2, 21, 17], [35, 40, 36], [39, 21, 1], [2, 24, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 56], []]
 b := ![[], [37, 2, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [37, 34, 35, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70962154, 8252568, 236865135]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1163314, 135288, 3883035]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [24, 55, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 48, 24], [27, 18, 43], [0, 1]]
 g := ![![[47, 7, 65], [47, 4, 37], [33, 64], [43, 56], [38, 1], []], ![[56, 26, 9, 21], [23, 48, 24, 64], [27, 16], [29, 36], [39, 56], [5, 40]], ![[44, 47, 53, 43], [63, 22, 36, 45], [23, 16], [17, 40], [15, 26], [53, 40]]]
 h' := ![![[11, 48, 24], [11, 54, 20], [51, 8, 38], [46, 62, 59], [26, 30, 49], [0, 0, 1], [0, 1]], ![[27, 18, 43], [22, 17, 48], [43, 14, 5], [50, 53, 4], [3, 39, 61], [1, 22, 18], [11, 48, 24]], ![[0, 1], [56, 63, 66], [1, 45, 24], [34, 19, 4], [24, 65, 24], [60, 45, 48], [27, 18, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 55], []]
 b := ![[], [32, 41, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [24, 55, 29, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44220, 15678, -9648]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-660, 234, -144]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![29, -13, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![29, -13, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![29, 58, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![29, -13, 1], ![21, -29, -107], ![-651, 260, 51]]]
  hmulB := by decide  
  f := ![![![-28, 13, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -58, 71]], ![![0, -1, 1], ![44, 87, -107], ![-30, -38, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [55, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 70], [0, 1]]
 g := ![![[43, 45], [39, 3], [67, 1], [64], [58], [1]], ![[47, 26], [44, 68], [45, 70], [64], [58], [1]]]
 h' := ![![[49, 70], [56, 20], [7, 43], [62, 70], [48, 8], [16, 49], [0, 1]], ![[0, 1], [42, 51], [55, 28], [13, 1], [14, 63], [3, 22], [49, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [65, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [55, 22, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-642, -432, -6608]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2690, 5392, -6608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-35, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-35, 1, 0]] 
 ![![71, 0, 0], ![36, 1, 0], ![20, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-35, 1, 0], ![2, -32, 8], ![47, -19, -38]]]
  hmulB := by decide  
  f := ![![![28, 127, -32], ![71, 284, 0]], ![![32, 63, -16], ![72, 142, 0]], ![![0, 36, -9], ![4, 80, 0]]]
  g := ![![![1, 0, 0], ![-36, 71, 0], ![-20, 0, 71]], ![![-1, 1, 0], ![14, -32, 8], ![21, -19, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![29, -13, 1]] ![![71, 0, 0], ![-35, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2485, 71, 0]], ![![2059, -923, 71], ![-994, 426, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-35, 1, 0]]], ![![![29, -13, 1]], ![![-14, 6, -2]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [63, 46, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 20, 61], [71, 52, 12], [0, 1]]
 g := ![![[21, 64, 55], [26, 50], [23, 36], [30, 49, 4], [62, 1], []], ![[57, 55, 47, 9], [59, 8], [65, 61], [36, 34, 39, 55], [63, 3], [53, 71]], ![[53, 32, 68, 38], [2, 25], [65, 54], [57, 27, 14, 61], [61, 35], [29, 71]]]
 h' := ![![[64, 20, 61], [45, 12, 37], [2, 31, 14], [8, 41, 6], [36, 5, 2], [0, 0, 1], [0, 1]], ![[71, 52, 12], [60, 72, 28], [28, 4, 64], [20, 45, 39], [45, 12, 44], [27, 29, 52], [64, 20, 61]], ![[0, 1], [22, 62, 8], [41, 38, 68], [11, 60, 28], [30, 56, 27], [2, 44, 20], [71, 52, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 51], []]
 b := ![[], [33, 44, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [63, 46, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9815872, 1742510, -13752835]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-134464, 23870, -188395]
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


def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56, -2, -3]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-56, -2, -3]] 
 ![![79, 0, 0], ![43, 1, 0], ![69, 0, 1]] where
  M :=![![![-56, -2, -3], ![-145, -5, -7], ![26, -1, 1]]]
  hmulB := by decide  
  f := ![![![12, -5, 1]], ![![7, -3, 0]], ![![7, -3, 1]]]
  g := ![![![3, -2, -3], ![7, -5, -7], ![0, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -2, -3]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![4, -2, -3]] 
 ![![79, 0, 0], ![72, 1, 0], ![56, 0, 1]] where
  M :=![![![4, -2, -3], ![-145, 55, -7], ![26, -1, 61]]]
  hmulB := by decide  
  f := ![![![-3348, -125, -179]], ![![-3161, -118, -169]], ![![-2357, -88, -126]]]
  g := ![![![4, -2, -3], ![-47, 55, -7], ![-42, -1, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-56, -2, -3]] ![![-56, -2, -3]]
  ![![3348, 125, 179]] where
 M := ![![![3348, 125, 179]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI79N1 : IdealMulLeCertificate' Table 
  ![![3348, 125, 179]] ![![4, -2, -3]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB138I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB138I1 : PrimesBelowBoundCertificateInterval O 31 79 138 where
  m := 11
  g := ![3, 2, 1, 2, 2, 1, 1, 1, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB138I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N0, I79N1]
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
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
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
      exact NI37N1
      exact NI37N1
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
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I41N1, I47N1, I53N1, I71N1, I79N0, I79N1]
  Il := ![[I37N0, I37N1, I37N1], [I41N1], [], [I47N1], [I53N1], [], [], [], [I71N1], [], [I79N0, I79N0, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
