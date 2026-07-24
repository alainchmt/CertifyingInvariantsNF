
import IdealArithmetic.Examples.NF3_3_405405_1.RI3_3_405405_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![37, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![37, 48, 0]]]
  hmulB := by decide  
  f := ![![![-48, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 48, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 22, 3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![16, 22, 3]] 
 ![![37, 0, 0], ![14, 1, 0], ![26, 0, 1]] where
  M :=![![![16, 22, 3], ![111, 160, 22], ![814, 1167, 160]]]
  hmulB := by decide  
  f := ![![![74, 19, -4]], ![![24, 4, -1]], ![![71, 34, -6]]]
  g := ![![![-10, 22, 3], ![-73, 160, 22], ![-532, 1167, 160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 4, -2]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![77, 4, -2]] 
 ![![37, 0, 0], ![23, 1, 0], ![26, 0, 1]] where
  M :=![![![77, 4, -2], ![-74, -19, 4], ![148, 118, -19]]]
  hmulB := by decide  
  f := ![![![-111, -160, -22]], ![![-91, -131, -18]], ![![-238, -342, -47]]]
  g := ![![![1, 4, -2], ![7, -19, 4], ![-56, 118, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![16, 22, 3]]
  ![![111, 160, 22]] where
 M := ![![![111, 160, 22]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![111, 160, 22]] ![![77, 4, -2]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-27, -12, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-27, -12, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![14, 29, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-27, -12, 1], ![37, 21, -12], ![-444, -539, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -29, 41]], ![![-1, -1, 1], ![5, 9, -12], ![-18, -28, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [9, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 40], [0, 1]]
 g := ![![[37, 32], [36], [18], [6, 25], [1]], ![[0, 9], [36], [18], [4, 16], [1]]]
 h' := ![![[36, 40], [12, 27], [7, 6], [28, 31], [32, 36], [0, 1]], ![[0, 1], [0, 14], [18, 35], [37, 10], [16, 5], [36, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [34, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [9, 5, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![83, 128, 44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, -28, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 12, 1], ![37, 48, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![36, 3, 0], ![-122, 0, 0]], ![![76, 6, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-4, 12, 1], ![-19, 48, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-27, -12, 1]] ![![41, 0, 0], ![12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![-1107, -492, 41], ![-287, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![12, 1, 0]]], ![![![-27, -12, 1]], ![![-7, -3, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [18, 40, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 27, 21], [31, 15, 22], [0, 1]]
 g := ![![[5, 33, 31], [24, 1, 25], [8, 16], [1, 27, 1], []], ![[21, 0, 9, 13], [5, 16, 25, 1], [20, 11], [41, 25, 0, 38], [12, 11]], ![[27, 32, 37, 2], [8, 35, 24, 39], [17, 31], [26, 5, 1, 42], [11, 11]]]
 h' := ![![[39, 27, 21], [41, 32, 17], [8, 10, 5], [25, 33, 4], [0, 0, 1], [0, 1]], ![[31, 15, 22], [39, 28, 24], [0, 14, 27], [39, 24, 22], [15, 9, 15], [39, 27, 21]], ![[0, 1], [29, 26, 2], [5, 19, 11], [15, 29, 17], [32, 34, 27], [31, 15, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 5], []]
 b := ![[], [13, 17, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [18, 40, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65016, -30745, 67639]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1512, -715, 1573]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-24, 20, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-24, 20, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![23, 20, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-24, 20, 1], ![37, 24, 20], ![740, 997, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -20, 47]], ![![-1, 0, 1], ![-9, -8, 20], ![4, 11, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [45, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[31, 21], [25, 12], [40, 9], [4, 37], [1]], ![[17, 26], [17, 35], [34, 38], [42, 10], [1]]]
 h' := ![![[15, 46], [3, 31], [33, 24], [8, 44], [2, 15], [0, 1]], ![[0, 1], [45, 16], [17, 23], [10, 3], [39, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [16, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [45, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2019, -155, 145]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -65, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-20, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-20, 1, 0]] 
 ![![47, 0, 0], ![27, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-20, 1, 0], ![0, -20, 1], ![37, 48, -20]]]
  hmulB := by decide  
  f := ![![![921, -46, 0], ![2162, 0, 0]], ![![541, -27, 0], ![1270, 0, 0]], ![![449, -22, 0], ![1054, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 47, 0], ![-23, 0, 47]], ![![-1, 1, 0], ![11, -20, 1], ![-17, 48, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-24, 20, 1]] ![![47, 0, 0], ![-20, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-940, 47, 0]], ![![-1128, 940, 47], ![517, -376, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-20, 1, 0]]], ![![![-24, 20, 1]], ![![11, -8, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, -78, -11]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-54, -78, -11]] 
 ![![53, 0, 0], ![0, 53, 0], ![29, 36, 1]] where
  M :=![![![-54, -78, -11], ![-407, -582, -78], ![-2886, -4151, -582]]]
  hmulB := by decide  
  f := ![![![282, 5, -6]], ![![-222, -6, 5]], ![![7, -1, 0]]]
  g := ![![![5, 6, -11], ![35, 42, -78], ![264, 317, -582]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [38, 38, 1] where
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
 g := ![![[1, 7], [6], [10, 29], [42], [15, 1]], ![[0, 46], [6], [21, 24], [42], [30, 52]]]
 h' := ![![[15, 52], [12, 31], [44, 18], [4, 33], [13, 28], [0, 1]], ![[0, 1], [0, 22], [49, 35], [22, 20], [9, 25], [15, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [14, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [38, 38, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145, 85, 313]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-174, -211, 313]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![282, 5, -6]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![282, 5, -6]] 
 ![![53, 0, 0], ![17, 1, 0], ![29, 0, 1]] where
  M :=![![![282, 5, -6], ![-222, -6, 5], ![185, 18, -6]]]
  hmulB := by decide  
  f := ![![![-54, -78, -11]], ![![-25, -36, -5]], ![![-84, -121, -17]]]
  g := ![![![7, 5, -6], ![-5, -6, 5], ![1, 18, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-54, -78, -11]] ![![282, 5, -6]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [43, 21, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 7, 52], [18, 51, 7], [0, 1]]
 g := ![![[15, 35, 26], [17, 38, 1], [16, 17], [2, 48, 12], [1]], ![[38, 42, 44, 23], [54, 20, 48, 2], [39, 53], [41, 5, 48, 13], [24, 32, 32, 11]], ![[3, 30, 14, 19], [14, 10, 7, 53], [46, 3], [9, 47, 44, 48], [4, 47, 57, 48]]]
 h' := ![![[4, 7, 52], [36, 44, 12], [41, 8, 1], [32, 38, 31], [16, 38, 22], [0, 1]], ![[18, 51, 7], [0, 18, 9], [16, 22, 54], [10, 38, 17], [35, 49, 30], [4, 7, 52]], ![[0, 1], [31, 56, 38], [35, 29, 4], [19, 42, 11], [55, 31, 7], [18, 51, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 49], []]
 b := ![[], [1, 58, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [43, 21, 37, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3953, -5723, -767]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67, -97, -13]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [39, 20, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 5, 56], [26, 55, 5], [0, 1]]
 g := ![![[56, 49, 9], [29, 5], [43, 59, 41], [12, 38, 41], [1]], ![[56, 17, 35, 45], [14, 42], [12, 53, 22, 9], [9, 17, 12, 3], [45, 11, 17, 58]], ![[8, 36, 51, 14], [30, 60], [16, 6, 27, 14], [49, 12, 13, 57], [56, 32, 30, 3]]]
 h' := ![![[12, 5, 56], [13, 2, 3], [31, 45, 26], [20, 43, 23], [22, 41, 38], [0, 1]], ![[26, 55, 5], [28, 53, 33], [5, 8, 46], [40, 16, 13], [34, 38, 55], [12, 5, 56]], ![[0, 1], [16, 6, 25], [24, 8, 50], [10, 2, 25], [20, 43, 29], [26, 55, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 34], []]
 b := ![[], [30, 39, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [39, 20, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![393023, 553880, 67100]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6443, 9080, 1100]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [27, 55, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 0, 40], [16, 66, 27], [0, 1]]
 g := ![![[39, 61, 6], [53, 35, 47], [55, 64], [46, 23], [35, 1], []], ![[28, 34, 44, 1], [28, 19, 46, 4], [20, 33], [7, 54], [25, 1], [55, 59]], ![[31, 4, 38, 52], [0, 21, 2, 51], [7, 4], [36, 22], [], [1, 59]]]
 h' := ![![[19, 0, 40], [43, 66, 41], [24, 12, 39], [13, 57, 59], [60, 58, 31], [0, 0, 1], [0, 1]], ![[16, 66, 27], [36, 4, 53], [33, 61, 39], [38, 27, 10], [19, 21, 11], [15, 5, 66], [19, 0, 40]], ![[0, 1], [36, 64, 40], [35, 61, 56], [31, 50, 65], [47, 55, 25], [28, 62], [16, 66, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 13], []]
 b := ![[], [13, 27, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [27, 55, 32, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9179, 10184, -1608]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![137, 152, -24]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3039, 20, -60]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3039, 20, -60]] 
 ![![71, 0, 0], ![0, 71, 0], ![31, 47, 1]] where
  M :=![![![3039, 20, -60], ![-2220, 159, 20], ![740, -1260, 159]]]
  hmulB := by decide  
  f := ![![![-711, -1020, -140]], ![![-5180, -7431, -1020]], ![![-4271, -6127, -841]]]
  g := ![![![69, 40, -60], ![-40, -11, 20], ![-59, -123, 159]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [38, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 70], [0, 1]]
 g := ![![[62, 43], [2, 60], [24, 45], [4], [27], [1]], ![[0, 28], [3, 11], [7, 26], [4], [27], [1]]]
 h' := ![![[58, 70], [66, 16], [11, 42], [54, 51], [63, 69], [33, 58], [0, 1]], ![[0, 1], [0, 55], [33, 29], [30, 20], [18, 2], [60, 13], [58, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [41, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [38, 13, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![186, 353, 219]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-93, -140, 219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-711, -1020, -140]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-711, -1020, -140]] 
 ![![71, 0, 0], ![24, 1, 0], ![63, 0, 1]] where
  M :=![![![-711, -1020, -140], ![-5180, -7431, -1020], ![-37740, -54140, -7431]]]
  hmulB := by decide  
  f := ![![![3039, 20, -60]], ![![996, 9, -20]], ![![2707, 0, -51]]]
  g := ![![![459, -1020, -140], ![3344, -7431, -1020], ![24363, -54140, -7431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3039, 20, -60]] ![![-711, -1020, -140]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [17, 43, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 13, 6], [21, 59, 67], [0, 1]]
 g := ![![[54, 69, 55], [57, 36], [1, 12], [41, 56, 67], [52, 1], []], ![[70, 66, 69, 38], [69, 36], [31, 71], [34, 71, 66, 38], [23, 50], [57, 36]], ![[70, 69, 12, 67], [], [64, 24], [42, 51, 58, 50], [18, 23], [69, 36]]]
 h' := ![![[31, 13, 6], [71, 17, 36], [50, 60, 67], [33, 50, 31], [65, 10, 33], [0, 0, 1], [0, 1]], ![[21, 59, 67], [18, 72, 36], [60, 14, 6], [21, 33, 12], [38, 36, 36], [65, 6, 59], [31, 13, 6]], ![[0, 1], [64, 57, 1], [8, 72], [72, 63, 30], [63, 27, 4], [71, 67, 13], [21, 59, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 40], []]
 b := ![[], [9, 65, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [17, 43, 21, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-278933, -323098, 50954]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3821, -4426, 698]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-2, 21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-2, 21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![77, 21, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-2, 21, 1], ![37, 46, 21], ![777, 1045, 46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -21, 79]], ![![-1, 0, 1], ![-20, -5, 21], ![-35, 1, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [25, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 78], [0, 1]]
 g := ![![[53, 19], [21, 23], [42, 40], [17, 50], [8], [1]], ![[0, 60], [40, 56], [51, 39], [48, 29], [8], [1]]]
 h' := ![![[18, 78], [28, 16], [56, 24], [49, 35], [30, 34], [54, 18], [0, 1]], ![[0, 1], [0, 63], [14, 55], [47, 44], [10, 45], [62, 61], [18, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [29, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [25, 61, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![913, -146, 136]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -38, 136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-21, 1, 0]] 
 ![![79, 0, 0], ![58, 1, 0], ![33, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-21, 1, 0], ![0, -21, 1], ![37, 48, -21]]]
  hmulB := by decide  
  f := ![![![1513, -72, 0], ![5688, 0, 0]], ![![1114, -53, 0], ![4188, 0, 0]], ![![615, -29, 0], ![2312, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 79, 0], ![-33, 0, 79]], ![![-1, 1, 0], ![15, -21, 1], ![-26, 48, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-2, 21, 1]] ![![79, 0, 0], ![-21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1659, 79, 0]], ![![-158, 1659, 79], ![79, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-21, 1, 0]]], ![![![-2, 21, 1]], ![![1, -5, 0]]]]
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


lemma PB142I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB142I1 : PrimesBelowBoundCertificateInterval O 31 79 142 where
  m := 11
  g := ![3, 2, 1, 2, 2, 1, 1, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB142I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I53N1, I71N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [I53N1], [], [], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
