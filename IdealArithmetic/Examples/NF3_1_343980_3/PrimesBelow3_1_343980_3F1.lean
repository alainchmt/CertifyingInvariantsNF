
import IdealArithmetic.Examples.NF3_1_343980_3.RI3_1_343980_3
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [12, 2, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36, 13], [18, 0, 24], [0, 1]]
 g := ![![[27, 20, 4], [36, 7], [9, 26, 21], [27, 1], []], ![[14, 26, 17, 5], [11, 28], [35, 26, 35, 8], [], [23, 21]], ![[23, 6, 9, 15], [25, 7], [31, 35, 17, 17], [24, 1], [12, 21]]]
 h' := ![![[9, 36, 13], [21, 15, 2], [3, 10, 9], [9, 8, 24], [0, 0, 1], [0, 1]], ![[18, 0, 24], [25, 19, 10], [3, 32, 19], [26, 30, 30], [27, 17], [9, 36, 13]], ![[0, 1], [22, 3, 25], [27, 32, 9], [33, 36, 20], [32, 20, 36], [18, 0, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 18], []]
 b := ![[], [2, 35, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [12, 2, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40182, -16354, -1924]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1086, -442, -52]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [8, 21, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 1, 31], [31, 39, 10], [0, 1]]
 g := ![![[24, 20, 37], [1, 18], [28, 10], [29, 3, 1], []], ![[8, 12, 5, 32], [37, 32], [26, 10], [2, 29, 19, 1], [34, 18]], ![[16, 29, 1, 4], [9, 16], [], [35, 14, 22, 10], [14, 18]]]
 h' := ![![[13, 1, 31], [38, 31, 23], [13, 17, 31], [14, 23, 16], [0, 0, 1], [0, 1]], ![[31, 39, 10], [40, 1, 13], [34, 14, 14], [18, 36, 25], [20, 29, 39], [13, 1, 31]], ![[0, 1], [26, 9, 5], [4, 10, 37], [2, 23], [29, 12, 1], [31, 39, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 19], []]
 b := ![[], [19, 23, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [8, 21, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![225172, 290198, 54038]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5492, 7078, 1318]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-26, 4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-26, 4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![17, 4, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-26, 4, 1], ![154, 16, 4], ![616, 322, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -4, 43]], ![![-1, 0, 1], ![2, 0, 4], ![8, 6, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [5, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 42], [0, 1]]
 g := ![![[40, 17], [0, 1], [23], [0, 10], [1]], ![[37, 26], [15, 42], [23], [21, 33], [1]]]
 h' := ![![[15, 42], [0, 19], [14, 1], [0, 18], [38, 15], [0, 1]], ![[0, 1], [27, 24], [29, 42], [12, 25], [5, 28], [15, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [20, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [5, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2001, -30, 143]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -14, 143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-4, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-4, 1, 0]] 
 ![![43, 0, 0], ![39, 1, 0], ![27, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-4, 1, 0], ![0, -4, 1], ![154, 42, -4]]]
  hmulB := by decide  
  f := ![![![53, -13, 0], ![559, 0, 0]], ![![49, -12, 0], ![517, 0, 0]], ![![37, -9, 0], ![391, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 43, 0], ![-27, 0, 43]], ![![-1, 1, 0], ![3, -4, 1], ![-32, 42, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-26, 4, 1]] ![![43, 0, 0], ![-4, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-172, 43, 0]], ![![-1118, 172, 43], ![258, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-4, 1, 0]]], ![![![-26, 4, 1]], ![![6, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-24, -26, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-24, -26, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![23, 21, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-24, -26, 1], ![154, 18, -26], ![-4004, -938, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -21, 47]], ![![-1, -1, 1], ![16, 12, -26], ![-94, -28, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [46, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 46], [0, 1]]
 g := ![![[18, 42], [44, 27], [3, 27], [40, 42], [1]], ![[22, 5], [13, 20], [19, 20], [44, 5], [1]]]
 h' := ![![[18, 46], [44, 29], [3, 36], [40, 11], [1, 18], [0, 1]], ![[0, 1], [2, 18], [40, 11], [3, 36], [43, 29], [18, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [29, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [46, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-848, 1165, 286]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-158, -103, 286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-21, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-21, 1, 0]] 
 ![![47, 0, 0], ![26, 1, 0], ![29, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-21, 1, 0], ![0, -21, 1], ![154, 42, -21]]]
  hmulB := by decide  
  f := ![![![316, -15, 0], ![705, 0, 0]], ![![190, -9, 0], ![424, 0, 0]], ![![220, -10, 0], ![491, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 47, 0], ![-29, 0, 47]], ![![-1, 1, 0], ![11, -21, 1], ![-7, 42, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-24, -26, 1]] ![![47, 0, 0], ![-21, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-987, 47, 0]], ![![-1128, -1222, 47], ![658, 564, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-21, 1, 0]]], ![![![-24, -26, 1]], ![![14, 12, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![12, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![12, 1, 0]] 
 ![![53, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![12, 1, 0], ![0, 12, 1], ![154, 42, 12]]]
  hmulB := by decide  
  f := ![![![277, 23, 0], ![-1219, 0, 0]], ![![60, 5, 0], ![-264, 0, 0]], ![![63, 5, 0], ![-277, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 53, 0], ![-15, 0, 53]], ![![0, 1, 0], ![-3, 12, 1], ![-10, 42, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, 1, 0]] 
 ![![53, 0, 0], ![20, 1, 0], ![24, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, 1, 0], ![0, 20, 1], ![154, 42, 20]]]
  hmulB := by decide  
  f := ![![![121, 6, 0], ![-318, 0, 0]], ![![20, 1, 0], ![-52, 0, 0]], ![![48, 2, 0], ![-126, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 53, 0], ![-24, 0, 53]], ![![0, 1, 0], ![-8, 20, 1], ![-22, 42, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![36, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![0, 21, 1], ![154, 42, 21]]]
  hmulB := by decide  
  f := ![![![379, 18, 0], ![-954, 0, 0]], ![![147, 7, 0], ![-370, 0, 0]], ![![240, 11, 0], ![-604, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-36, 0, 53]], ![![0, 1, 0], ![-9, 21, 1], ![-28, 42, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![12, 1, 0]] ![![53, 0, 0], ![20, 1, 0]]
  ![![53, 0, 0], ![-25, -21, 1]] where
 M := ![![![2809, 0, 0], ![1060, 53, 0]], ![![636, 53, 0], ![240, 32, 1]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![20, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-25, -21, 1]] ![![53, 0, 0], ![21, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1113, 53, 0]], ![![-1325, -1113, 53], ![-371, -424, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![21, 1, 0]]], ![![![-25, -21, 1]], ![![-7, -8, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![6, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![6, 1, 0]] 
 ![![59, 0, 0], ![6, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![6, 1, 0], ![0, 6, 1], ![154, 42, 6]]]
  hmulB := by decide  
  f := ![![![49, 8, 0], ![-472, 0, 0]], ![![-6, -1, 0], ![60, 0, 0]], ![![13, 2, 0], ![-124, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 59, 0], ![-23, 0, 59]], ![![0, 1, 0], ![-1, 6, 1], ![-4, 42, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![26, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![26, 1, 0]] 
 ![![59, 0, 0], ![26, 1, 0], ![32, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![26, 1, 0], ![0, 26, 1], ![154, 42, 26]]]
  hmulB := by decide  
  f := ![![![443, 17, 0], ![-1003, 0, 0]], ![![182, 7, 0], ![-412, 0, 0]], ![![220, 8, 0], ![-498, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 59, 0], ![-32, 0, 59]], ![![0, 1, 0], ![-12, 26, 1], ![-30, 42, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, 1, 0]] 
 ![![59, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, 1, 0], ![0, 27, 1], ![154, 42, 27]]]
  hmulB := by decide  
  f := ![![![514, 19, 0], ![-1121, 0, 0]], ![![216, 8, 0], ![-471, 0, 0]], ![![310, 11, 0], ![-676, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 59, 0], ![-38, 0, 59]], ![![0, 1, 0], ![-13, 27, 1], ![-34, 42, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![6, 1, 0]] ![![59, 0, 0], ![26, 1, 0]]
  ![![59, 0, 0], ![-21, -27, 1]] where
 M := ![![![3481, 0, 0], ![1534, 59, 0]], ![![354, 59, 0], ![156, 32, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![26, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-21, -27, 1]] ![![59, 0, 0], ![27, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1593, 59, 0]], ![![-1239, -1593, 59], ![-413, -708, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![27, 1, 0]]], ![![![-21, -27, 1]], ![![-7, -12, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [17, 40, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 57, 47], [55, 3, 14], [0, 1]]
 g := ![![[1, 54, 14], [11, 60], [12, 24, 22], [58, 43, 41], [1]], ![[60, 15, 31, 9], [16, 27], [16, 57, 4, 9], [37, 37, 0, 57], [33, 58, 4, 1]], ![[16, 60, 43, 13], [38, 5], [53, 21, 50, 15], [33, 4, 38, 49], [52, 14, 18, 60]]]
 h' := ![![[44, 57, 47], [10, 38, 21], [40, 5, 11], [51, 44, 49], [44, 21, 38], [0, 1]], ![[55, 3, 14], [29, 20, 19], [39, 12, 24], [21, 22, 19], [16, 21, 3], [44, 57, 47]], ![[0, 1], [6, 3, 21], [46, 44, 26], [25, 56, 54], [59, 19, 20], [55, 3, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 18], []]
 b := ![[], [57, 27, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [17, 40, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36173, -13298, -1403]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-593, -218, -23]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [33, 38, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 26, 8], [1, 40, 59], [0, 1]]
 g := ![![[38, 31, 24], [18, 56, 60], [16, 9], [32, 59], [20, 1], []], ![[35, 9, 57, 51], [31, 18, 21, 7], [30, 35], [31, 37], [46, 59], [21, 64]], ![[14, 35, 56, 1], [39, 4, 47, 25], [2, 55], [28, 54], [33, 6], [37, 64]]]
 h' := ![![[19, 26, 8], [9, 23, 15], [64, 54, 44], [49, 5, 64], [10, 11, 27], [0, 0, 1], [0, 1]], ![[1, 40, 59], [22, 42, 47], [16, 50, 48], [1, 0, 54], [32, 49, 29], [3, 21, 40], [19, 26, 8]], ![[0, 1], [23, 2, 5], [38, 30, 42], [29, 62, 16], [45, 7, 11], [53, 46, 26], [1, 40, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 23], []]
 b := ![[], [27, 17, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [33, 38, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1741397, 658409, 76313]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25991, 9827, 1139]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-35, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-35, 1, 0]] 
 ![![71, 0, 0], ![36, 1, 0], ![53, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-35, 1, 0], ![0, -35, 1], ![154, 42, -35]]]
  hmulB := by decide  
  f := ![![![2486, -71, 0], ![5041, 0, 0]], ![![1296, -37, 0], ![2628, 0, 0]], ![![1908, -54, 0], ![3869, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 71, 0], ![-53, 0, 71]], ![![-1, 1, 0], ![17, -35, 1], ![7, 42, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-26, 1, 0]] 
 ![![71, 0, 0], ![45, 1, 0], ![34, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-26, 1, 0], ![0, -26, 1], ![154, 42, -26]]]
  hmulB := by decide  
  f := ![![![1379, -53, 0], ![3763, 0, 0]], ![![885, -34, 0], ![2415, 0, 0]], ![![686, -26, 0], ![1872, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 71, 0], ![-34, 0, 71]], ![![-1, 1, 0], ![16, -26, 1], ![-12, 42, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-10, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-10, 1, 0]] 
 ![![71, 0, 0], ![61, 1, 0], ![42, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-10, 1, 0], ![0, -10, 1], ![154, 42, -10]]]
  hmulB := by decide  
  f := ![![![661, -66, 0], ![4686, 0, 0]], ![![571, -57, 0], ![4048, 0, 0]], ![![402, -40, 0], ![2850, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 71, 0], ![-42, 0, 71]], ![![-1, 1, 0], ![8, -10, 1], ![-28, 42, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-35, 1, 0]] ![![71, 0, 0], ![-26, 1, 0]]
  ![![71, 0, 0], ![-13, 10, 1]] where
 M := ![![![5041, 0, 0], ![-1846, 71, 0]], ![![-2485, 71, 0], ![910, -61, 1]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![-13, -9, -1], ![71, 0, 0]]], ![![![-22, -9, -1], ![71, 0, 0]], ![![13, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-13, 10, 1]] ![![71, 0, 0], ![-10, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-710, 71, 0]], ![![-923, 710, 71], ![284, -71, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-10, 1, 0]]], ![![![-13, 10, 1]], ![![4, -1, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [63, 23, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 47, 4], [20, 25, 69], [0, 1]]
 g := ![![[55, 24, 49], [37, 41], [47, 8], [54, 57, 72], [59, 1], []], ![[29, 48, 4, 37], [5, 65], [41, 70], [17, 59, 48, 8], [12, 41], [6, 16]], ![[69, 29, 44, 69], [34, 1], [0, 19], [4, 19, 27, 19], [31, 19], [14, 16]]]
 h' := ![![[39, 47, 4], [14, 9, 7], [70, 71, 48], [29, 21, 9], [6, 40, 27], [0, 0, 1], [0, 1]], ![[20, 25, 69], [44, 32, 65], [33, 51, 24], [39, 15, 17], [15, 59, 32], [48, 38, 25], [39, 47, 4]], ![[0, 1], [32, 32, 1], [35, 24, 1], [53, 37, 47], [56, 47, 14], [29, 35, 47], [20, 25, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 14], []]
 b := ![[], [45, 35, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [63, 23, 14, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28543, -1168, -949]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![391, -16, -13]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [73, 7, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 55], [32, 23], [0, 1]]
 g := ![![[49, 71, 42], [18, 27, 16], [41, 66, 49], [1, 10, 38], [10, 1], []], ![[13, 67, 18], [58, 53, 52], [27, 74, 21], [3, 72, 5], [67, 55], []], ![[62, 20, 19], [44, 78, 11], [31, 18, 9], [49, 76, 36], [42, 23], []]]
 h' := ![![[57, 55], [29, 38, 11], [9, 66, 75], [6, 19, 72], [60, 15, 14], [0, 0, 1], [0, 1]], ![[32, 23], [14, 39, 16], [18, 38, 66], [71, 52, 76], [28, 46, 6], [10, 29, 23], [57, 55]], ![[0, 1], [27, 2, 52], [0, 54, 17], [3, 8, 10], [24, 18, 59], [76, 50, 55], [32, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45], []]
 b := ![[], [20, 67, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [73, 7, 69, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![310075, 179725, 27887]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3925, 2275, 353]
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



lemma PB166I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB166I1 : PrimesBelowBoundCertificateInterval O 31 79 166 where
  m := 11
  g := ![1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB166I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
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
  β := ![I43N1, I47N1, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I71N0, I71N1, I71N2]
  Il := ![[], [], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [], [], [I71N0, I71N1, I71N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
