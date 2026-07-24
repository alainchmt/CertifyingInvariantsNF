
import IdealArithmetic.Examples.NF3_1_117720_1.RI3_1_117720_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, 5, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, 5, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 5, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, 5, 1], ![38, -12, 5], ![190, -97, -12]]]
  hmulB := by decide  
  f := ![![![-14, -5, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -5, 37]], ![![0, 0, 1], ![-1, -1, 5], ![10, -1, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [17, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 36], [0, 1]]
 g := ![![[19, 1], [21], [13, 36], [26], [1]], ![[29, 36], [21], [3, 1], [26], [1]]]
 h' := ![![[10, 36], [14, 36], [1, 24], [32, 31], [20, 10], [0, 1]], ![[0, 1], [4, 1], [19, 13], [9, 6], [9, 27], [10, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [35, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [17, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93, -43, -53]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 6, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![12, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![0, -5, 1], ![38, -27, -5]]]
  hmulB := by decide  
  f := ![![![96, -19, 0], ![703, 0, 0]], ![![76, -15, 0], ![556, 0, 0]], ![![36, -7, 0], ![264, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-12, 0, 37]], ![![-1, 1, 0], ![4, -5, 1], ![26, -27, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, 5, 1]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![555, 185, 37], ![-37, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-5, 1, 0]]], ![![![15, 5, 1]], ![![-1, -1, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [10, 13, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 40, 38], [11, 0, 3], [0, 1]]
 g := ![![[34, 26, 31], [40, 2], [40, 20], [29, 40, 1], []], ![[15, 24, 7, 17], [14, 37], [10, 36], [3, 27], [38, 9]], ![[35, 37, 0, 14], [19, 36], [9, 40], [0, 33, 40, 3], [32, 9]]]
 h' := ![![[29, 40, 38], [2, 16, 21], [19, 6, 24], [38, 2, 15], [0, 0, 1], [0, 1]], ![[11, 0, 3], [20, 32, 34], [23, 2, 23], [0, 3, 35], [10, 14], [29, 40, 38]], ![[0, 1], [17, 34, 27], [24, 33, 35], [27, 36, 32], [6, 27, 40], [11, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 9], []]
 b := ![[], [12, 40, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [10, 13, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![94997, -94546, 17179]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2317, -2306, 419]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [12, 11, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 20, 29], [17, 22, 14], [0, 1]]
 g := ![![[38, 31, 4], [21, 21, 38], [33, 41], [27, 34, 1], []], ![[40, 15, 28, 3], [35, 12, 28, 28], [22, 15], [42, 1, 24, 18], [41, 24]], ![[28, 9, 25, 6], [21, 23, 16, 21], [26, 16], [29, 4, 40, 10], [13, 24]]]
 h' := ![![[17, 20, 29], [6, 6, 2], [4, 13, 9], [20, 26, 16], [0, 0, 1], [0, 1]], ![[17, 22, 14], [3, 2, 3], [32, 30, 16], [9, 6, 31], [12, 27, 22], [17, 20, 29]], ![[0, 1], [30, 35, 38], [3, 0, 18], [10, 11, 39], [4, 16, 20], [17, 22, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 27], []]
 b := ![[], [1, 22, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [12, 11, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-216548, -1591, -6923]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5036, -37, -161]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117, 6, 4]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![117, 6, 4]] 
 ![![47, 0, 0], ![0, 47, 0], ![41, 25, 1]] where
  M :=![![![117, 6, 4], ![152, 9, 6], ![228, -10, 9]]]
  hmulB := by decide  
  f := ![![![3, -2, 0]], ![![0, 3, -2]], ![![1, 1, -1]]]
  g := ![![![-1, -2, 4], ![-2, -3, 6], ![-3, -5, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [1, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 46], [0, 1]]
 g := ![![[7, 1], [7, 1], [40, 1], [0, 2], [1]], ![[0, 46], [0, 46], [33, 46], [33, 45], [1]]]
 h' := ![![[40, 46], [40, 46], [7, 1], [0, 46], [46, 40], [0, 1]], ![[0, 1], [0, 1], [0, 46], [7, 1], [1, 7], [40, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [27, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [1, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-219, 513, -269]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![230, 154, -269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![3, -2, 0]] 
 ![![47, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![3, -2, 0], ![0, 3, -2], ![-76, 54, 3]]]
  hmulB := by decide  
  f := ![![![117, 6, 4]], ![![58, 3, 2]], ![![87, 4, 3]]]
  g := ![![![1, -2, 0], ![0, 3, -2], ![-29, 54, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![117, 6, 4]] ![![3, -2, 0]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![23, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![23, 1, 0]] 
 ![![53, 0, 0], ![23, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![23, 1, 0], ![0, 23, 1], ![38, -27, 23]]]
  hmulB := by decide  
  f := ![![![369, 16, 0], ![-848, 0, 0]], ![![161, 7, 0], ![-370, 0, 0]], ![![-13, -1, 0], ![30, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 53, 0], ![-1, 0, 53]], ![![0, 1, 0], ![-10, 23, 1], ![12, -27, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-12, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-12, 1, 0]] 
 ![![53, 0, 0], ![41, 1, 0], ![15, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-12, 1, 0], ![0, -12, 1], ![38, -27, -12]]]
  hmulB := by decide  
  f := ![![![445, -37, 0], ![1961, 0, 0]], ![![361, -30, 0], ![1591, 0, 0]], ![![135, -11, 0], ![595, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 53, 0], ![-15, 0, 53]], ![![-1, 1, 0], ![9, -12, 1], ![25, -27, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-11, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-11, 1, 0]] 
 ![![53, 0, 0], ![42, 1, 0], ![38, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-11, 1, 0], ![0, -11, 1], ![38, -27, -11]]]
  hmulB := by decide  
  f := ![![![386, -35, 0], ![1855, 0, 0]], ![![320, -29, 0], ![1538, 0, 0]], ![![278, -25, 0], ![1336, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 53, 0], ![-38, 0, 53]], ![![-1, 1, 0], ![8, -11, 1], ![30, -27, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![23, 1, 0]] ![![53, 0, 0], ![-12, 1, 0]]
  ![![53, 0, 0], ![42, 11, 1]] where
 M := ![![![2809, 0, 0], ![-636, 53, 0]], ![![1219, 53, 0], ![-276, 11, 1]]]
 hmul := by decide  
 g := ![![![![11, -11, -1], ![53, 0, 0]], ![![-12, 1, 0], ![0, 0, 0]]], ![![![-19, -10, -1], ![53, 0, 0]], ![![-6, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![42, 11, 1]] ![![53, 0, 0], ![-11, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-583, 53, 0]], ![![2226, 583, 53], ![-424, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-11, 1, 0]]], ![![![42, 11, 1]], ![![-8, -2, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![42, 29, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![42, 29, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![42, 29, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![42, 29, 1], ![38, 15, 29], ![1102, -745, 15]]]
  hmulB := by decide  
  f := ![![![-41, -29, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -29, 59]], ![![0, 0, 1], ![-20, -14, 29], ![8, -20, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [57, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 58], [0, 1]]
 g := ![![[49, 29], [56, 12], [48], [53, 3], [39, 1]], ![[0, 30], [52, 47], [48], [52, 56], [19, 58]]]
 h' := ![![[39, 58], [53, 41], [4, 37], [47, 15], [19, 48], [0, 1]], ![[0, 1], [0, 18], [31, 22], [42, 44], [3, 11], [39, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [4, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [57, 20, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![133, -36, -46]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, 22, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![44, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![0, -29, 1], ![38, -27, -29]]]
  hmulB := by decide  
  f := ![![![1712, -59, 0], ![3481, 0, 0]], ![![900, -31, 0], ![1830, 0, 0]], ![![1320, -45, 0], ![2684, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-44, 0, 59]], ![![-1, 1, 0], ![14, -29, 1], ![36, -27, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![42, 29, 1]] ![![59, 0, 0], ![-29, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1711, 59, 0]], ![![2478, 1711, 59], ![-1180, -826, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-29, 1, 0]]], ![![![42, 29, 1]], ![![-20, -14, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, 27, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, 27, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![24, 27, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, 27, 1], ![38, -3, 27], ![1026, -691, -3]]]
  hmulB := by decide  
  f := ![![![-23, -27, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -27, 61]], ![![0, 0, 1], ![-10, -12, 27], ![18, -10, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [25, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 60], [0, 1]]
 g := ![![[42, 22], [4], [14, 5], [17, 57], [48, 1]], ![[0, 39], [4], [10, 56], [8, 4], [35, 60]]]
 h' := ![![[48, 60], [34, 12], [16, 2], [2, 35], [20, 22], [0, 1]], ![[0, 1], [0, 49], [51, 59], [35, 26], [39, 39], [48, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [6, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [25, 13, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1483, -703, 349]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-113, -166, 349]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![3, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![0, -27, 1], ![38, -27, -27]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![3538, 0, 0]], ![![892, -33, 0], ![2014, 0, 0]], ![![93, -3, 0], ![210, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-3, 0, 61]], ![![-1, 1, 0], ![15, -27, 1], ![17, -27, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![24, 27, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![1464, 1647, 61], ![-610, -732, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![24, 27, 1]], ![![-10, -12, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![43, 4, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![43, 4, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![43, 4, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![43, 4, 1], ![38, 16, 4], ![152, -70, 16]]]
  hmulB := by decide  
  f := ![![![-42, -4, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -4, 67]], ![![0, 0, 1], ![-2, 0, 4], ![-8, -2, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [15, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 66], [0, 1]]
 g := ![![[32, 9], [38, 40], [19], [16], [54], [1]], ![[0, 58], [0, 27], [19], [16], [54], [1]]]
 h' := ![![[56, 66], [33, 3], [4, 43], [17, 35], [18, 4], [52, 56], [0, 1]], ![[0, 1], [0, 64], [0, 24], [34, 32], [41, 63], [39, 11], [56, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [13, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [15, 11, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-223, 227, -27]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 5, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-4, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-4, 1, 0]] 
 ![![67, 0, 0], ![63, 1, 0], ![51, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-4, 1, 0], ![0, -4, 1], ![38, -27, -4]]]
  hmulB := by decide  
  f := ![![![77, -19, 0], ![1273, 0, 0]], ![![73, -18, 0], ![1207, 0, 0]], ![![61, -15, 0], ![1009, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 67, 0], ![-51, 0, 67]], ![![-1, 1, 0], ![3, -4, 1], ![29, -27, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![43, 4, 1]] ![![67, 0, 0], ![-4, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-268, 67, 0]], ![![2881, 268, 67], ![-134, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-4, 1, 0]]], ![![![43, 4, 1]], ![![-2, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![16, 29, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![16, 29, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![16, 29, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![16, 29, 1], ![38, -11, 29], ![1102, -745, -11]]]
  hmulB := by decide  
  f := ![![![-15, -29, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -29, 71]], ![![0, 0, 1], ![-6, -12, 29], ![18, -6, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [41, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 70], [0, 1]]
 g := ![![[8, 1], [34, 8], [69, 57], [9], [19], [1]], ![[35, 70], [37, 63], [46, 14], [9], [19], [1]]]
 h' := ![![[27, 70], [26, 1], [11, 24], [1, 46], [50, 3], [30, 27], [0, 1]], ![[0, 1], [53, 70], [20, 47], [36, 25], [60, 68], [49, 44], [27, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [62, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [41, 44, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![193, 88, -19]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 9, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-29, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-29, 1, 0]] 
 ![![71, 0, 0], ![42, 1, 0], ![11, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-29, 1, 0], ![0, -29, 1], ![38, -27, -29]]]
  hmulB := by decide  
  f := ![![![1770, -61, 0], ![4331, 0, 0]], ![![1074, -37, 0], ![2628, 0, 0]], ![![302, -10, 0], ![739, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 71, 0], ![-11, 0, 71]], ![![-1, 1, 0], ![17, -29, 1], ![21, -27, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![16, 29, 1]] ![![71, 0, 0], ![-29, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2059, 71, 0]], ![![1136, 2059, 71], ![-426, -852, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-29, 1, 0]]], ![![![16, 29, 1]], ![![-6, -12, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![36, -3, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![36, -3, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![36, 70, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![36, -3, 1], ![38, 9, -3], ![-114, 119, 9]]]
  hmulB := by decide  
  f := ![![![-35, 3, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -70, 73]], ![![0, -1, 1], ![2, 3, -3], ![-6, -7, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [38, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 72], [0, 1]]
 g := ![![[4, 25], [38], [18], [35, 3], [36], [1]], ![[0, 48], [38], [18], [17, 70], [36], [1]]]
 h' := ![![[67, 72], [43, 68], [10, 44], [57, 50], [3, 21], [35, 67], [0, 1]], ![[0, 1], [0, 5], [38, 29], [49, 23], [23, 52], [71, 6], [67, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [29, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [38, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1466, 1132, 12]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, 4, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![3, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![3, 1, 0]] 
 ![![73, 0, 0], ![3, 1, 0], ![64, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![3, 1, 0], ![0, 3, 1], ![38, -27, 3]]]
  hmulB := by decide  
  f := ![![![136, 45, 0], ![-3285, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![118, 39, 0], ![-2850, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 73, 0], ![-64, 0, 73]], ![![0, 1, 0], ![-1, 3, 1], ![-1, -27, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![36, -3, 1]] ![![73, 0, 0], ![3, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![219, 73, 0]], ![![2628, -219, 73], ![146, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![3, 1, 0]]], ![![![36, -3, 1]], ![![2, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-14, -14, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-14, -14, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![65, 65, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-14, -14, 1], ![38, -41, -14], ![-532, 416, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -65, 79]], ![![-1, -1, 1], ![12, 11, -14], ![27, 39, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [38, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 78], [0, 1]]
 g := ![![[52, 52], [64, 64], [21, 21], [33, 16], [1], [1]], ![[0, 27], [0, 15], [0, 58], [17, 63], [1], [1]]]
 h' := ![![[78, 78], [17, 17], [71, 71], [10, 10], [63, 75], [41, 78], [0, 1]], ![[0, 1], [0, 62], [0, 8], [0, 69], [67, 4], [42, 1], [78, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [45, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [38, 1, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![144, 65, 1]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 0, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![14, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![14, 1, 0]] 
 ![![79, 0, 0], ![14, 1, 0], ![41, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![14, 1, 0], ![0, 14, 1], ![38, -27, 14]]]
  hmulB := by decide  
  f := ![![![211, 15, 0], ![-1185, 0, 0]], ![![14, 1, 0], ![-78, 0, 0]], ![![101, 7, 0], ![-567, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 79, 0], ![-41, 0, 79]], ![![0, 1, 0], ![-3, 14, 1], ![-2, -27, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-14, -14, 1]] ![![79, 0, 0], ![14, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1106, 79, 0]], ![![-1106, -1106, 79], ![-158, -237, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![14, 1, 0]]], ![![![-14, -14, 1]], ![![-2, -3, 0]]]]
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


lemma PB98I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB98I1 : PrimesBelowBoundCertificateInterval O 31 79 98 where
  m := 11
  g := ![2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB98I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I47N1, I53N0, I53N1, I53N2, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [], [], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
