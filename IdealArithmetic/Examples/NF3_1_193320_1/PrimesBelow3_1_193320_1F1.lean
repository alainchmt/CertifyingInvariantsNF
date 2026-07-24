
import IdealArithmetic.Examples.NF3_1_193320_1.RI3_1_193320_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17934865, -7526200, -851884]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-17934865, -7526200, -851884]] 
 ![![37, 0, 0], ![0, 37, 0], ![27, 11, 1]] where
  M :=![![![-17934865, -7526200, -851884], ![-158450424, -66492253, -7526200], ![-1399873200, -587443824, -66492253]]]
  hmulB := by decide  
  f := ![![![-22357, -968, 396]], ![![73656, 215, -968]], ![![717, -143, 7]]]
  g := ![![![136919, 49852, -851884], ![1209648, 440431, -7526200], ![10686963, 3891107, -66492253]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [15, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 36], [0, 1]]
 g := ![![[21, 28], [33], [35, 1], [28], [1]], ![[7, 9], [33], [16, 36], [28], [1]]]
 h' := ![![[18, 36], [35, 19], [30, 12], [27, 1], [22, 18], [0, 1]], ![[0, 1], [7, 18], [24, 25], [8, 36], [13, 19], [18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [11, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [15, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![387, 281, 39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -4, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22357, -968, 396]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-22357, -968, 396]] 
 ![![37, 0, 0], ![26, 1, 0], ![27, 0, 1]] where
  M :=![![![-22357, -968, 396], ![73656, 215, -968], ![-180048, 18480, 215]]]
  hmulB := by decide  
  f := ![![![-17934865, -7526200, -851884]], ![![-16885322, -7085769, -802032]], ![![-50922015, -21368952, -2418733]]]
  g := ![![![-213, -968, 396], ![2546, 215, -968], ![-18009, 18480, 215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-17934865, -7526200, -851884]] ![![-22357, -968, 396]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![0, 12, 1], ![186, 57, 12]]]
  hmulB := by decide  
  f := ![![![193, 16, 0], ![-656, 0, 0]], ![![36, 3, 0], ![-122, 0, 0]], ![![76, 6, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-20, 0, 41]], ![![0, 1, 0], ![-4, 12, 1], ![-18, 57, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![0, 14, 1], ![186, 57, 14]]]
  hmulB := by decide  
  f := ![![![15, 1, 0], ![-41, 0, 0]], ![![-14, -1, 0], ![42, 0, 0]], ![![-9, -1, 0], ![27, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-9, 0, 41]], ![![0, 1, 0], ![-5, 14, 1], ![-18, 57, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, 1, 0]] 
 ![![41, 0, 0], ![15, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, 1, 0], ![0, 15, 1], ![186, 57, 15]]]
  hmulB := by decide  
  f := ![![![136, 9, 0], ![-369, 0, 0]], ![![30, 2, 0], ![-81, 0, 0]], ![![66, 4, 0], ![-179, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-6, 15, 1], ![-24, 57, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![12, 1, 0]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0], ![-37, -15, 1]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![492, 41, 0], ![168, 26, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-37, -15, 1]] ![![41, 0, 0], ![15, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![615, 41, 0]], ![![-1517, -615, 41], ![-369, -205, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![15, 1, 0]]], ![![![-37, -15, 1]], ![![-9, -5, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-40, -24, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-40, -24, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![3, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-40, -24, 1], ![186, 17, -24], ![-4464, -1182, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -19, 43]], ![![-1, -1, 1], ![6, 11, -24], ![-105, -35, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [21, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 42], [0, 1]]
 g := ![![[9, 41], [15, 11], [21], [15, 31], [1]], ![[0, 2], [0, 32], [21], [4, 12], [1]]]
 h' := ![![[26, 42], [29, 27], [13, 21], [29, 8], [22, 26], [0, 1]], ![[0, 1], [0, 16], [0, 22], [22, 35], [10, 17], [26, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [6, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [21, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2227, 960, 562]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, -226, 562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![0, -19, 1], ![186, 57, -19]]]
  hmulB := by decide  
  f := ![![![761, -40, 0], ![1720, 0, 0]], ![![438, -23, 0], ![990, 0, 0]], ![![484, -25, 0], ![1094, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-26, 0, 43]], ![![-1, 1, 0], ![10, -19, 1], ![-16, 57, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-40, -24, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-1720, -1032, 43], ![946, 473, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![-40, -24, 1]], ![![22, 11, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-33, -27, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-33, -27, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![14, 20, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-33, -27, 1], ![186, 24, -27], ![-5022, -1353, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -20, 47]], ![![-1, -1, 1], ![12, 12, -27], ![-114, -39, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [17, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 46], [0, 1]]
 g := ![![[14, 36], [10, 21], [6, 25], [28, 9], [1]], ![[0, 11], [41, 26], [25, 22], [1, 38], [1]]]
 h' := ![![[44, 46], [18, 6], [39, 16], [41, 5], [30, 44], [0, 1]], ![[0, 1], [0, 41], [38, 31], [26, 42], [39, 3], [44, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [12, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [17, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3549, -53, 183]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, -79, 183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-20, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-20, 1, 0]] 
 ![![47, 0, 0], ![27, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-20, 1, 0], ![0, -20, 1], ![186, 57, -20]]]
  hmulB := by decide  
  f := ![![![921, -46, 0], ![2162, 0, 0]], ![![541, -27, 0], ![1270, 0, 0]], ![![449, -22, 0], ![1054, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 47, 0], ![-23, 0, 47]], ![![-1, 1, 0], ![11, -20, 1], ![-19, 57, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-33, -27, 1]] ![![47, 0, 0], ![-20, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-940, 47, 0]], ![![-1551, -1269, 47], ![846, 564, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-20, 1, 0]]], ![![![-33, -27, 1]], ![![18, 12, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [22, 20, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 8, 3], [13, 44, 50], [0, 1]]
 g := ![![[16, 36, 43], [6, 40], [29, 2, 47], [6, 17], [1]], ![[25, 6, 45, 31], [12, 44], [0, 32, 47, 33], [2, 52], [22, 23, 20, 27]], ![[12, 4, 5, 18], [5, 47], [25, 44, 46, 35], [21, 4], [35, 36, 6, 26]]]
 h' := ![![[19, 8, 3], [31, 52, 34], [51, 2, 26], [34, 15, 10], [31, 33, 32], [0, 1]], ![[13, 44, 50], [41, 48, 9], [27, 37, 37], [22, 18, 8], [15, 33, 23], [19, 8, 3]], ![[0, 1], [2, 6, 10], [18, 14, 43], [31, 20, 35], [49, 40, 51], [13, 44, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 46], []]
 b := ![[], [42, 12, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [22, 20, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-674372, -454369, -71073]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12724, -8573, -1341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-63, -17, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-63, -17, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![55, 42, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-63, -17, 1], ![186, -6, -17], ![-3162, -783, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -42, 59]], ![![-2, -1, 1], ![19, 12, -17], ![-48, -9, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [3, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 58], [0, 1]]
 g := ![![[26, 20], [56, 35], [29], [34, 16], [40, 1]], ![[0, 39], [40, 24], [29], [25, 43], [21, 58]]]
 h' := ![![[40, 58], [9, 16], [51, 25], [16, 18], [57, 4], [0, 1]], ![[0, 1], [0, 43], [48, 34], [28, 41], [40, 55], [40, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [51, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [3, 19, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![375, 281, 39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -23, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, 1, 0]] 
 ![![59, 0, 0], ![17, 1, 0], ![6, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, 1, 0], ![0, 17, 1], ![186, 57, 17]]]
  hmulB := by decide  
  f := ![![![86, 5, 0], ![-295, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-12, -1, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 59, 0], ![-6, 0, 59]], ![![0, 1, 0], ![-5, 17, 1], ![-15, 57, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-63, -17, 1]] ![![59, 0, 0], ![17, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1003, 59, 0]], ![![-3717, -1003, 59], ![-885, -295, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![17, 1, 0]]], ![![![-63, -17, 1]], ![![-15, -5, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-18, 10, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-18, 10, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![43, 10, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-18, 10, 1], ![186, 39, 10], ![1860, 756, 39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -10, 61]], ![![-1, 0, 1], ![-4, -1, 10], ![3, 6, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [60, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 60], [0, 1]]
 g := ![![[9, 60], [22], [4, 25], [16, 14], [9, 1]], ![[0, 1], [22], [46, 36], [20, 47], [18, 60]]]
 h' := ![![[9, 60], [38, 50], [4, 12], [16, 56], [9, 21], [0, 1]], ![[0, 1], [0, 11], [51, 49], [32, 5], [15, 40], [9, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [8, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [60, 52, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7181, 3378, 472]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-215, -22, 472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, 1, 0]] 
 ![![61, 0, 0], ![51, 1, 0], ![22, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, 1, 0], ![0, -10, 1], ![186, 57, -10]]]
  hmulB := by decide  
  f := ![![![571, -57, 0], ![3477, 0, 0]], ![![481, -48, 0], ![2929, 0, 0]], ![![222, -22, 0], ![1352, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 61, 0], ![-22, 0, 61]], ![![-1, 1, 0], ![8, -10, 1], ![-41, 57, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-18, 10, 1]] ![![61, 0, 0], ![-10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-610, 61, 0]], ![![-1098, 610, 61], ![366, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-10, 1, 0]]], ![![![-18, 10, 1]], ![![6, -1, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-43, -9, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-43, -9, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![24, 58, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-43, -9, 1], ![186, 14, -9], ![-1674, -327, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -58, 67]], ![![-1, -1, 1], ![6, 8, -9], ![-30, -17, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [17, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 66], [0, 1]]
 g := ![![[32, 4], [64, 6], [37], [47], [64], [1]], ![[0, 63], [16, 61], [37], [47], [64], [1]]]
 h' := ![![[59, 66], [51, 65], [3, 41], [30, 38], [5, 28], [50, 59], [0, 1]], ![[0, 1], [0, 2], [10, 26], [61, 29], [49, 39], [47, 8], [59, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [17, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1106, -138, 60]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38, -54, 60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![9, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![9, 1, 0]] 
 ![![67, 0, 0], ![9, 1, 0], ![53, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![9, 1, 0], ![0, 9, 1], ![186, 57, 9]]]
  hmulB := by decide  
  f := ![![![118, 13, 0], ![-871, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![92, 10, 0], ![-679, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 67, 0], ![-53, 0, 67]], ![![0, 1, 0], ![-2, 9, 1], ![-12, 57, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-43, -9, 1]] ![![67, 0, 0], ![9, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![603, 67, 0]], ![![-2881, -603, 67], ![-201, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![9, 1, 0]]], ![![![-43, -9, 1]], ![![-3, -1, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-12, 20, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-12, 20, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![59, 20, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-12, 20, 1], ![186, 45, 20], ![3720, 1326, 45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -20, 71]], ![![-1, 0, 1], ![-14, -5, 20], ![15, 6, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [50, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 70], [0, 1]]
 g := ![![[9, 27], [25, 4], [53, 20], [49], [8], [1]], ![[0, 44], [0, 67], [70, 51], [49], [8], [1]]]
 h' := ![![[47, 70], [28, 13], [48, 2], [12, 37], [41, 7], [21, 47], [0, 1]], ![[0, 1], [0, 58], [0, 69], [47, 34], [15, 64], [29, 24], [47, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [9, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [50, 24, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![794, 996, 277]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-219, -64, 277]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-20, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-20, 1, 0]] 
 ![![71, 0, 0], ![51, 1, 0], ![26, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-20, 1, 0], ![0, -20, 1], ![186, 57, -20]]]
  hmulB := by decide  
  f := ![![![841, -42, 0], ![2982, 0, 0]], ![![621, -31, 0], ![2202, 0, 0]], ![![326, -16, 0], ![1156, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 71, 0], ![-26, 0, 71]], ![![-1, 1, 0], ![14, -20, 1], ![-31, 57, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-12, 20, 1]] ![![71, 0, 0], ![-20, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1420, 71, 0]], ![![-852, 1420, 71], ![426, -355, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-20, 1, 0]]], ![![![-12, 20, 1]], ![![6, -5, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![29, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![29, 1, 0]] 
 ![![73, 0, 0], ![29, 1, 0], ![35, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![29, 1, 0], ![0, 29, 1], ![186, 57, 29]]]
  hmulB := by decide  
  f := ![![![697, 24, 0], ![-1752, 0, 0]], ![![261, 9, 0], ![-656, 0, 0]], ![![331, 11, 0], ![-832, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 73, 0], ![-35, 0, 73]], ![![0, 1, 0], ![-12, 29, 1], ![-34, 57, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-505, -212, -24]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-505, -212, -24]] 
 ![![73, 0, 0], ![46, 1, 0], ![1, 0, 1]] where
  M :=![![![-505, -212, -24], ![-4464, -1873, -212], ![-39432, -16548, -1873]]]
  hmulB := by decide  
  f := ![![![47, -76, 8]], ![![50, -41, 4]], ![![-193, -40, 7]]]
  g := ![![![127, -212, -24], ![1122, -1873, -212], ![9913, -16548, -1873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, 1, 0]] 
 ![![73, 0, 0], ![71, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, 1, 0], ![0, -2, 1], ![186, 57, -2]]]
  hmulB := by decide  
  f := ![![![79, -39, 0], ![2847, 0, 0]], ![![77, -38, 0], ![2775, 0, 0]], ![![75, -37, 0], ![2703, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![1, -2, 1], ![-51, 57, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![29, 1, 0]] ![![-505, -212, -24]]
  ![![73, 0, 0], ![-53, 2, 1]] where
 M := ![![![-36865, -15476, -1752]], ![![-19109, -8021, -908]]]
 hmul := by decide  
 g := ![![![![-293, -220, -28], ![292, 0, 0]]], ![![![-126, -115, -15], ![187, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-53, 2, 1]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-146, 73, 0]], ![![-3869, 146, 73], ![292, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-2, 1, 0]]], ![![![-53, 2, 1]], ![![4, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [4, 25, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 15, 63], [70, 63, 16], [0, 1]]
 g := ![![[38, 75, 67], [59, 55, 44], [23, 78, 20], [30, 41, 19], [76, 1], []], ![[18, 38, 30, 3], [22, 59, 29, 41], [50, 38, 70, 60], [35, 38, 78, 39], [14, 19], [16, 19]], ![[59, 31, 9, 73], [32, 52, 71, 20], [28, 41, 45, 38], [71, 32, 5, 51], [68, 67], [63, 19]]]
 h' := ![![[6, 15, 63], [1, 54, 64], [66, 4, 53], [38, 20, 39], [12, 71, 63], [0, 0, 1], [0, 1]], ![[70, 63, 16], [34, 36, 8], [28, 14, 36], [14, 53, 4], [17, 34, 68], [51, 20, 63], [6, 15, 63]], ![[0, 1], [26, 68, 7], [52, 61, 69], [62, 6, 36], [55, 53, 27], [66, 59, 15], [70, 63, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 42], []]
 b := ![[], [50, 45, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [4, 25, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1248358, -179962, 40922]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15802, -2278, 518]
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



lemma PB125I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB125I1 : PrimesBelowBoundCertificateInterval O 31 79 125 where
  m := 11
  g := ![2, 3, 2, 2, 1, 2, 2, 2, 2, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB125I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N1, I59N1, I61N1, I67N1, I71N1, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [], [I59N1], [I61N1], [I67N1], [I71N1], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
