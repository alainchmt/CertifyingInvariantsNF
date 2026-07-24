
import IdealArithmetic.Examples.NF3_1_119660_3.RI3_1_119660_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-303317, -52757, -15571]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-303317, -52757, -15571]] 
 ![![37, 0, 0], ![0, 37, 0], ![20, 7, 1]] where
  M :=![![![-303317, -52757, -15571], ![-1027686, -178749, -52757], ![-3481962, -605630, -178749]]]
  hmulB := by decide  
  f := ![![![457, -101, -10]], ![![-660, 537, -101]], ![![-58, 51, -10]]]
  g := ![![![219, 1520, -15571], ![742, 5150, -52757], ![2514, 17449, -178749]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[23, 30], [30], [14, 4], [4], [1]], ![[0, 7], [30], [6, 33], [4], [1]]]
 h' := ![![[35, 36], [3, 20], [2, 20], [24, 2], [16, 35], [0, 1]], ![[0, 1], [0, 17], [36, 17], [20, 35], [20, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [25, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153, 48, -9]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 3, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, -101, -10]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![457, -101, -10]] 
 ![![37, 0, 0], ![30, 1, 0], ![25, 0, 1]] where
  M :=![![![457, -101, -10], ![-660, 537, -101], ![-6666, 148, 537]]]
  hmulB := by decide  
  f := ![![![-303317, -52757, -15571]], ![![-273708, -47607, -14051]], ![![-299051, -52015, -15352]]]
  g := ![![![101, -101, -10], ![-385, 537, -101], ![-663, 148, 537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-303317, -52757, -15571]] ![![457, -101, -10]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1363, 237, 70]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1363, 237, 70]] 
 ![![41, 0, 0], ![0, 41, 0], ![6, 11, 1]] where
  M :=![![![1363, 237, 70], ![4620, 803, 237], ![15642, 2724, 803]]]
  hmulB := by decide  
  f := ![![![-19, 9, -1]], ![![-66, -11, 9]], ![![-6, -5, 2]]]
  g := ![![![23, -13, 70], ![78, -44, 237], ![264, -149, 803]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 22, 1] where
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
 g := ![![[16, 21], [18], [36], [11, 33], [1]], ![[5, 20], [18], [36], [23, 8], [1]]]
 h' := ![![[19, 40], [4, 29], [30, 31], [31, 6], [14, 19], [0, 1]], ![[0, 1], [22, 12], [4, 10], [22, 35], [6, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [32, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-786, 650, -8]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, 18, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 9, -1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-19, 9, -1]] 
 ![![41, 0, 0], ![30, 1, 0], ![2, 0, 1]] where
  M :=![![![-19, 9, -1], ![-66, -11, 9], ![594, -138, -11]]]
  hmulB := by decide  
  f := ![![![1363, 237, 70]], ![![1110, 193, 57]], ![![448, 78, 23]]]
  g := ![![![-7, 9, -1], ![6, -11, 9], ![116, -138, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1363, 237, 70]] ![![-19, 9, -1]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [27, 18, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 4, 21], [24, 38, 22], [0, 1]]
 g := ![![[9, 4, 31], [32, 3, 38], [29, 14], [41, 39, 1], []], ![[25, 5, 4, 4], [22, 37, 41, 31], [31, 6], [32, 32, 16, 9], [38, 11]], ![[12, 5, 22, 18], [2, 6, 21, 28], [22, 31], [32, 37, 21, 8], [37, 11]]]
 h' := ![![[15, 4, 21], [39, 19, 26], [26, 32, 34], [11, 15, 10], [0, 0, 1], [0, 1]], ![[24, 38, 22], [9, 7, 11], [18, 8, 29], [9, 7, 7], [16, 42, 38], [15, 4, 21]], ![[0, 1], [32, 17, 6], [0, 3, 23], [11, 21, 26], [7, 1, 4], [24, 38, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 18], []]
 b := ![[], [36, 35, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [27, 18, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-227943, -2580, -10320]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5301, -60, -240]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [36, 8, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 3, 3], [38, 43, 44], [0, 1]]
 g := ![![[14, 26, 12], [42, 45, 21], [40, 44, 27], [8, 4, 1], []], ![[8, 28, 23, 7], [33, 41, 17, 2], [0, 40, 17, 18], [19, 31, 15, 1], [7, 9]], ![[41, 20, 22, 20], [15, 10, 14, 38], [18, 14, 45, 44], [44, 21, 13, 20], [13, 9]]]
 h' := ![![[13, 3, 3], [39, 25, 24], [17, 12, 16], [41, 27, 11], [0, 0, 1], [0, 1]], ![[38, 43, 44], [17, 18, 26], [20, 45, 19], [43, 2, 37], [11, 27, 43], [13, 3, 3]], ![[0, 1], [20, 4, 44], [15, 37, 12], [6, 18, 46], [36, 20, 3], [38, 43, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 4], []]
 b := ![[], [0, 11, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [36, 8, 43, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-149930, 59267, -3431]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3190, 1261, -73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![14, -18, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![14, -18, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![14, 35, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![14, -18, 1], ![66, 6, -18], ![-1188, 210, 6]]]
  hmulB := by decide  
  f := ![![![-13, 18, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -35, 53]], ![![0, -1, 1], ![6, 12, -18], ![-24, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [38, 49, 1] where
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
 g := ![![[25, 7], [17], [43, 13], [7], [4, 1]], ![[0, 46], [17], [42, 40], [7], [8, 52]]]
 h' := ![![[4, 52], [18, 22], [9, 21], [48, 38], [7, 31], [0, 1]], ![[0, 1], [0, 31], [40, 32], [41, 15], [25, 22], [4, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [14, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [38, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![170, 1, -56]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 37, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![18, 1, 0]] 
 ![![53, 0, 0], ![18, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![18, 1, 0], ![0, 18, 1], ![66, -8, 18]]]
  hmulB := by decide  
  f := ![![![19, 1, 0], ![-53, 0, 0]], ![![-18, -1, 0], ![54, 0, 0]], ![![25, 1, 0], ![-71, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 53, 0], ![-47, 0, 53]], ![![0, 1, 0], ![-7, 18, 1], ![-12, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![14, -18, 1]] ![![53, 0, 0], ![18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![954, 53, 0]], ![![742, -954, 53], ![318, -318, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![18, 1, 0]]], ![![![14, -18, 1]], ![![6, -6, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [20, 46, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 38, 6], [20, 20, 53], [0, 1]]
 g := ![![[40, 28, 36], [42, 55, 17], [23, 41], [28, 2, 51], [1]], ![[25, 53, 44, 55], [40, 17, 27, 30], [16, 1], [15, 50, 3, 32], [1, 10, 57, 39]], ![[45, 24, 39, 19], [23, 36, 29, 12], [42, 3], [5, 23, 45, 3], [58, 20, 12, 20]]]
 h' := ![![[26, 38, 6], [45, 57, 53], [27, 26, 28], [30, 16, 10], [39, 13, 46], [0, 1]], ![[20, 20, 53], [43, 50, 45], [37, 46, 8], [48, 44, 1], [33, 0, 54], [26, 38, 6]], ![[0, 1], [24, 11, 20], [6, 46, 23], [43, 58, 48], [55, 46, 18], [20, 20, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 54], []]
 b := ![[], [16, 28, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [20, 46, 13, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![467162, 16815, 885]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7918, 285, 15]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [58, 30, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 52, 43], [7, 8, 18], [0, 1]]
 g := ![![[2, 29, 46], [59, 22], [20, 35, 22], [55, 14, 47], [1]], ![[10, 44, 56, 50], [4, 49], [32, 39, 60, 35], [54, 52, 21, 54], [6, 16, 43, 24]], ![[43, 15, 30, 10], [44, 56], [46, 15, 46, 59], [50, 50, 1, 51], [30, 42, 22, 37]]]
 h' := ![![[6, 52, 43], [56, 41, 31], [60, 12, 49], [43, 48, 12], [3, 31, 13], [0, 1]], ![[7, 8, 18], [48, 38, 59], [6, 6, 54], [30, 3, 25], [51, 55, 34], [6, 52, 43]], ![[0, 1], [11, 43, 32], [60, 43, 19], [36, 10, 24], [6, 36, 14], [7, 8, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 57], []]
 b := ![[], [52, 34, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [58, 30, 48, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25071, 4575, 854]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-411, 75, 14]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![953, 166, 49]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![953, 166, 49]] 
 ![![67, 0, 0], ![0, 67, 0], ![55, 28, 1]] where
  M :=![![![953, 166, 49], ![3234, 561, 166], ![10956, 1906, 561]]]
  hmulB := by decide  
  f := ![![![-25, 4, 1]], ![![66, -33, 4]], ![![11, -10, 2]]]
  g := ![![![-26, -18, 49], ![-88, -61, 166], ![-297, -206, 561]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [30, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 66], [0, 1]]
 g := ![![[23, 16], [38, 23], [21], [17], [65], [1]], ![[38, 51], [47, 44], [21], [17], [65], [1]]]
 h' := ![![[47, 66], [66, 63], [46, 36], [41, 17], [22, 34], [37, 47], [0, 1]], ![[0, 1], [12, 4], [63, 31], [36, 50], [12, 33], [35, 20], [47, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [43, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [30, 20, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![294, 252, 9]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 0, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -4, -1]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![25, -4, -1]] 
 ![![67, 0, 0], ![39, 1, 0], ![20, 0, 1]] where
  M :=![![![25, -4, -1], ![-66, 33, -4], ![-264, -34, 33]]]
  hmulB := by decide  
  f := ![![![-953, -166, -49]], ![![-603, -105, -31]], ![![-448, -78, -23]]]
  g := ![![![3, -4, -1], ![-19, 33, -4], ![6, -34, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![953, 166, 49]] ![![25, -4, -1]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38327, -32898, 6371]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![38327, -32898, 6371]] 
 ![![71, 0, 0], ![0, 71, 0], ![53, 20, 1]] where
  M :=![![![38327, -32898, 6371], ![420486, -12641, -32898], ![-2171268, 683670, -12641]]]
  hmulB := by decide  
  f := ![![![-319030571, -55490112, -16377665]], ![![-1080925890, -188009251, -55490112]], ![![-594218105, -103354450, -30504616]]]
  g := ![![![-4216, -2258, 6371], ![30480, 9089, -32898], ![-21145, 13190, -12641]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [53, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 70], [0, 1]]
 g := ![![[44, 10], [9, 50], [63, 4], [32], [50], [1]], ![[12, 61], [62, 21], [36, 67], [32], [50], [1]]]
 h' := ![![[11, 70], [20, 9], [69, 11], [13, 69], [17, 23], [18, 11], [0, 1]], ![[0, 1], [48, 62], [48, 60], [62, 2], [57, 48], [68, 60], [11, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [3, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [53, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2463, -56, 196]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-181, -56, 196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![319030571, 55490112, 16377665]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![319030571, 55490112, 16377665]] 
 ![![71, 0, 0], ![51, 1, 0], ![26, 0, 1]] where
  M :=![![![319030571, 55490112, 16377665], ![1080925890, 188009251, 55490112], ![3662347392, 637004994, 188009251]]]
  hmulB := by decide  
  f := ![![![-38327, 32898, -6371]], ![![-33453, 23809, -4113]], ![![16546, 2418, -2155]]]
  g := ![![![-41363161, 55490112, 16377665], ![-140144913, 188009251, 55490112], ![-474833068, 637004994, 188009251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![38327, -32898, 6371]] ![![319030571, 55490112, 16377665]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![2, 33, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![2, 33, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![2, 33, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![2, 33, 1], ![66, -6, 33], ![2178, -198, -6]]]
  hmulB := by decide  
  f := ![![![-1, -33, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -33, 73]], ![![0, 0, 1], ![0, -15, 33], ![30, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [29, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 72], [0, 1]]
 g := ![![[26, 35], [16], [25], [10, 46], [65], [1]], ![[62, 38], [16], [25], [1, 27], [65], [1]]]
 h' := ![![[49, 72], [55, 53], [9, 4], [2, 5], [51, 51], [44, 49], [0, 1]], ![[0, 1], [24, 20], [59, 69], [28, 68], [68, 22], [36, 24], [49, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [52, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [29, 24, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![378, 32, 43]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, -19, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-33, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-33, 1, 0]] 
 ![![73, 0, 0], ![40, 1, 0], ![6, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-33, 1, 0], ![0, -33, 1], ![66, -8, -33]]]
  hmulB := by decide  
  f := ![![![1486, -45, 0], ![3285, 0, 0]], ![![826, -25, 0], ![1826, 0, 0]], ![![180, -5, 0], ![398, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 73, 0], ![-6, 0, 73]], ![![-1, 1, 0], ![18, -33, 1], ![8, -8, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![2, 33, 1]] ![![73, 0, 0], ![-33, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2409, 73, 0]], ![![146, 2409, 73], ![0, -1095, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-33, 1, 0]]], ![![![2, 33, 1]], ![![0, -15, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [57, 67, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 57, 20], [70, 21, 59], [0, 1]]
 g := ![![[30, 51, 36], [23, 2, 40], [40, 26, 65], [77, 13, 10], [19, 1], []], ![[1, 6, 77, 31], [50, 19, 78, 36], [65, 45, 70, 26], [40, 48, 38, 10], [36, 46], [5, 5]], ![[1, 27, 70, 61], [31, 19, 54, 6], [2, 38, 40, 47], [51, 61, 49, 17], [72, 10], [45, 5]]]
 h' := ![![[28, 57, 20], [32, 46, 6], [11, 65, 44], [35, 1, 67], [23, 13, 57], [0, 0, 1], [0, 1]], ![[70, 21, 59], [48, 42, 19], [8, 32, 12], [0, 3, 5], [74, 10, 35], [25, 44, 21], [28, 57, 20]], ![[0, 1], [40, 70, 54], [19, 61, 23], [51, 75, 7], [44, 56, 66], [44, 35, 57], [70, 21, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 76], []]
 b := ![[], [41, 57, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [57, 67, 60, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31205, -3002, -158]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![395, -38, -2]
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



lemma PB98I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB98I1 : PrimesBelowBoundCertificateInterval O 31 79 98 where
  m := 11
  g := ![2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB98I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
  β := ![I37N1, I41N1, I53N1, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [], [], [I53N1], [], [], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
