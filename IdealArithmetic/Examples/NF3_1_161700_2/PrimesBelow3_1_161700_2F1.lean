
import IdealArithmetic.Examples.NF3_1_161700_2.RI3_1_161700_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [12, 21, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 35, 3], [20, 1, 34], [0, 1]]
 g := ![![[29, 1, 25], [34, 33], [9, 32, 16], [5, 1], []], ![[1, 24, 1, 4], [36, 7], [19, 14, 26, 33], [3, 1], [33, 9]], ![[18, 2, 20, 36], [15, 9], [35, 34, 15, 33], [16, 4], [2, 9]]]
 h' := ![![[22, 35, 3], [8, 32, 5], [3, 30, 12], [14, 31, 4], [0, 0, 1], [0, 1]], ![[20, 1, 34], [5, 5, 27], [17, 2, 28], [12, 8, 23], [14, 36, 1], [22, 35, 3]], ![[0, 1], [12, 0, 5], [9, 5, 34], [29, 35, 10], [6, 1, 35], [20, 1, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 6], []]
 b := ![[], [35, 16, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [12, 21, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1215228, 103970, -50320]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32844, 2810, -1360]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [34, 15, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 11, 11], [18, 29, 30], [0, 1]]
 g := ![![[16], [31, 2], [2, 2], [34, 7, 1], []], ![[25, 30, 6, 17], [7, 32], [36, 32], [30, 40, 38, 26], [23, 39]], ![[12, 38, 8, 24], [10, 9], [21, 18], [38, 33, 40, 22], [4, 39]]]
 h' := ![![[30, 11, 11], [28, 37], [37, 21, 17], [33, 31, 17], [0, 0, 1], [0, 1]], ![[18, 29, 30], [31, 38, 38], [8, 18, 27], [17, 5, 14], [36, 14, 29], [30, 11, 11]], ![[0, 1], [38, 7, 3], [3, 2, 38], [15, 5, 10], [24, 27, 11], [18, 29, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 9], []]
 b := ![[], [13, 2, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [34, 15, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![515944, 738, 5904]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12584, 18, 144]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [27, 11, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 34, 29], [6, 8, 14], [0, 1]]
 g := ![![[4, 39, 25], [31, 17, 40], [34, 40], [30, 27, 1], []], ![[7, 16, 5, 2], [40, 7, 24, 37], [35, 38], [14, 0, 36, 7], [40, 24]], ![[28, 12, 40, 13], [12, 0, 7, 36], [31, 11], [2, 2, 29, 16], [12, 24]]]
 h' := ![![[21, 34, 29], [23, 12, 38], [34, 17, 13], [7, 16, 13], [0, 0, 1], [0, 1]], ![[6, 8, 14], [30, 41, 7], [39, 10, 38], [34, 19, 9], [6, 39, 8], [21, 34, 29]], ![[0, 1], [30, 33, 41], [4, 16, 35], [14, 8, 21], [13, 4, 34], [6, 8, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 16], []]
 b := ![[], [15, 39, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [27, 11, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-196037, -2236, -9890]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4559, -52, -230]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [23, 37, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 20, 31], [43, 26, 16], [0, 1]]
 g := ![![[20, 9, 32], [25, 32, 14], [25, 21, 21], [46, 6, 1], []], ![[29, 21, 0, 46], [31, 1, 43, 44], [38, 20, 14, 11], [45, 19, 5, 41], [3, 21]], ![[36, 26, 38, 7], [27, 6, 12, 42], [39, 23, 35, 27], [25, 5, 0, 8], [18, 21]]]
 h' := ![![[10, 20, 31], [36, 11, 28], [36, 14, 25], [23, 40, 31], [0, 0, 1], [0, 1]], ![[43, 26, 16], [27, 5, 35], [11, 36, 3], [21, 3, 25], [31, 41, 26], [10, 20, 31]], ![[0, 1], [34, 31, 31], [41, 44, 19], [27, 4, 38], [25, 6, 20], [43, 26, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 5], []]
 b := ![[], [16, 27, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [23, 37, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2048542, 190444, -72897]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43586, 4052, -1551]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-16, -24, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-16, -24, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![37, 29, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-16, -24, 1], ![78, -42, -144], ![-1885, 61, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -29, 53]], ![![-1, -1, 1], ![102, 78, -144], ![-23, 11, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [8, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 52], [0, 1]]
 g := ![![[29, 1], [25], [9, 29], [17], [33, 1]], ![[9, 52], [25], [12, 24], [17], [13, 52]]]
 h' := ![![[33, 52], [2, 52], [34, 5], [24, 20], [1, 21], [0, 1]], ![[0, 1], [22, 1], [40, 48], [48, 33], [5, 32], [33, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [42, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [8, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1867, 1449, -438]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![341, 267, -438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-15, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-15, 1, 0]] 
 ![![53, 0, 0], ![38, 1, 0], ![18, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-15, 1, 0], ![0, -14, 6], ![78, -2, -15]]]
  hmulB := by decide  
  f := ![![![721, -48, 0], ![2544, 0, 0]], ![![526, -35, 0], ![1856, 0, 0]], ![![246, -14, -1], ![868, 9, 0]]]
  g := ![![![1, 0, 0], ![-38, 53, 0], ![-18, 0, 53]], ![![-1, 1, 0], ![8, -14, 6], ![8, -2, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-16, -24, 1]] ![![53, 0, 0], ![-15, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-795, 53, 0]], ![![-848, -1272, 53], ![318, 318, -159]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-15, 1, 0]]], ![![![-16, -24, 1]], ![![6, 6, -3]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![7, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![7, 1, 0]] 
 ![![59, 0, 0], ![7, 1, 0], ![30, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![7, 1, 0], ![0, 8, 6], ![78, -2, 7]]]
  hmulB := by decide  
  f := ![![![92, 13, 0], ![-767, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![38, 4, -1], ![-316, 10, 0]]]
  g := ![![![1, 0, 0], ![-7, 59, 0], ![-30, 0, 59]], ![![0, 1, 0], ![-4, 8, 6], ![-2, -2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, 1, 0]] 
 ![![59, 0, 0], ![15, 1, 0], ![19, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, 1, 0], ![0, 16, 6], ![78, -2, 15]]]
  hmulB := by decide  
  f := ![![![31, 2, 0], ![-118, 0, 0]], ![![-15, -1, 0], ![60, 0, 0]], ![![11, -2, -1], ![-42, 10, 0]]]
  g := ![![![1, 0, 0], ![-15, 59, 0], ![-19, 0, 59]], ![![0, 1, 0], ![-6, 16, 6], ![-3, -2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![0, -22, 6], ![78, -2, -23]]]
  hmulB := by decide  
  f := ![![![967, -42, 0], ![2478, 0, 0]], ![![576, -25, 0], ![1476, 0, 0]], ![![224, -6, -1], ![574, 10, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-14, 0, 59]], ![![-1, 1, 0], ![12, -22, 6], ![8, -2, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![7, 1, 0]] ![![59, 0, 0], ![15, 1, 0]]
  ![![59, 0, 0], ![-12, -6, 1]] where
 M := ![![![3481, 0, 0], ![885, 59, 0]], ![![413, 59, 0], ![105, 23, 6]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-12, -6, 1]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![-708, -354, 59], ![354, 118, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-23, 1, 0]]], ![![![-12, -6, 1]], ![![6, 2, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-3, 16, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-3, 16, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![58, 16, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-3, 16, 1], ![78, 11, 96], ![1235, -19, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -16, 61]], ![![-1, 0, 1], ![-90, -25, 96], ![25, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [57, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 60], [0, 1]]
 g := ![![[54, 15], [13], [21, 46], [54, 25], [33, 1]], ![[0, 46], [13], [14, 15], [25, 36], [5, 60]]]
 h' := ![![[33, 60], [32, 36], [23, 14], [33, 30], [10, 56], [0, 1]], ![[0, 1], [0, 25], [58, 47], [47, 31], [28, 5], [33, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [57, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [57, 28, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182593, 125533, -14972]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17229, 5985, -14972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![26, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![26, 1, 0]] 
 ![![61, 0, 0], ![26, 1, 0], ![5, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![26, 1, 0], ![0, 27, 6], ![78, -2, 26]]]
  hmulB := by decide  
  f := ![![![469, 18, 0], ![-1098, 0, 0]], ![![182, 7, 0], ![-426, 0, 0]], ![![41, -21, -5], ![-96, 51, 0]]]
  g := ![![![1, 0, 0], ![-26, 61, 0], ![-5, 0, 61]], ![![0, 1, 0], ![-12, 27, 6], ![0, -2, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-3, 16, 1]] ![![61, 0, 0], ![26, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1586, 61, 0]], ![![-183, 976, 61], ![0, 427, 122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![26, 1, 0]]], ![![![-3, 16, 1]], ![![0, 7, 2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![21, 7, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![21, 7, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![21, 7, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![21, 7, 1], ![78, 26, 42], ![533, -1, 19]]]
  hmulB := by decide  
  f := ![![![-20, -7, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -7, 67]], ![![0, 0, 1], ![-12, -4, 42], ![2, -2, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [8, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 66], [0, 1]]
 g := ![![[28, 23], [29, 24], [49], [49], [60], [1]], ![[35, 44], [13, 43], [49], [49], [60], [1]]]
 h' := ![![[44, 66], [36, 31], [35, 15], [5, 7], [53, 60], [59, 44], [0, 1]], ![[0, 1], [60, 36], [25, 52], [45, 60], [13, 7], [52, 23], [44, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [59, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [8, 23, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1741, 1027, 51]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 10, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![25, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![25, 1, 0]] 
 ![![67, 0, 0], ![25, 1, 0], ![48, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![25, 1, 0], ![0, 26, 6], ![78, -2, 25]]]
  hmulB := by decide  
  f := ![![![726, 29, 0], ![-1943, 0, 0]], ![![250, 10, 0], ![-669, 0, 0]], ![![494, 24, 1], ![-1322, -11, 0]]]
  g := ![![![1, 0, 0], ![-25, 67, 0], ![-48, 0, 67]], ![![0, 1, 0], ![-14, 26, 6], ![-16, -2, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![21, 7, 1]] ![![67, 0, 0], ![25, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1675, 67, 0]], ![![1407, 469, 67], ![603, 201, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![25, 1, 0]]], ![![![21, 7, 1]], ![![9, 3, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [48, 14, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 53, 46], [67, 17, 25], [0, 1]]
 g := ![![[56, 5, 43], [13, 52, 19], [70, 30, 36], [7, 58], [6, 1], []], ![[22, 24, 61, 68], [36, 52, 50, 17], [18, 65, 46, 67], [16, 40], [13, 5], [35, 57]], ![[39, 18, 9, 6], [27, 17, 18, 49], [68, 58, 26, 3], [68, 16], [9, 40], [56, 57]]]
 h' := ![![[10, 53, 46], [15, 52, 16], [48, 12, 27], [35, 20, 6], [67, 10, 22], [0, 0, 1], [0, 1]], ![[67, 17, 25], [34, 50, 37], [37, 19, 17], [56, 63, 28], [55, 22, 53], [53, 35, 17], [10, 53, 46]], ![[0, 1], [10, 40, 18], [63, 40, 27], [40, 59, 37], [31, 39, 67], [26, 36, 53], [67, 17, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 26], []]
 b := ![[], [32, 45, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [48, 14, 65, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4989383, 21087, 119493]
  a := ![0, 3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70273, 297, 1683]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-20, 3, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-20, 3, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![53, 3, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-20, 3, 1], ![78, -19, 18], ![221, 7, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -3, 73]], ![![-1, 0, 1], ![-12, -1, 18], ![19, 1, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [57, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 72], [0, 1]]
 g := ![![[39, 41], [23], [70], [32, 32], [67], [1]], ![[0, 32], [23], [70], [71, 41], [67], [1]]]
 h' := ![![[40, 72], [22, 25], [26, 60], [1, 17], [14, 18], [16, 40], [0, 1]], ![[0, 1], [0, 48], [17, 13], [24, 56], [4, 55], [10, 33], [40, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [46, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [57, 33, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28779, 17324, -3910]
  a := ![2, -8, -38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3233, 398, -3910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-18, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-18, 1, 0]] 
 ![![73, 0, 0], ![55, 1, 0], ![22, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-18, 1, 0], ![0, -17, 6], ![78, -2, -18]]]
  hmulB := by decide  
  f := ![![![1279, -71, 0], ![5183, 0, 0]], ![![973, -54, 0], ![3943, 0, 0]], ![![382, -7, -5], ![1548, 61, 0]]]
  g := ![![![1, 0, 0], ![-55, 73, 0], ![-22, 0, 73]], ![![-1, 1, 0], ![11, -17, 6], ![8, -2, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-20, 3, 1]] ![![73, 0, 0], ![-18, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1314, 73, 0]], ![![-1460, 219, 73], ![438, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-18, 1, 0]]], ![![![-20, 3, 1]], ![![6, -1, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [35, 25, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 9, 34], [15, 69, 45], [0, 1]]
 g := ![![[22, 29, 16], [64, 56, 65], [53, 47, 40], [69, 9, 67], [35, 1], []], ![[46, 62, 77, 28], [59, 45, 56, 35], [71, 34, 44, 60], [57, 14, 23, 61], [45, 21], [71, 50]], ![[40, 68, 22, 44], [16, 49, 18, 40], [44, 15, 67, 52], [74, 45, 2, 46], [2, 2], [60, 50]]]
 h' := ![![[20, 9, 34], [51, 17, 75], [41, 3, 12], [34, 34, 44], [39, 38, 15], [0, 0, 1], [0, 1]], ![[15, 69, 45], [41, 15, 65], [45, 46, 61], [61, 7, 5], [18, 30, 36], [48, 74, 69], [20, 9, 34]], ![[0, 1], [64, 47, 18], [22, 30, 6], [46, 38, 30], [55, 11, 28], [21, 5, 9], [15, 69, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 60], []]
 b := ![[], [18, 40, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [35, 25, 44, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9954, 1027, 1501]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![126, 13, 19]
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



lemma PB114I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB114I1 : PrimesBelowBoundCertificateInterval O 31 79 114 where
  m := 11
  g := ![1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB114I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
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
      exact NI59N1
      exact NI59N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I53N1, I59N0, I59N1, I59N2, I61N1, I67N1, I73N1]
  Il := ![[], [], [], [], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
