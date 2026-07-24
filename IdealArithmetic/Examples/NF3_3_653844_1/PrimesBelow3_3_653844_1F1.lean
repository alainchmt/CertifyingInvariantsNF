
import IdealArithmetic.Examples.NF3_3_653844_1.RI3_3_653844_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70919, -1806, 1669]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-70919, -1806, 1669]] 
 ![![37, 0, 0], ![0, 37, 0], ![21, 11, 1]] where
  M :=![![![-70919, -1806, 1669], ![230322, 5855, -5418], ![-249228, -6302, 5855]]]
  hmulB := by decide  
  f := ![![![3697, 1516, 349]], ![![48162, 19751, 4548]], ![![22071, 9051, 2084]]]
  g := ![![![-2864, -545, 1669], ![9300, 1769, -5418], ![-10059, -1911, 5855]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [33, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[2, 9], [16], [4, 34], [27], [1]], ![[0, 28], [16], [17, 3], [27], [1]]]
 h' := ![![[8, 36], [24, 34], [16, 4], [13, 21], [4, 8], [0, 1]], ![[0, 1], [0, 3], [11, 33], [33, 16], [31, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [26, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [33, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![309, 109, 20]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -3, 20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3697, -1516, -349]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-3697, -1516, -349]] 
 ![![37, 0, 0], ![4, 1, 0], ![7, 0, 1]] where
  M :=![![![-3697, -1516, -349], ![-48162, -19751, -4548], ![-209208, -85790, -19751]]]
  hmulB := by decide  
  f := ![![![70919, 1806, -1669]], ![![1442, 37, -34]], ![![20153, 512, -474]]]
  g := ![![![130, -1516, -349], ![1694, -19751, -4548], ![7357, -85790, -19751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-70919, -1806, 1669]] ![![-3697, -1516, -349]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![881, 203, -63]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![881, 203, -63]] 
 ![![41, 0, 0], ![0, 41, 0], ![14, 15, 1]] where
  M :=![![![881, 203, -63], ![-8694, -2017, 609], ![28014, 6440, -2017]]]
  hmulB := by decide  
  f := ![![![-3569, -91, 84]], ![![11592, 295, -273]], ![![2716, 69, -64]]]
  g := ![![![43, 28, -63], ![-420, -272, 609], ![1372, 895, -2017]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [33, 21, 1] where
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
 g := ![![[23, 5], [33], [36], [38, 31], [1]], ![[0, 36], [33], [36], [2, 10], [1]]]
 h' := ![![[20, 40], [27, 13], [3, 22], [17, 6], [8, 20], [0, 1]], ![[0, 1], [0, 28], [33, 19], [14, 35], [39, 21], [20, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [27, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [33, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1643, -176, 483]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-205, -181, 483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3569, 91, -84]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![3569, 91, -84]] 
 ![![41, 0, 0], ![37, 1, 0], ![22, 0, 1]] where
  M :=![![![3569, 91, -84], ![-11592, -295, 273], ![12558, 322, -295]]]
  hmulB := by decide  
  f := ![![![-881, -203, 63]], ![![-583, -134, 42]], ![![-1156, -266, 83]]]
  g := ![![![50, 91, -84], ![-163, -295, 273], ![174, 322, -295]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![881, 203, -63]] ![![3569, 91, -84]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![155, 64, 15]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![155, 64, 15]] 
 ![![43, 0, 0], ![0, 43, 0], ![39, 10, 1]] where
  M :=![![![155, 64, 15], ![2070, 845, 192], ![8832, 3634, 845]]]
  hmulB := by decide  
  f := ![![![-379, -10, 9]], ![![1242, 35, -30]], ![![-87, -2, 2]]]
  g := ![![![-10, -2, 15], ![-126, -25, 192], ![-561, -112, 845]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [27, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 42], [0, 1]]
 g := ![![[30, 40], [24, 21], [11], [8, 6], [1]], ![[9, 3], [42, 22], [11], [7, 37], [1]]]
 h' := ![![[7, 42], [40, 13], [5, 35], [42, 21], [16, 7], [0, 1]], ![[0, 1], [2, 30], [35, 8], [17, 22], [22, 36], [7, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [13, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [27, 36, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1543, -138, 141]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, -36, 141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-379, -10, 9]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-379, -10, 9]] 
 ![![43, 0, 0], ![13, 1, 0], ![1, 0, 1]] where
  M :=![![![-379, -10, 9], ![1242, 35, -30], ![-1380, -46, 35]]]
  hmulB := by decide  
  f := ![![![155, 64, 15]], ![![95, 39, 9]], ![![209, 86, 20]]]
  g := ![![![-6, -10, 9], ![19, 35, -30], ![-19, -46, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![155, 64, 15]] ![![-379, -10, 9]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [31, 0, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 19, 21], [19, 27, 26], [0, 1]]
 g := ![![[17, 29, 36], [32, 9, 25], [26, 23, 2], [34, 9, 1], []], ![[2, 1, 40, 32], [29, 35, 1, 21], [9, 9, 6, 25], [42, 8, 22, 34], [20, 18]], ![[36, 23, 39, 29], [44, 15, 26, 43], [38, 7, 26, 19], [26, 10, 31, 33], [15, 18]]]
 h' := ![![[37, 19, 21], [42, 5, 41], [40, 16, 5], [27, 3, 40], [0, 0, 1], [0, 1]], ![[19, 27, 26], [10, 36, 37], [6, 32, 1], [18, 43, 15], [44, 2, 27], [37, 19, 21]], ![[0, 1], [9, 6, 16], [12, 46, 41], [13, 1, 39], [37, 45, 19], [19, 27, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 34], []]
 b := ![[], [39, 44, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [31, 0, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33464, -52499, -37788]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-712, -1117, -804]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [43, 27, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 4, 42], [2, 48, 11], [0, 1]]
 g := ![![[33, 46, 52], [21, 7], [49, 33, 24], [27, 37], [1]], ![[40, 44, 29, 9], [37, 4], [34, 44, 51, 42], [18, 13], [20, 34, 43, 47]], ![[33, 25, 45, 38], [14, 46], [43, 17, 35, 7], [40, 46], [33, 51, 18, 6]]]
 h' := ![![[12, 4, 42], [8, 52, 23], [13, 15, 31], [52, 2, 17], [10, 26, 14], [0, 1]], ![[2, 48, 11], [45, 11, 2], [24, 18, 51], [50, 26, 52], [20, 44, 15], [12, 4, 42]], ![[0, 1], [43, 43, 28], [3, 20, 24], [5, 25, 37], [20, 36, 24], [2, 48, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 19], []]
 b := ![[], [36, 11, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [43, 27, 39, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14999, -5777, -1060]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-283, -109, -20]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -5, 2]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-25, -5, 2]] 
 ![![59, 0, 0], ![0, 59, 0], ![17, 27, 1]] where
  M :=![![![-25, -5, 2], ![276, 67, -15], ![-690, -138, 67]]]
  hmulB := by decide  
  f := ![![![-41, -1, 1]], ![![138, 5, -3]], ![![49, 2, -1]]]
  g := ![![![-1, -1, 2], ![9, 8, -15], ![-31, -33, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [55, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 58], [0, 1]]
 g := ![![[36, 29], [45, 45], [48], [46, 17], [26, 1]], ![[23, 30], [35, 14], [48], [16, 42], [52, 58]]]
 h' := ![![[26, 58], [3, 18], [5, 35], [7, 44], [45, 31], [0, 1]], ![[0, 1], [58, 41], [30, 24], [30, 15], [25, 28], [26, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [50, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [55, 33, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5333, 2459, 1164]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-245, -491, 1164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -1, 1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-41, -1, 1]] 
 ![![59, 0, 0], ![37, 1, 0], ![55, 0, 1]] where
  M :=![![![-41, -1, 1], ![138, 5, -3], ![-138, 0, 5]]]
  hmulB := by decide  
  f := ![![![-25, -5, 2]], ![![-11, -2, 1]], ![![-35, -7, 3]]]
  g := ![![![-1, -1, 1], ![2, 5, -3], ![-7, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-25, -5, 2]] ![![-41, -1, 1]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 4, -1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![71, 4, -1]] 
 ![![61, 0, 0], ![29, 1, 0], ![45, 0, 1]] where
  M :=![![![71, 4, -1], ![-138, 25, 12], ![552, 138, 25]]]
  hmulB := by decide  
  f := ![![![1031, 238, -73]], ![![325, 75, -23]], ![![1299, 300, -92]]]
  g := ![![![0, 4, -1], ![-23, 25, 12], ![-75, 138, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 311, 72]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![757, 311, 72]] 
 ![![61, 0, 0], ![39, 1, 0], ![42, 0, 1]] where
  M :=![![![757, 311, 72], ![9936, 4069, 933], ![42918, 17618, 4069]]]
  hmulB := by decide  
  f := ![![![119167, 3037, -2805]], ![![69843, 1780, -1644]], ![![88920, 2266, -2093]]]
  g := ![![![-236, 311, 72], ![-3081, 4069, 933], ![-13362, 17618, 4069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2279, -77, 58]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-2279, -77, 58]] 
 ![![61, 0, 0], ![54, 1, 0], ![4, 0, 1]] where
  M :=![![![-2279, -77, 58], ![8004, 389, -231], ![-10626, -874, 389]]]
  hmulB := by decide  
  f := ![![![-50573, -20739, -4775]], ![![-55572, -22789, -5247]], ![![-50234, -20600, -4743]]]
  g := ![![![27, -77, 58], ![-198, 389, -231], ![574, -874, 389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![71, 4, -1]] ![![757, 311, 72]]
  ![![50573, 20739, 4775]] where
 M := ![![![50573, 20739, 4775]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![50573, 20739, 4775]] ![![-2279, -77, 58]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -18, 5]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-49, -18, 5]] 
 ![![67, 0, 0], ![0, 67, 0], ![17, 50, 1]] where
  M :=![![![-49, -18, 5], ![690, 181, -54], ![-2484, -598, 181]]]
  hmulB := by decide  
  f := ![![![-7, -4, -1]], ![![-138, -53, -12]], ![![-113, -44, -10]]]
  g := ![![![-2, -4, 5], ![24, 43, -54], ![-83, -144, 181]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [34, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 66], [0, 1]]
 g := ![![[24, 36], [9, 17], [55], [6], [10], [1]], ![[61, 31], [6, 50], [55], [6], [10], [1]]]
 h' := ![![[55, 66], [29, 61], [55, 33], [7, 16], [12, 26], [33, 55], [0, 1]], ![[0, 1], [34, 6], [61, 34], [16, 51], [35, 41], [43, 12], [55, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [32, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [34, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-805, -200, 63]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -50, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -4, -1]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-7, -4, -1]] 
 ![![67, 0, 0], ![51, 1, 0], ![4, 0, 1]] where
  M :=![![![-7, -4, -1], ![-138, -53, -12], ![-552, -230, -53]]]
  hmulB := by decide  
  f := ![![![-49, -18, 5]], ![![-27, -11, 3]], ![![-40, -10, 3]]]
  g := ![![![3, -4, -1], ![39, -53, -12], ![170, -230, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-49, -18, 5]] ![![-7, -4, -1]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [38, 43, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 26, 40], [69, 44, 31], [0, 1]]
 g := ![![[25, 1, 8], [68, 25, 32], [39, 9, 54], [65, 5], [42, 1], []], ![[29, 4, 37, 16], [57, 22, 67, 3], [33, 23, 63, 60], [26, 8], [4, 19], [55, 38]], ![[21, 45, 2, 67], [20, 51, 9, 28], [53, 70, 19, 42], [64, 49], [61, 37], [64, 38]]]
 h' := ![![[44, 26, 40], [43, 41, 47], [9, 58, 48], [35, 3, 14], [37, 2, 17], [0, 0, 1], [0, 1]], ![[69, 44, 31], [5, 11, 16], [68, 68, 30], [70, 13, 26], [63, 39, 47], [59, 41, 44], [44, 26, 40]], ![[0, 1], [13, 19, 8], [2, 16, 64], [46, 55, 31], [8, 30, 7], [57, 30, 26], [69, 44, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 2], []]
 b := ![[], [28, 55, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [38, 43, 29, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![143420, 70929, 24921]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2020, 999, 351]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84263, -2150, 1984]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-84263, -2150, 1984]] 
 ![![73, 0, 0], ![0, 73, 0], ![4, 48, 1]] where
  M :=![![![-84263, -2150, 1984], ![273792, 7001, -6450], ![-296700, -7636, 7001]]]
  hmulB := by decide  
  f := ![![![-3263, -1338, -308]], ![![-42504, -17431, -4014]], ![![-30656, -12572, -2895]]]
  g := ![![![-1263, -1334, 1984], ![4104, 4337, -6450], ![-4448, -4708, 7001]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [68, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 72], [0, 1]]
 g := ![![[72, 8], [70], [35], [16, 38], [25], [1]], ![[32, 65], [70], [35], [45, 35], [25], [1]]]
 h' := ![![[68, 72], [10, 64], [5, 56], [7, 53], [4, 44], [5, 68], [0, 1]], ![[0, 1], [55, 9], [17, 17], [34, 20], [3, 29], [30, 5], [68, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [8, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [68, 5, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5438, -1746, 502]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -354, 502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3263, -1338, -308]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-3263, -1338, -308]] 
 ![![73, 0, 0], ![2, 1, 0], ![23, 0, 1]] where
  M :=![![![-3263, -1338, -308], ![-42504, -17431, -4014], ![-184644, -75716, -17431]]]
  hmulB := by decide  
  f := ![![![-84263, -2150, 1984]], ![![1442, 37, -34]], ![![-30613, -782, 721]]]
  g := ![![![89, -1338, -308], ![1160, -17431, -4014], ![5037, -75716, -17431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-84263, -2150, 1984]] ![![-3263, -1338, -308]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [23, 77, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 44, 72], [35, 34, 7], [0, 1]]
 g := ![![[13, 50, 20], [2, 66, 50], [26, 56, 18], [32, 24, 5], [52, 1], []], ![[28, 15, 51, 62], [25, 29, 55, 18], [20, 36, 46, 26], [29, 1, 75, 45], [40, 50], [36, 49]], ![[33, 50, 31, 43], [67, 68, 15, 15], [62, 26, 69, 43], [35, 77, 4, 30], [7, 40], [22, 49]]]
 h' := ![![[17, 44, 72], [33, 37, 40], [34, 21, 45], [54, 28, 52], [68, 2, 20], [0, 0, 1], [0, 1]], ![[35, 34, 7], [37, 71, 74], [73, 71, 40], [73, 69, 71], [66, 60, 34], [14, 46, 34], [17, 44, 72]], ![[0, 1], [68, 50, 44], [23, 66, 73], [28, 61, 35], [61, 17, 25], [8, 33, 44], [35, 34, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 34], []]
 b := ![[], [31, 41, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [23, 77, 27, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23542, -6162, 6636]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-298, -78, 84]
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



lemma PB180I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB180I1 : PrimesBelowBoundCertificateInterval O 31 79 180 where
  m := 11
  g := ![2, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB180I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI61N2
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
  β := ![I37N1, I41N1, I43N1, I59N1, I61N0, I61N1, I61N2, I67N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N1], [], [], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
