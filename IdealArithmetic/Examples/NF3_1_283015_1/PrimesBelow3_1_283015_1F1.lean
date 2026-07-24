
import IdealArithmetic.Examples.NF3_1_283015_1.RI3_1_283015_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![16, -3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![16, -3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![16, 34, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![16, -3, 1], ![-99, 7, -27], ![308, 7, 10]]]
  hmulB := by decide  
  f := ![![![-15, 3, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -34, 37]], ![![0, -1, 1], ![9, 25, -27], ![4, -9, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [18, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 36], [0, 1]]
 g := ![![[7, 21], [4], [32, 11], [3], [1]], ![[25, 16], [4], [15, 26], [3], [1]]]
 h' := ![![[22, 36], [36, 24], [16, 35], [11, 14], [19, 22], [0, 1]], ![[0, 1], [9, 13], [9, 2], [23, 23], [22, 15], [22, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [34, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [18, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3535, -3613, -1953]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![749, 1697, -1953]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-10, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-10, 1, 0]] 
 ![![37, 0, 0], ![27, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-10, 1, 0], ![0, -9, 9], ![-99, -6, -10]]]
  hmulB := by decide  
  f := ![![![321, -32, 0], ![1184, 0, 0]], ![![231, -23, 0], ![852, 0, 0]], ![![231, -24, 1], ![852, -4, 0]]]
  g := ![![![1, 0, 0], ![-27, 37, 0], ![-27, 0, 37]], ![![-1, 1, 0], ![0, -9, 9], ![9, -6, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![16, -3, 1]] ![![37, 0, 0], ![-10, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-370, 37, 0]], ![![592, -111, 37], ![-259, 37, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-10, 1, 0]]], ![![![16, -3, 1]], ![![-7, 1, -1]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [10, 26, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40, 34], [13, 0, 7], [0, 1]]
 g := ![![[27, 34, 8], [37, 10], [39, 18], [13, 30, 1], []], ![[8, 27, 32, 29], [1, 25], [18, 9], [22, 35], [8, 8]], ![[38, 23, 7, 35], [1, 31], [14, 8], [1, 39, 7, 7], [35, 8]]]
 h' := ![![[17, 40, 34], [4, 3, 34], [28, 30, 25], [34, 18, 10], [0, 0, 1], [0, 1]], ![[13, 0, 7], [27, 37, 20], [23, 38, 36], [11, 1, 38], [4, 6], [17, 40, 34]], ![[0, 1], [39, 1, 28], [34, 14, 21], [16, 22, 34], [24, 35, 40], [13, 0, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 30], []]
 b := ![[], [32, 19, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [10, 26, 11, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1569562, 173553, 19188]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38282, 4233, 468]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [16, 27, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 21, 7], [5, 21, 36], [0, 1]]
 g := ![![[25, 34, 17], [38, 37, 15], [22, 14], [37, 35, 1], []], ![[5, 32, 18, 30], [41, 16, 37, 3], [35, 24], [35, 17, 35, 34], [31, 6]], ![[20, 3, 8, 25], [12, 5, 22, 1], [27, 16], [3, 18, 20, 9], [2, 6]]]
 h' := ![![[30, 21, 7], [37, 9, 19], [6, 37, 12], [10, 32, 33], [0, 0, 1], [0, 1]], ![[5, 21, 36], [28, 38, 32], [30, 14, 38], [26, 25, 14], [17, 26, 21], [30, 21, 7]], ![[0, 1], [35, 39, 35], [21, 35, 36], [25, 29, 39], [36, 17, 21], [5, 21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 35], []]
 b := ![[], [0, 0, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [16, 27, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234135, 1892, -10234]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5445, 44, -238]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![10, 13, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![10, 13, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![10, 13, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![10, 13, 1], ![-99, 17, 117], ![-1276, -89, 4]]]
  hmulB := by decide  
  f := ![![![-9, -13, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -13, 47]], ![![0, 0, 1], ![-27, -32, 117], ![-28, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [30, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 46], [0, 1]]
 g := ![![[4, 34], [10, 27], [27, 24], [11, 18], [1]], ![[13, 13], [13, 20], [14, 23], [13, 29], [1]]]
 h' := ![![[21, 46], [29, 38], [36, 36], [46, 27], [17, 21], [0, 1]], ![[0, 1], [28, 9], [40, 11], [2, 20], [35, 26], [21, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [15, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [30, 26, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3496, -4479, -2662]
  a := ![1, -2, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![492, 641, -2662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-23, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-23, 1, 0]] 
 ![![47, 0, 0], ![24, 1, 0], ![43, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-23, 1, 0], ![0, -22, 9], ![-99, -6, -23]]]
  hmulB := by decide  
  f := ![![![24, 659, -270], ![47, 1410, 0]], ![![24, 329, -135], ![48, 705, 0]], ![![20, 603, -247], ![39, 1290, 0]]]
  g := ![![![1, 0, 0], ![-24, 47, 0], ![-43, 0, 47]], ![![-1, 1, 0], ![3, -22, 9], ![22, -6, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![10, 13, 1]] ![![47, 0, 0], ![-23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-1081, 47, 0]], ![![470, 611, 47], ![-329, -282, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-23, 1, 0]]], ![![![10, 13, 1]], ![![-7, -6, 2]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203585, 12966, -15491]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-203585, 12966, -15491]] 
 ![![53, 0, 0], ![0, 53, 0], ![22, 26, 1]] where
  M :=![![![-203585, 12966, -15491], ![1533609, -97673, 116694], ![-1454035, 92605, -110639]]]
  hmulB := by decide  
  f := ![![![91, -23, -37]], ![![3663, 290, -207]], ![![1870, 143, -111]]]
  g := ![![![2589, 7844, -15491], ![-19503, -59089, 116694], ![18491, 56023, -110639]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [28, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 52], [0, 1]]
 g := ![![[8, 36], [1], [2, 11], [47], [41, 1]], ![[0, 17], [1], [29, 42], [47], [29, 52]]]
 h' := ![![[41, 52], [34, 47], [50, 52], [15, 8], [18, 10], [0, 1]], ![[0, 1], [0, 6], [9, 1], [25, 45], [4, 43], [41, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [46, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [28, 12, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3525, -3607, -1902]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![723, 865, -1902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, -23, -37]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![91, -23, -37]] 
 ![![53, 0, 0], ![31, 1, 0], ![37, 0, 1]] where
  M :=![![![91, -23, -37], ![3663, 290, -207], ![1870, 545, 313]]]
  hmulB := by decide  
  f := ![![![-203585, 12966, -15491]], ![![-90142, 5741, -6859]], ![![-169560, 10799, -12902]]]
  g := ![![![41, -23, -37], ![44, 290, -207], ![-502, 545, 313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-203585, 12966, -15491]] ![![91, -23, -37]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-20, -26, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-20, -26, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![39, 33, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-20, -26, 1], ![-99, -52, -234], ![2585, 145, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -33, 59]], ![![-1, -1, 1], ![153, 130, -234], ![61, 17, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [58, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 58], [0, 1]]
 g := ![![[53, 5], [28, 48], [53], [15, 12], [53, 1]], ![[23, 54], [35, 11], [53], [2, 47], [47, 58]]]
 h' := ![![[53, 58], [28, 51], [42, 15], [15, 17], [53, 37], [0, 1]], ![[0, 1], [17, 8], [11, 44], [31, 42], [8, 22], [53, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [50, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [58, 6, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-352364, -323211, -150638]
  a := ![1, 20, 161]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![93602, 78777, -150638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-2, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-2, 1, 0]] 
 ![![59, 0, 0], ![57, 1, 0], ![26, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-2, 1, 0], ![0, -1, 9], ![-99, -6, -2]]]
  hmulB := by decide  
  f := ![![![3, 28, -261], ![59, 1711, 0]], ![![1, 28, -252], ![1, 1652, 0]], ![![2, 12, -115], ![46, 754, 0]]]
  g := ![![![1, 0, 0], ![-57, 59, 0], ![-26, 0, 59]], ![![-1, 1, 0], ![-3, -1, 9], ![5, -6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-20, -26, 1]] ![![59, 0, 0], ![-2, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-118, 59, 0]], ![![-1180, -1534, 59], ![-59, 0, -236]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-2, 1, 0]]], ![![![-20, -26, 1]], ![![-1, 0, -4]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [20, 46, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 22, 25], [35, 38, 36], [0, 1]]
 g := ![![[23, 10, 9], [16, 22], [6, 57, 42], [36, 7, 4], [1]], ![[16, 55, 42, 45], [37, 39], [29, 40, 1, 41], [2, 32, 47, 4], [14, 0, 32, 9]], ![[37, 16, 10, 13], [5, 57], [1, 29, 52, 34], [16, 57, 58, 58], [25, 41, 45, 52]]]
 h' := ![![[28, 22, 25], [50, 19, 3], [2, 9, 12], [12, 7, 46], [41, 15, 2], [0, 1]], ![[35, 38, 36], [38, 18, 40], [30, 1, 10], [0, 19, 32], [17, 43, 24], [28, 22, 25]], ![[0, 1], [19, 24, 18], [34, 51, 39], [16, 35, 44], [41, 3, 35], [35, 38, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 6], []]
 b := ![[], [52, 49, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [20, 46, 59, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4053389, 316102, -59292]
  a := ![-1, 2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66449, 5182, -972]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [55, 18, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 5, 64], [46, 61, 3], [0, 1]]
 g := ![![[43, 46, 22], [4, 51, 40], [21, 49], [15, 10], [26, 1], []], ![[48, 26, 8, 47], [62, 37, 7, 39], [51, 64], [32, 17], [8, 36], [3, 9]], ![[5, 28, 44, 8], [43, 49, 44, 38], [62, 1], [20, 39], [33, 25], [64, 9]]]
 h' := ![![[47, 5, 64], [48, 27, 25], [31, 22, 43], [39, 56, 60], [44, 13, 55], [0, 0, 1], [0, 1]], ![[46, 61, 3], [23, 36, 37], [48, 63, 11], [21, 29, 8], [46, 8, 33], [34, 55, 61], [47, 5, 64]], ![[0, 1], [25, 4, 5], [33, 49, 13], [48, 49, 66], [3, 46, 46], [3, 12, 5], [46, 61, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 39], []]
 b := ![[], [18, 62, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [55, 18, 41, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21241814, 2121086, 23584]
  a := ![0, 3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![317042, 31658, 352]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8816134, -561485, 670829]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![8816134, -561485, 670829]] 
 ![![71, 0, 0], ![0, 71, 0], ![47, 33, 1]] where
  M :=![![![8816134, -561485, 670829], ![-66412071, 4229675, -5053365], ![62966134, -4010209, 4791160]]]
  hmulB := by decide  
  f := ![![![-1835, -291, -50]], ![![4950, -1826, -2619]], ![![1484, -1009, -1272]]]
  g := ![![![-319899, -319702, 670829], ![2409804, 2408320, -5053365], ![-2284766, -2283359, 4791160]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [33, 22, 1] where
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
 g := ![![[48, 3], [14, 10], [62, 8], [20], [58], [1]], ![[53, 68], [7, 61], [28, 63], [20], [58], [1]]]
 h' := ![![[49, 70], [35, 28], [13, 9], [69, 47], [27, 34], [38, 49], [0, 1]], ![[0, 1], [58, 43], [28, 62], [29, 24], [60, 37], [25, 22], [49, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [31, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [33, 22, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55843, -48380, -24100]
  a := ![2, -8, -62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15167, 10520, -24100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1835, -291, -50]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1835, -291, -50]] 
 ![![71, 0, 0], ![58, 1, 0], ![30, 0, 1]] where
  M :=![![![-1835, -291, -50], ![4950, -1826, -2619], ![28259, 2296, -1535]]]
  hmulB := by decide  
  f := ![![![8816134, -561485, 670829]], ![![6266531, -399105, 476827]], ![![4611974, -293729, 350930]]]
  g := ![![![233, -291, -50], ![2668, -1826, -2619], ![-829, 2296, -1535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![8816134, -561485, 670829]] ![![-1835, -291, -50]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [30, 1, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 59, 54], [57, 13, 19], [0, 1]]
 g := ![![[1, 41, 1], [61, 25], [7, 19], [8, 44, 4], [27, 1], []], ![[47, 69, 61, 4], [17, 65], [7, 69], [21, 71, 41, 12], [30, 23], [59, 69]], ![[33, 44, 13, 54], [11, 69], [3, 49], [72, 14, 60, 32], [6, 50], [21, 69]]]
 h' := ![![[43, 59, 54], [66, 66, 72], [12, 70, 5], [52, 35, 47], [66, 16, 71], [0, 0, 1], [0, 1]], ![[57, 13, 19], [51, 0, 47], [59, 21, 49], [14, 28, 19], [12, 18, 35], [6, 25, 13], [43, 59, 54]], ![[0, 1], [41, 7, 27], [15, 55, 19], [18, 10, 7], [47, 39, 40], [64, 48, 59], [57, 13, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 27], []]
 b := ![[], [71, 59, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [30, 1, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11972, -803, 1241]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![164, -11, 17]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [70, 43, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 8, 18], [20, 70, 61], [0, 1]]
 g := ![![[61, 66, 42], [49, 12, 1], [76, 62, 23], [31, 17, 23], [16, 1], []], ![[42, 15, 6, 5], [78, 40, 48, 31], [75, 48, 55, 55], [4, 29, 1, 72], [26, 2], [21, 8]], ![[53, 37, 55, 78], [43, 40, 31, 70], [39, 14, 21, 30], [76, 43, 39, 57], [18, 64], [57, 8]]]
 h' := ![![[75, 8, 18], [46, 73, 11], [52, 2, 78], [42, 43, 24], [65, 32, 55], [0, 0, 1], [0, 1]], ![[20, 70, 61], [34, 61, 30], [76, 42, 45], [50, 36, 5], [73, 11, 2], [47, 53, 70], [75, 8, 18]], ![[0, 1], [15, 24, 38], [48, 35, 35], [62, 0, 50], [44, 36, 22], [44, 26, 8], [20, 70, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 21], []]
 b := ![[], [46, 1, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [70, 43, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86830875, -11057788, -1235955]
  a := ![1, -5, -41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1099125, -139972, -15645]
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



lemma PB151I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB151I1 : PrimesBelowBoundCertificateInterval O 31 79 151 where
  m := 11
  g := ![2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB151I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
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
  β := ![I37N1, I47N1, I53N1, I59N1, I71N1]
  Il := ![[I37N1], [], [], [I47N1], [I53N1], [I59N1], [], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
