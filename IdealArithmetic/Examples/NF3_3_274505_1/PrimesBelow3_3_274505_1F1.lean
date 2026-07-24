
import IdealArithmetic.Examples.NF3_3_274505_1.RI3_3_274505_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![541, 79, -16]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![541, 79, -16]] 
 ![![37, 0, 0], ![0, 37, 0], ![24, 2, 1]] where
  M :=![![![541, 79, -16], ![-1744, -355, 63], ![6867, 1784, -292]]]
  hmulB := by decide  
  f := ![![![236, 148, 19]], ![![2071, 1300, 167]], ![![757, 475, 61]]]
  g := ![![![25, 3, -16], ![-88, -13, 63], ![375, 64, -292]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [34, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[3, 12], [11], [18, 36], [7], [1]], ![[0, 25], [11], [9, 1], [7], [1]]]
 h' := ![![[9, 36], [26, 30], [17, 23], [30, 6], [3, 9], [0, 1]], ![[0, 1], [0, 7], [2, 14], [10, 31], [10, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [18, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [34, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![361, 249, 32]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, 5, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![236, 148, 19]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![236, 148, 19]] 
 ![![37, 0, 0], ![34, 1, 0], ![28, 0, 1]] where
  M :=![![![236, 148, 19], ![2071, 1300, 167], ![18203, 11423, 1467]]]
  hmulB := by decide  
  f := ![![![541, 79, -16]], ![![450, 63, -13]], ![![595, 108, -20]]]
  g := ![![![-144, 148, 19], ![-1265, 1300, 167], ![-11115, 11423, 1467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![541, 79, -16]] ![![236, 148, 19]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 31, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 8], [3, 40, 33], [0, 1]]
 g := ![![[36, 0, 18], [8, 25], [28, 40], [5, 6, 1], []], ![[26, 19, 28, 5], [18, 21], [30, 9], [19, 9, 9, 8], [15, 23]], ![[9, 34, 6, 40], [28, 8], [27, 36], [16, 5], [31, 23]]]
 h' := ![![[3, 0, 8], [38, 11, 10], [25, 35, 5], [38, 30, 32], [0, 0, 1], [0, 1]], ![[3, 40, 33], [30, 9, 37], [7, 25, 29], [5, 37, 3], [0, 5, 40], [3, 0, 8]], ![[0, 1], [16, 21, 35], [0, 22, 7], [34, 15, 6], [15, 36], [3, 40, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 26], []]
 b := ![[], [20, 19, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 31, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![310452, 356741, 101229]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7572, 8701, 2469]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [2, 27, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 27, 8], [23, 15, 35], [0, 1]]
 g := ![![[13, 29, 11], [18, 23, 38], [18, 16], [25, 40, 1], []], ![[36, 28, 7, 3], [24, 37], [26, 9], [3, 32, 24, 37], [25, 21]], ![[30, 27, 34, 9], [6, 32, 32, 40], [3, 1], [0, 32, 23, 16], [41, 21]]]
 h' := ![![[17, 27, 8], [7, 24, 21], [13, 33, 34], [36, 19, 4], [0, 0, 1], [0, 1]], ![[23, 15, 35], [16, 10, 34], [14, 28], [25, 27, 40], [24, 29, 15], [17, 27, 8]], ![[0, 1], [13, 9, 31], [17, 25, 9], [25, 40, 42], [17, 14, 27], [23, 15, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 28], []]
 b := ![[], [24, 29, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [2, 27, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236758, -7267, -25542]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5506, -169, -594]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [42, 33, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 0, 17], [14, 46, 30], [0, 1]]
 g := ![![[43, 11, 25], [28, 30, 32], [43, 15, 9], [3, 41, 1], []], ![[21, 25, 32, 9], [11, 33, 23, 28], [7, 20, 46, 27], [45, 34, 41, 17], [5, 7]], ![[37, 19, 10, 41], [38, 8, 29, 43], [33, 39, 9, 19], [18, 11], [39, 7]]]
 h' := ![![[27, 0, 17], [46, 2, 5], [27, 9, 28], [15, 12, 44], [0, 0, 1], [0, 1]], ![[14, 46, 30], [16, 8, 29], [44, 26, 31], [4, 14, 19], [2, 11, 46], [27, 0, 17]], ![[0, 1], [8, 37, 13], [9, 12, 35], [44, 21, 31], [15, 36], [14, 46, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 7], []]
 b := ![[], [44, 8, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [42, 33, 6, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-483442, -405328, -85211]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10286, -8624, -1813]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 61, -9]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![181, 61, -9]] 
 ![![53, 0, 0], ![0, 53, 0], ![27, 5, 1]] where
  M :=![![![181, 61, -9], ![-981, -323, 52], ![5668, 1931, -271]]]
  hmulB := by decide  
  f := ![![![-243, -16, 5]], ![![545, 37, -11]], ![![-95, -6, 2]]]
  g := ![![![8, 2, -9], ![-45, -11, 52], ![245, 62, -271]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [38, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 52], [0, 1]]
 g := ![![[27, 7], [15], [9, 37], [25], [34, 1]], ![[0, 46], [15], [48, 16], [25], [15, 52]]]
 h' := ![![[34, 52], [6, 31], [29, 42], [33, 14], [33, 5], [0, 1]], ![[0, 1], [0, 22], [26, 11], [32, 39], [44, 48], [34, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [24, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [38, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![365, 258, 41]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 1, 41]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-243, -16, 5]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-243, -16, 5]] 
 ![![53, 0, 0], ![47, 1, 0], ![17, 0, 1]] where
  M :=![![![-243, -16, 5], ![545, 37, -11], ![-1199, -71, 26]]]
  hmulB := by decide  
  f := ![![![181, 61, -9]], ![![142, 48, -7]], ![![165, 56, -8]]]
  g := ![![![8, -16, 5], ![-19, 37, -11], ![32, -71, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![181, 61, -9]] ![![-243, -16, 5]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -26, -3]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-44, -26, -3]] 
 ![![59, 0, 0], ![0, 59, 0], ![54, 48, 1]] where
  M :=![![![-44, -26, -3], ![-327, -212, -29], ![-3161, -1951, -241]]]
  hmulB := by decide  
  f := ![![![-93, -7, 2]], ![![218, 19, -5]], ![![83, 8, -2]]]
  g := ![![![2, 2, -3], ![21, 20, -29], ![167, 163, -241]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [53, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 58], [0, 1]]
 g := ![![[57, 49], [45, 48], [17], [37, 21], [47, 1]], ![[0, 10], [0, 11], [17], [21, 38], [35, 58]]]
 h' := ![![[47, 58], [34, 52], [3, 15], [45, 28], [46, 32], [0, 1]], ![[0, 1], [0, 7], [0, 44], [4, 31], [16, 27], [47, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [21, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [53, 12, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4317, 2559, 470]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-357, -339, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93, 7, -2]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![93, 7, -2]] 
 ![![59, 0, 0], ![10, 1, 0], ![18, 0, 1]] where
  M :=![![![93, 7, -2], ![-218, -19, 5], ![545, 62, -14]]]
  hmulB := by decide  
  f := ![![![44, 26, 3]], ![![13, 8, 1]], ![![67, 41, 5]]]
  g := ![![![1, 7, -2], ![-2, -19, 5], ![3, 62, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-44, -26, -3]] ![![93, 7, -2]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [2, 4, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 4, 48], [27, 56, 13], [0, 1]]
 g := ![![[9, 12, 22], [36, 3], [9, 26, 60], [18, 47, 20], [1]], ![[20, 19, 57, 41], [59, 47], [35, 46, 44, 16], [52, 30, 36, 34], [48, 7, 6, 60]], ![[2, 17, 42, 27], [26, 25], [22, 12, 28, 42], [28, 15, 48, 34], [42, 39, 36, 1]]]
 h' := ![![[43, 4, 48], [8, 38, 12], [43, 49, 53], [25, 21, 11], [59, 57, 9], [0, 1]], ![[27, 56, 13], [9, 40, 56], [26, 47, 13], [36, 22, 38], [50, 22, 7], [43, 4, 48]], ![[0, 1], [5, 44, 54], [39, 26, 56], [30, 18, 12], [18, 43, 45], [27, 56, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 53], []]
 b := ![[], [13, 24, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [2, 4, 52, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5063, -549, 0]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![83, -9, 0]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [61, 63, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 66, 13], [47, 0, 54], [0, 1]]
 g := ![![[30, 34, 10], [65, 47, 23], [41, 10], [43, 33], [26, 1], []], ![[7, 1, 57, 66], [28, 13, 61, 8], [63, 49], [62, 60], [], [13, 35]], ![[28, 29, 63, 9], [38, 55, 25, 17], [7, 26], [15, 17], [31, 1], [39, 35]]]
 h' := ![![[46, 66, 13], [55, 15, 55], [3, 64, 36], [5, 51, 55], [22, 43, 10], [0, 0, 1], [0, 1]], ![[47, 0, 54], [11, 22, 61], [57, 26, 28], [9, 53, 60], [21, 49, 23], [50, 36], [46, 66, 13]], ![[0, 1], [53, 30, 18], [40, 44, 3], [20, 30, 19], [8, 42, 34], [31, 31, 66], [47, 0, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 17], []]
 b := ![[], [37, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [61, 63, 41, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304716, 226125, 40870]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4548, 3375, 610]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 4, -1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![14, 4, -1]] 
 ![![71, 0, 0], ![33, 1, 0], ![47, 0, 1]] where
  M :=![![![14, 4, -1], ![-109, -42, 3], ![327, 59, -39]]]
  hmulB := by decide  
  f := ![![![1461, 97, -30]], ![![633, 42, -13]], ![![1070, 71, -22]]]
  g := ![![![-1, 4, -1], ![16, -42, 3], ![3, 59, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7419, -4656, -598]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-7419, -4656, -598]] 
 ![![71, 0, 0], ![52, 1, 0], ![65, 0, 1]] where
  M :=![![![-7419, -4656, -598], ![-65182, -40907, -5254], ![-572686, -359406, -46161]]]
  hmulB := by decide  
  f := ![![![-11097, -828, 238]], ![![-7762, -575, 166]], ![![-11065, -858, 241]]]
  g := ![![![3853, -4656, -598], ![33852, -40907, -5254], ![297421, -359406, -46161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, 47, 6]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![75, 47, 6]] 
 ![![71, 0, 0], ![56, 1, 0], ![59, 0, 1]] where
  M :=![![![75, 47, 6], ![654, 411, 53], ![5777, 3622, 464]]]
  hmulB := by decide  
  f := ![![![-1262, -76, 25]], ![![-957, -58, 19]], ![![-1127, -65, 22]]]
  g := ![![![-41, 47, 6], ![-359, 411, 53], ![-3161, 3622, 464]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![14, 4, -1]] ![![-7419, -4656, -598]]
  ![![208092, 130594, 16773]] where
 M := ![![![208092, 130594, 16773]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![208092, 130594, 16773]] ![![75, 47, 6]]
  ![![71, 0, 0]] where
 M := ![![![197912997, 124206264, 15952706]]]
 hmul := by decide  
 g := ![![![![2787507, 1749384, 224686]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 2, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![5, 2, 0]] 
 ![![73, 0, 0], ![39, 1, 0], ![12, 0, 1]] where
  M :=![![![5, 2, 0], ![0, 5, 2], ![218, 112, 7]]]
  hmulB := by decide  
  f := ![![![189, 14, -4]], ![![95, 7, -2]], ![![46, 4, -1]]]
  g := ![![![-1, 2, 0], ![-3, 5, 2], ![-58, 112, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 8, 1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![14, 8, 1]] 
 ![![73, 0, 0], ![45, 1, 0], ![19, 0, 1]] where
  M :=![![![14, 8, 1], ![109, 70, 9], ![981, 613, 79]]]
  hmulB := by decide  
  f := ![![![13, -19, 2]], ![![11, -10, 1]], ![![-22, -15, 2]]]
  g := ![![![-5, 8, 1], ![-44, 70, 9], ![-385, 613, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, -15, 4]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-177, -15, 4]] 
 ![![73, 0, 0], ![61, 1, 0], ![2, 0, 1]] where
  M :=![![![-177, -15, 4], ![436, 47, -11], ![-1199, -180, 36]]]
  hmulB := by decide  
  f := ![![![-288, -180, -23]], ![![-275, -172, -22]], ![![-311, -195, -25]]]
  g := ![![![10, -15, 4], ![-33, 47, -11], ![133, -180, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![5, 2, 0]] ![![14, 8, 1]]
  ![![288, 180, 23]] where
 M := ![![![288, 180, 23]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![288, 180, 23]] ![![-177, -15, 4]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11361, 754, -233]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![11361, 754, -233]] 
 ![![79, 0, 0], ![0, 79, 0], ![16, 70, 1]] where
  M :=![![![11361, 754, -233], ![-25397, -1687, 521], ![56789, 3779, -1166]]]
  hmulB := by decide  
  f := ![![![-23, -17, -3]], ![![-327, -191, -20]], ![![-322, -191, -21]]]
  g := ![![![191, 216, -233], ![-427, -483, 521], ![955, 1081, -1166]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [1, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 78], [0, 1]]
 g := ![![[67, 1], [12, 8], [24, 62], [54, 50], [65], [1]], ![[0, 78], [29, 71], [57, 17], [22, 29], [65], [1]]]
 h' := ![![[12, 78], [67, 1], [55, 61], [25, 33], [15, 45], [78, 12], [0, 1]], ![[0, 1], [0, 78], [76, 18], [26, 46], [2, 34], [64, 67], [12, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [52, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [1, 67, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3785, -2290, 430]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-135, -410, 430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 17, 3]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![23, 17, 3]] 
 ![![79, 0, 0], ![8, 1, 0], ![15, 0, 1]] where
  M :=![![![23, 17, 3], ![327, 191, 20], ![2180, 1447, 211]]]
  hmulB := by decide  
  f := ![![![-11361, -754, 233]], ![![-829, -55, 17]], ![![-2876, -191, 59]]]
  g := ![![![-2, 17, 3], ![-19, 191, 20], ![-159, 1447, 211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![11361, 754, -233]] ![![23, 17, 3]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB117I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB117I1 : PrimesBelowBoundCertificateInterval O 31 79 117 where
  m := 11
  g := ![2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB117I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I53N1, I59N1, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [], [], [], [I53N1], [I59N1], [], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
