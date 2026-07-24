
import IdealArithmetic.Examples.NF3_3_567849_1.RI3_3_567849_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 4, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 2, 10], [13, 34, 27], [0, 1]]
 g := ![![[30, 31, 36], [34, 34], [32, 22, 27], [12, 1], []], ![[14, 3, 27, 25], [25, 9], [0, 36], [16, 9], [19, 26]], ![[23, 19, 33, 28], [1, 21], [0, 6, 12, 26], [36, 4], [2, 26]]]
 h' := ![![[36, 2, 10], [25, 18, 31], [31, 14, 21], [7, 5, 29], [0, 0, 1], [0, 1]], ![[13, 34, 27], [27, 18, 13], [21, 17, 3], [4, 23], [9, 3, 34], [36, 2, 10]], ![[0, 1], [15, 1, 30], [31, 6, 13], [18, 9, 8], [16, 34, 2], [13, 34, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 35], []]
 b := ![[], [4, 7, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 4, 25, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19277, 30784, -47582]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![521, 832, -1286]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [21, 14, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 24, 36], [21, 16, 5], [0, 1]]
 g := ![![[32, 36, 10], [30, 20], [36, 25], [11, 5, 1], []], ![[31, 32, 39, 32], [2, 23], [7, 33], [23, 15, 28, 32], [8, 25]], ![[40, 2], [2, 8], [17, 32], [31, 28, 16, 10], [39, 25]]]
 h' := ![![[25, 24, 36], [30, 3, 25], [2, 16, 26], [15, 28, 5], [0, 0, 1], [0, 1]], ![[21, 16, 5], [9, 2, 16], [25, 16, 8], [7, 2, 22], [6, 30, 16], [25, 24, 36]], ![[0, 1], [32, 36], [22, 9, 7], [25, 11, 14], [32, 11, 24], [21, 16, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 40], []]
 b := ![[], [27, 6, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [21, 14, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![343170, -261867, 165312]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8370, -6387, 4032]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-689, 226, 52]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-689, 226, 52]] 
 ![![43, 0, 0], ![0, 43, 0], ![19, 6, 1]] where
  M :=![![![-689, 226, 52], ![-6032, 1981, 452], ![-23200, 7606, 1755]]]
  hmulB := by decide  
  f := ![![![901, -26, -20]], ![![2320, -65, -52]], ![![765, -22, -17]]]
  g := ![![![-39, -2, 52], ![-340, -17, 452], ![-1315, -68, 1755]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [42, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 42], [0, 1]]
 g := ![![[16, 1], [0, 41], [1], [0, 41], [1]], ![[32, 42], [11, 2], [1], [11, 2], [1]]]
 h' := ![![[16, 42], [0, 42], [1, 16], [0, 42], [1, 16], [0, 1]], ![[0, 1], [27, 1], [42, 27], [27, 1], [42, 27], [16, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [8, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [42, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2468, -58, 148]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -22, 148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-901, 26, 20]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-901, 26, 20]] 
 ![![43, 0, 0], ![31, 1, 0], ![20, 0, 1]] where
  M :=![![![-901, 26, 20], ![-2320, 65, 52], ![-1856, 62, 39]]]
  hmulB := by decide  
  f := ![![![689, -226, -52]], ![![637, -209, -48]], ![![860, -282, -65]]]
  g := ![![![-49, 26, 20], ![-125, 65, 52], ![-106, 62, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-689, 226, 52]] ![![-901, 26, 20]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [46, 8, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 39, 39], [38, 7, 8], [0, 1]]
 g := ![![[10, 9, 36], [43, 46, 7], [7, 10, 8], [40, 1, 1], []], ![[25, 43, 29, 11], [28, 35, 39, 15], [8, 7, 41, 46], [34, 43, 16, 31], [4, 17]], ![[6, 28, 28, 21], [21, 15, 23, 21], [31, 17, 12, 34], [3, 12, 39, 42], [35, 17]]]
 h' := ![![[10, 39, 39], [43, 33, 6], [7, 3, 30], [40, 10, 33], [0, 0, 1], [0, 1]], ![[38, 7, 8], [10, 2, 13], [8, 37, 45], [0, 20, 10], [10, 13, 7], [10, 39, 39]], ![[0, 1], [19, 12, 28], [29, 7, 19], [18, 17, 4], [22, 34, 39], [38, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 3], []]
 b := ![[], [15, 45, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [46, 8, 46, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-404623, 328530, -214179]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8609, 6990, -4557]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 47, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 51, 30], [20, 1, 23], [0, 1]]
 g := ![![[41, 10, 16], [28, 1], [34, 21, 6], [15, 43], [1]], ![[18, 19, 34, 26], [52, 24], [7, 21, 47, 14], [32, 4], [25, 6, 46, 23]], ![[30, 45, 37, 14], [1, 6], [1, 0, 30, 5], [12, 24], [49, 52, 10, 30]]]
 h' := ![![[14, 51, 30], [45, 26, 4], [31, 3, 52], [3, 17, 18], [43, 6, 34], [0, 1]], ![[20, 1, 23], [39, 43, 42], [33, 10, 36], [7, 49, 51], [3, 27, 2], [14, 51, 30]], ![[0, 1], [42, 37, 7], [23, 40, 18], [30, 40, 37], [37, 20, 17], [20, 1, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 24], []]
 b := ![[], [38, 22, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 47, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24486, 30422, -50297]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![462, 574, -949]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11255837, -5151478, 999656]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![11255837, -5151478, 999656]] 
 ![![59, 0, 0], ![0, 59, 0], ![9, 46, 1]] where
  M :=![![![11255837, -5151478, 999656], ![-115960096, 53088191, -10302956], ![655551496, -300099514, 58239669]]]
  hmulB := by decide  
  f := ![![![1244351095, -408369722, -93601808]], ![![10857809728, -3563303603, -816739444]], ![![9366108309, -3073758734, -704531603]]]
  g := ![![![38287, -866706, 999656], ![-393788, 8932613, -10302956], ![2227025, -50493632, 58239669]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [20, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[51, 3], [29, 26], [46], [33, 27], [42, 1]], ![[0, 56], [0, 33], [46], [46, 32], [25, 58]]]
 h' := ![![[42, 58], [10, 11], [27, 12], [48, 39], [45, 33], [0, 1]], ![[0, 1], [0, 48], [0, 47], [34, 20], [15, 26], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [5, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [20, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71824, 14682, 21926]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4562, -16846, 21926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1244351095, -408369722, -93601808]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1244351095, -408369722, -93601808]] 
 ![![59, 0, 0], ![26, 1, 0], ![3, 0, 1]] where
  M :=![![![1244351095, -408369722, -93601808], ![10857809728, -3563303603, -816739444], ![41941982888, -13764472070, -3154933881]]]
  hmulB := by decide  
  f := ![![![11255837, -5151478, 999656]], ![![2994774, -1370343, 265900]], ![![11683373, -5348372, 1037943]]]
  g := ![![![205809649, -408369722, -93601808], ![1795829182, -3563303603, -816739444], ![6937000989, -13764472070, -3154933881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![11255837, -5151478, 999656]] ![![1244351095, -408369722, -93601808]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, -166, -38]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![503, -166, -38]] 
 ![![61, 0, 0], ![37, 1, 0], ![29, 0, 1]] where
  M :=![![![503, -166, -38], ![4408, -1449, -332], ![17052, -5598, -1283]]]
  hmulB := by decide  
  f := ![![![531, -254, 50]], ![![227, -111, 22]], ![![783, -364, 71]]]
  g := ![![![127, -166, -38], ![1109, -1449, -332], ![4285, -5598, -1283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55301, 25312, -4912]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-55301, 25312, -4912]] 
 ![![61, 0, 0], ![47, 1, 0], ![31, 0, 1]] where
  M :=![![![-55301, 25312, -4912], ![569792, -260853, 50624], ![-3221088, 1474560, -286165]]]
  hmulB := by decide  
  f := ![![![1126695, -369760, -84752]], ![![1029277, -337789, -77424]], ![![1195149, -392224, -89901]]]
  g := ![![![-17913, 25312, -4912], ![184599, -260853, 50624], ![-1043513, 1474560, -286165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![503, -166, -38]] ![![503, -166, -38]]
  ![![-1126695, 369760, 84752]] where
 M := ![![![-1126695, 369760, 84752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-1126695, 369760, 84752]] ![![-55301, 25312, -4912]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6009, 1972, 452]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-6009, 1972, 452]] 
 ![![67, 0, 0], ![9, 1, 0], ![22, 0, 1]] where
  M :=![![![-6009, 1972, 452], ![-52432, 17207, 3944], ![-202536, 66468, 15235]]]
  hmulB := by decide  
  f := ![![![-1147, 116, 4]], ![![-161, 3, 4]], ![![-574, 116, -13]]]
  g := ![![![-503, 1972, 452], ![-4389, 17207, 3944], ![-16954, 66468, 15235]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26977, 774, 600]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-26977, 774, 600]] 
 ![![67, 0, 0], ![25, 1, 0], ![10, 0, 1]] where
  M :=![![![-26977, 774, 600], ![-69600, 1997, 1548], ![-54984, 1578, 1223]]]
  hmulB := by decide  
  f := ![![![413, -198, 48]], ![![71, -37, 12]], ![![446, -210, 47]]]
  g := ![![![-781, 774, 600], ![-2015, 1997, 1548], ![-1592, 1578, 1223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15173, 6946, -1348]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-15173, 6946, -1348]] 
 ![![67, 0, 0], ![32, 1, 0], ![8, 0, 1]] where
  M :=![![![-15173, 6946, -1348], ![156368, -71583, 13892], ![-883920, 404646, -78529]]]
  hmulB := by decide  
  f := ![![![825, 374, 52]], ![![304, 233, 36]], ![![-504, 262, 55]]]
  g := ![![![-3383, 6946, -1348], ![34864, -71583, 13892], ![-197080, 404646, -78529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-6009, 1972, 452]] ![![-26977, 774, 600]]
  ![![825, 374, 52]] where
 M := ![![![825, 374, 52]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![825, 374, 52]] ![![-15173, 6946, -1348]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98551, 2912, 2170]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-98551, 2912, 2170]] 
 ![![71, 0, 0], ![0, 71, 0], ![23, 16, 1]] where
  M :=![![![-98551, 2912, 2170], ![-251720, 6351, 5824], ![-211932, 11004, 3439]]]
  hmulB := by decide  
  f := ![![![-595017, 195272, 44758]], ![![-5191928, 1703881, 390544]], ![![-1645237, 539932, 123757]]]
  g := ![![![-2091, -448, 2170], ![-5432, -1223, 5824], ![-4099, -620, 3439]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [28, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 70], [0, 1]]
 g := ![![[42, 8], [27, 8], [41, 12], [29], [38], [1]], ![[6, 63], [62, 63], [58, 59], [29], [38], [1]]]
 h' := ![![[31, 70], [25, 47], [59, 24], [56, 56], [4, 10], [43, 31], [0, 1]], ![[0, 1], [62, 24], [22, 47], [17, 15], [30, 61], [10, 40], [31, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [37, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [28, 40, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-417, 210, 93]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -18, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![595017, -195272, -44758]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![595017, -195272, -44758]] 
 ![![71, 0, 0], ![39, 1, 0], ![1, 0, 1]] where
  M :=![![![595017, -195272, -44758], ![5191928, -1703881, -390544], ![20055588, -6581820, -1508609]]]
  hmulB := by decide  
  f := ![![![98551, -2912, -2170]], ![![57679, -1689, -1274]], ![![4373, -196, -79]]]
  g := ![![![116273, -195272, -44758], ![1014561, -1703881, -390544], ![3919087, -6581820, -1508609]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-98551, 2912, 2170]] ![![595017, -195272, -44758]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [20, 16, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 46, 68], [56, 26, 5], [0, 1]]
 g := ![![[12, 63, 64], [20, 1], [29, 16], [22, 33, 2], [35, 1], []], ![[39, 43, 49, 51], [38, 72], [7, 49], [19, 39, 7, 40], [63, 19], [50, 25]], ![[72, 56, 63, 13], [10, 54], [36, 48], [28, 31, 60, 28], [53, 72], [40, 25]]]
 h' := ![![[52, 46, 68], [29, 51, 8], [8, 29, 1], [71, 34, 4], [30, 4, 41], [0, 0, 1], [0, 1]], ![[56, 26, 5], [34, 69, 26], [8, 0, 27], [41, 24, 7], [22, 21, 24], [25, 53, 26], [52, 46, 68]], ![[0, 1], [38, 26, 39], [26, 44, 45], [4, 15, 62], [35, 48, 8], [0, 20, 46], [56, 26, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 60], []]
 b := ![[], [13, 28, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [20, 16, 38, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-128334, -192355, 315433]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1758, -2635, 4321]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [19, 19, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 24, 25], [31, 54, 54], [0, 1]]
 g := ![![[73, 5, 73], [26, 16, 1], [11, 7, 64], [65, 23, 64], [66, 1], []], ![[4, 26, 13, 32], [19, 10, 66, 42], [50, 31], [29, 33, 28, 62], [29, 72], [27, 72]], ![[51, 51, 52, 7], [47, 7, 10, 43], [53, 31, 12, 59], [58, 46, 70, 30], [27, 23], [77, 72]]]
 h' := ![![[35, 24, 25], [59, 65, 28], [28, 25, 78], [29, 8, 8], [10, 70, 71], [0, 0, 1], [0, 1]], ![[31, 54, 54], [71, 40, 56], [33, 11, 18], [1, 6], [3, 49, 54], [1, 36, 54], [35, 24, 25]], ![[0, 1], [26, 53, 74], [41, 43, 62], [53, 65, 71], [34, 39, 33], [51, 43, 24], [31, 54, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 46], []]
 b := ![[], [6, 38, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [19, 19, 13, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2615453, -653488, -464678]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33107, -8272, -5882]
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



lemma PB168I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB168I1 : PrimesBelowBoundCertificateInterval O 31 79 168 where
  m := 11
  g := ![1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB168I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
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
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I43N1, I59N1, I61N0, I61N1, I67N0, I67N1, I67N2, I71N1]
  Il := ![[], [], [I43N1], [], [], [I59N1], [I61N0, I61N0, I61N1], [I67N0, I67N1, I67N2], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
