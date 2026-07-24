
import IdealArithmetic.Examples.NF3_3_874321_1.RI3_3_874321_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![4, 1, 0]] 
 ![![37, 0, 0], ![4, 1, 0], ![18, 0, 1]] where
  M :=![![![4, 1, 0], ![0, 5, 3], ![177, 54, 4]]]
  hmulB := by decide  
  f := ![![![142, 4, -3]], ![![1, 0, 0]], ![![93, 3, -2]]]
  g := ![![![0, 1, 0], ![-2, 5, 3], ![-3, 54, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 5, -1]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![24, 5, -1]] 
 ![![37, 0, 0], ![34, 1, 0], ![35, 0, 1]] where
  M :=![![![24, 5, -1], ![-177, -25, 15], ![944, 211, -30]]]
  hmulB := by decide  
  f := ![![![-2415, -61, 50]], ![![-1980, -50, 41]], ![![-2656, -67, 55]]]
  g := ![![![-3, 5, -1], ![4, -25, 15], ![-140, 211, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7197, 182, -149]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![7197, 182, -149]] 
 ![![37, 0, 0], ![35, 1, 0], ![24, 0, 1]] where
  M :=![![![7197, 182, -149], ![-26373, -667, 546], ![41005, 1037, -849]]]
  hmulB := by decide  
  f := ![![![81, 5, -11]], ![![24, -9, -10]], ![![94, -7, -21]]]
  g := ![![![119, 182, -149], ![-436, -667, 546], ![678, 1037, -849]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![4, 1, 0]] ![![24, 5, -1]]
  ![![-81, -5, 11]] where
 M := ![![![-81, -5, 11]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-81, -5, 11]] ![![7197, 182, -149]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [25, 36, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 4, 37], [11, 36, 4], [0, 1]]
 g := ![![[9, 31, 18], [29, 18], [30, 2], [4, 32, 1], []], ![[24, 19, 22, 16], [7, 4], [18, 1], [12, 15, 21, 23], [29, 16]], ![[19, 14, 18, 20], [3, 21], [35, 37], [8, 9, 37, 23], [21, 16]]]
 h' := ![![[21, 4, 37], [23, 17, 31], [25, 13, 31], [23, 40, 17], [0, 0, 1], [0, 1]], ![[11, 36, 4], [22, 36, 23], [22, 20, 39], [12, 34, 1], [3, 36, 36], [21, 4, 37]], ![[0, 1], [27, 29, 28], [26, 8, 12], [32, 8, 23], [6, 5, 4], [11, 36, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 14], []]
 b := ![[], [31, 2, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [25, 36, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2326463, -1226105, -381341]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56743, -29905, -9301]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64689, -12011, 3629]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-64689, -12011, 3629]] 
 ![![43, 0, 0], ![0, 43, 0], ![42, 27, 1]] where
  M :=![![![-64689, -12011, 3629], ![642333, 119266, -36033], ![-2340058, -434483, 131277]]]
  hmulB := by decide  
  f := ![![![-26901, -680, 557]], ![![98589, 2497, -2040]], ![![32066, 814, -663]]]
  g := ![![![-5049, -2558, 3629], ![50133, 25399, -36033], ![-182644, -92534, 131277]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [36, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[3, 6], [21, 35], [24], [9, 11], [1]], ![[0, 37], [25, 8], [24], [25, 32], [1]]]
 h' := ![![[21, 42], [18, 36], [9, 32], [20, 14], [7, 21], [0, 1]], ![[0, 1], [0, 7], [36, 11], [13, 29], [18, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [27, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [36, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![310, 2036, 1453]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1412, -865, 1453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26901, -680, 557]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-26901, -680, 557]] 
 ![![43, 0, 0], ![5, 1, 0], ![33, 0, 1]] where
  M :=![![![-26901, -680, 557], ![98589, 2497, -2040], ![-153223, -3857, 3177]]]
  hmulB := by decide  
  f := ![![![-64689, -12011, 3629]], ![![7416, 1377, -416]], ![![-104065, -19322, 5838]]]
  g := ![![![-974, -680, 557], ![3568, 2497, -2040], ![-5553, -3857, 3177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-64689, -12011, 3629]] ![![-26901, -680, 557]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [31, 41, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 0, 38], [14, 46, 9], [0, 1]]
 g := ![![[45, 22, 1], [29, 2, 9], [26, 45, 21], [1, 29, 1], []], ![[11, 33, 28, 29], [17, 21, 17, 22], [38, 3, 13, 46], [16, 45, 23, 38], [46, 34]], ![[23, 3, 31, 12], [26, 16, 38, 8], [22, 18], [8, 21], [28, 34]]]
 h' := ![![[15, 0, 38], [41, 20, 1], [40, 4, 44], [16, 0, 31], [0, 0, 1], [0, 1]], ![[14, 46, 9], [33, 21, 7], [37, 31, 14], [9, 40, 16], [21, 21, 46], [15, 0, 38]], ![[0, 1], [25, 6, 39], [44, 12, 36], [5, 7], [33, 26], [14, 46, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 5], []]
 b := ![[], [12, 11, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [31, 41, 18, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188000, -16638, -22278]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4000, -354, -474]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3813538, -96436, 78951]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-3813538, -96436, 78951]] 
 ![![53, 0, 0], ![0, 53, 0], ![35, 35, 1]] where
  M :=![![![-3813538, -96436, 78951], ![13974327, 353380, -289308], ![-21727281, -549435, 449816]]]
  hmulB := by decide  
  f := ![![![700, 247, 36]], ![![6372, 2891, 741]], ![![5455, 2364, 563]]]
  g := ![![![-124091, -53957, 78951], ![454719, 197720, -289308], ![-706997, -307415, 449816]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [24, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 52], [0, 1]]
 g := ![![[52, 42], [29], [50, 1], [7], [24, 1]], ![[0, 11], [29], [21, 52], [7], [48, 52]]]
 h' := ![![[24, 52], [36, 25], [19, 20], [40, 52], [7, 22], [0, 1]], ![[0, 1], [0, 28], [22, 33], [16, 1], [5, 31], [24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [8, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [24, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2119, 4345, 2441]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1572, -1530, 2441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-700, -247, -36]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-700, -247, -36]] 
 ![![53, 0, 0], ![1, 1, 0], ![17, 0, 1]] where
  M :=![![![-700, -247, -36], ![-6372, -2891, -741], ![-41595, -15462, -2644]]]
  hmulB := by decide  
  f := ![![![3813538, 96436, -78951]], ![![-191713, -4848, 3969]], ![![1633159, 41299, -33811]]]
  g := ![![![3, -247, -36], ![172, -2891, -741], ![355, -15462, -2644]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-3813538, -96436, 78951]] ![![-700, -247, -36]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24544, -4557, 1377]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-24544, -4557, 1377]] 
 ![![59, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-24544, -4557, 1377], ![243729, 45257, -13671], ![-887832, -164835, 49814]]]
  hmulB := by decide  
  f := ![![![972913, 24603, -20142]], ![![-60426, -1528, 1251]], ![![93951, 2376, -1945]]]
  g := ![![![-416, -4557, 1377], ![4131, 45257, -13671], ![-15048, -164835, 49814]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1110, -28, 23]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-1110, -28, 23]] 
 ![![59, 0, 0], ![29, 1, 0], ![5, 0, 1]] where
  M :=![![![-1110, -28, 23], ![4071, 104, -84], ![-6313, -155, 132]]]
  hmulB := by decide  
  f := ![![![-708, -131, 40]], ![![-228, -42, 13]], ![![-493, -91, 28]]]
  g := ![![![-7, -28, 23], ![25, 104, -84], ![-42, -155, 132]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-24544, -4557, 1377]] ![![-1110, -28, 23]]
  ![![-708, -131, 40]] where
 M := ![![![-708, -131, 40]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-708, -131, 40]] ![![-1110, -28, 23]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27639, -698, 572]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-27639, -698, 572]] 
 ![![61, 0, 0], ![0, 61, 0], ![13, 28, 1]] where
  M :=![![![-27639, -698, 572], ![101244, 2551, -2094], ![-157294, -3944, 3249]]]
  hmulB := by decide  
  f := ![![![-483, -194, -40]], ![![-7080, -2837, -582]], ![![-3877, -1554, -319]]]
  g := ![![![-575, -274, 572], ![2106, 1003, -2094], ![-3271, -1556, 3249]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [52, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 60], [0, 1]]
 g := ![![[16, 27], [56], [30, 39], [29, 25], [22, 1]], ![[0, 34], [56], [34, 22], [30, 36], [44, 60]]]
 h' := ![![[22, 60], [21, 24], [26, 19], [17, 51], [15, 5], [0, 1]], ![[0, 1], [0, 37], [17, 42], [41, 10], [3, 56], [22, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [35, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [52, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2117, 2481, 1167]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-214, -495, 1167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-483, -194, -40]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-483, -194, -40]] 
 ![![61, 0, 0], ![38, 1, 0], ![55, 0, 1]] where
  M :=![![![-483, -194, -40], ![-7080, -2837, -582], ![-31978, -12836, -2643]]]
  hmulB := by decide  
  f := ![![![-27639, -698, 572]], ![![-15558, -393, 322]], ![![-27499, -694, 569]]]
  g := ![![![149, -194, -40], ![2176, -2837, -582], ![9855, -12836, -2643]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-27639, -698, 572]] ![![-483, -194, -40]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![464097, 86171, -26035]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![464097, 86171, -26035]] 
 ![![67, 0, 0], ![0, 67, 0], ![57, 41, 1]] where
  M :=![![![464097, 86171, -26035], ![-4608195, -855622, 258513], ![16788332, 3117169, -941793]]]
  hmulB := by decide  
  f := ![![![-147753, -3736, 3059]], ![![541443, 13697, -11208]], ![![193067, 4886, -3996]]]
  g := ![![![29076, 17218, -26035], ![-288708, -170965, 258513], ![1051799, 622846, -941793]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [1, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 66], [0, 1]]
 g := ![![[15, 1], [15, 1], [4], [25], [24], [1]], ![[0, 66], [0, 66], [4], [25], [24], [1]]]
 h' := ![![[52, 66], [52, 66], [15, 1], [35, 65], [44, 5], [66, 52], [0, 1]], ![[0, 1], [0, 1], [0, 66], [65, 2], [36, 62], [23, 15], [52, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [16, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [1, 15, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![191118, 188479, 92671]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75987, -53896, 92671]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-147753, -3736, 3059]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-147753, -3736, 3059]] 
 ![![67, 0, 0], ![11, 1, 0], ![23, 0, 1]] where
  M :=![![![-147753, -3736, 3059], ![541443, 13697, -11208], ![-841753, -21263, 17433]]]
  hmulB := by decide  
  f := ![![![464097, 86171, -26035]], ![![7416, 1377, -416]], ![![409889, 76106, -22994]]]
  g := ![![![-2642, -3736, 3059], ![9680, 13697, -11208], ![-15057, -21263, 17433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![464097, 86171, -26035]] ![![-147753, -3736, 3059]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [31, 38, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 24, 24], [41, 46, 47], [0, 1]]
 g := ![![[39, 55, 2], [64, 53, 40], [56, 55, 60], [8, 64], [39, 1], []], ![[22, 61, 7, 10], [61, 28, 31, 64], [46, 47, 44, 27], [16, 19], [2, 57], [44, 8]], ![[29, 68, 23, 41], [57, 34, 58, 31], [13, 34, 21, 63], [58, 6], [23, 8], [21, 8]]]
 h' := ![![[69, 24, 24], [4, 2, 12], [39, 39, 18], [40, 1, 29], [69, 49, 63], [0, 0, 1], [0, 1]], ![[41, 46, 47], [10, 67, 32], [47, 6, 60], [3, 64, 9], [59, 51, 27], [60, 43, 46], [69, 24, 24]], ![[0, 1], [21, 2, 27], [14, 26, 64], [60, 6, 33], [15, 42, 52], [36, 28, 24], [41, 46, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 38], []]
 b := ![[], [51, 3, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [31, 38, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![762540, 373389, 106926]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10740, 5259, 1506]
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


def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33525, 848, -694]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![33525, 848, -694]] 
 ![![73, 0, 0], ![2, 1, 0], ![71, 0, 1]] where
  M :=![![![33525, 848, -694], ![-122838, -3103, 2544], ![191042, 4846, -3951]]]
  hmulB := by decide  
  f := ![![![-68271, -12676, 3830]], ![![7416, 1377, -416]], ![![-100231, -18610, 5623]]]
  g := ![![![1111, 848, -694], ![-4072, -3103, 2544], ![6327, 4846, -3951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3617, 92, -75]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![3617, 92, -75]] 
 ![![73, 0, 0], ![68, 1, 0], ![42, 0, 1]] where
  M :=![![![3617, 92, -75], ![-13275, -341, 276], ![20709, 543, -433]]]
  hmulB := by decide  
  f := ![![![-2215, -889, -183]], ![![-2507, -1006, -207]], ![![-3282, -1317, -271]]]
  g := ![![![7, 92, -75], ![-23, -341, 276], ![27, 543, -433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![33525, 848, -694]] ![![33525, 848, -694]]
  ![![887175853, 22434732, -18367044]] where
 M := ![![![887175853, 22434732, -18367044]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI73N1 : IdealMulLeCertificate' Table 
  ![![887175853, 22434732, -18367044]] ![![3617, 92, -75]]
  ![![73, 0, 0]] where
 M := ![![![2530730878805, 63996629972, -52393272891]]]
 hmul := by decide  
 g := ![![![![34667546285, 876666164, -717716067]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78, -26, -5]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-78, -26, -5]] 
 ![![79, 0, 0], ![0, 79, 0], ![63, 21, 1]] where
  M :=![![![-78, -26, -5], ![-885, -374, -78], ![-4307, -1699, -348]]]
  hmulB := by decide  
  f := ![![![30, 7, -2]], ![![-354, -71, 21]], ![![-53, -10, 3]]]
  g := ![![![3, 1, -5], ![51, 16, -78], ![223, 71, -348]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [64, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 78], [0, 1]]
 g := ![![[46, 21], [14, 46], [63, 5], [25, 19], [46], [1]], ![[0, 58], [75, 33], [37, 74], [21, 60], [46], [1]]]
 h' := ![![[58, 78], [52, 10], [76, 21], [59, 59], [46, 63], [15, 58], [0, 1]], ![[0, 1], [0, 69], [30, 58], [5, 20], [66, 16], [61, 21], [58, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [8, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [64, 21, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4784, 6440, 3651]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2851, -889, 3651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30, -7, 2]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-30, -7, 2]] 
 ![![79, 0, 0], ![16, 1, 0], ![41, 0, 1]] where
  M :=![![![-30, -7, 2], ![354, 71, -21], ![-1357, -260, 78]]]
  hmulB := by decide  
  f := ![![![78, 26, 5]], ![![27, 10, 2]], ![![95, 35, 7]]]
  g := ![![![0, -7, 2], ![1, 71, -21], ![-5, -260, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-78, -26, -5]] ![![-30, -7, 2]]
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


lemma PB208I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB208I1 : PrimesBelowBoundCertificateInterval O 31 79 208 where
  m := 11
  g := ![3, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB208I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N0, I73N1]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
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
      exact NI37N2
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
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I43N1, I53N1, I59N0, I59N1, I61N1, I67N1, I73N0, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N1], [], [I53N1], [I59N0, I59N1, I59N1], [I61N1], [I67N1], [], [I73N0, I73N0, I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
