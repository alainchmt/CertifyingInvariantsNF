
import IdealArithmetic.Examples.NF3_3_598044_1.RI3_3_598044_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, -2232, 510]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![349, -2232, 510]] 
 ![![37, 0, 0], ![0, 37, 0], ![35, 20, 1]] where
  M :=![![![349, -2232, 510], ![-3060, 19537, -4464], ![14922, -95274, 21769]]]
  hmulB := by decide  
  f := ![![![-59, -36, -6]], ![![36, -347, -72]], ![![-31, -262, -53]]]
  g := ![![![-473, -336, 510], ![4140, 2941, -4464], ![-20189, -14342, 21769]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [4, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 36], [0, 1]]
 g := ![![[32, 28], [10], [5, 16], [30], [1]], ![[0, 9], [10], [29, 21], [30], [1]]]
 h' := ![![[20, 36], [27, 19], [17, 11], [7, 33], [33, 20], [0, 1]], ![[0, 1], [0, 18], [15, 26], [1, 4], [26, 17], [20, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [12, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [4, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41, 447, 335]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-318, -169, 335]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -36, -6]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-59, -36, -6]] 
 ![![37, 0, 0], ![34, 1, 0], ![34, 0, 1]] where
  M :=![![![-59, -36, -6], ![36, -347, -72], ![198, -1494, -311]]]
  hmulB := by decide  
  f := ![![![349, -2232, 510]], ![![238, -1523, 348]], ![![724, -4626, 1057]]]
  g := ![![![37, -36, -6], ![386, -347, -72], ![1664, -1494, -311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![349, -2232, 510]] ![![-59, -36, -6]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [15, 27, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 33, 18], [3, 7, 23], [0, 1]]
 g := ![![[8, 22, 9], [33, 10], [], [9, 6, 1], []], ![[10, 19, 15, 21], [26, 4], [31, 23], [14, 19, 2, 21], [16, 37]], ![[5, 20, 11, 4], [20, 37], [29, 23], [31, 33, 24, 37], [11, 37]]]
 h' := ![![[3, 33, 18], [28, 22, 3], [21, 38, 25], [29, 36], [0, 0, 1], [0, 1]], ![[3, 7, 23], [16, 40, 7], [18, 20, 39], [14, 40, 33], [15, 31, 7], [3, 33, 18]], ![[0, 1], [36, 20, 31], [7, 24, 18], [14, 6, 8], [8, 10, 33], [3, 7, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 28], []]
 b := ![[], [6, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [15, 27, 35, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2870, 78269, 135218]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, 1909, 3298]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 8, 2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-1, 8, 2]] 
 ![![43, 0, 0], ![11, 1, 0], ![20, 0, 1]] where
  M :=![![![-1, 8, 2], ![-12, 91, 16], ![-42, 330, 83]]]
  hmulB := by decide  
  f := ![![![2273, -4, -54]], ![![589, -1, -14]], ![![1054, -2, -25]]]
  g := ![![![-3, 8, 2], ![-31, 91, 16], ![-124, 330, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91468, -704013, -146509]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![91468, -704013, -146509]] 
 ![![43, 0, 0], ![20, 1, 0], ![5, 0, 1]] where
  M :=![![![91468, -704013, -146509], ![879054, -6765923, -1408026], ![3784551, -29129019, -6061910]]]
  hmulB := by decide  
  f := ![![![186436, -159, -4469]], ![![87338, -107, -2086]], ![![21389, 138, -549]]]
  g := ![![![346611, -704013, -146509], ![3331108, -6765923, -1408026], ![14341267, -29129019, -6061910]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-1, 8, 2]] ![![-1, 8, 2]]
  ![![-179, 1380, 292]] where
 M := ![![![-179, 1380, 292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-179, 1380, 292]] ![![91468, -704013, -146509]]
  ![![43, 0, 0]] where
 M := ![![![2301810640, -17716628961, -3686928489]]]
 hmul := by decide  
 g := ![![![![53530480, -412014627, -85742523]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1840, 2357, -503]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1840, 2357, -503]] 
 ![![47, 0, 0], ![1, 1, 0], ![46, 0, 1]] where
  M :=![![![-1840, 2357, -503], ![3018, -20609, 4714], ![-15651, 100503, -22966]]]
  hmulB := by decide  
  f := ![![![464848, -3577853, -744571]], ![![104942, -807720, -168091]], ![![864179, -6651433, -1384200]]]
  g := ![![![403, 2357, -503], ![-4111, -20609, 4714], ![20006, 100503, -22966]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3533, -6, -84]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![3533, -6, -84]] 
 ![![47, 0, 0], ![5, 1, 0], ![32, 0, 1]] where
  M :=![![![3533, -6, -84], ![504, -1, -12], ![-216, 0, 5]]]
  hmulB := by decide  
  f := ![![![-5, 30, -12]], ![![1, -7, 0]], ![![-8, 48, -19]]]
  g := ![![![133, -6, -84], ![19, -1, -12], ![-8, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4711, 8, 112]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-4711, 8, 112]] 
 ![![47, 0, 0], ![40, 1, 0], ![26, 0, 1]] where
  M :=![![![-4711, 8, 112], ![-672, 1, 16], ![288, 0, -7]]]
  hmulB := by decide  
  f := ![![![7, -56, -16]], ![![8, -63, -16]], ![![10, -80, -23]]]
  g := ![![![-169, 8, 112], ![-24, 1, 16], ![10, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1840, 2357, -503]] ![![3533, -6, -84]]
  ![![-5204144, 8683, 123761]] where
 M := ![![![-5204144, 8683, 123761]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-5204144, 8683, 123761]] ![![-4711, 8, 112]]
  ![![47, 0, 0]] where
 M := ![![![24546530576, -41624469, -583591527]]]
 hmul := by decide  
 g := ![![![![522266608, -885627, -12416841]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17069, 1892, -852]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![17069, 1892, -852]] 
 ![![53, 0, 0], ![0, 53, 0], ![39, 4, 1]] where
  M :=![![![17069, 1892, -852], ![5112, -16823, 3784], ![-13908, 82020, -18715]]]
  hmulB := by decide  
  f := ![![![84505, -650420, -135356]], ![![812136, -6250867, -1300840]], ![![189447, -1458140, -303447]]]
  g := ![![![949, 100, -852], ![-2688, -603, 3784], ![13509, 2960, -18715]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [29, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 52], [0, 1]]
 g := ![![[10, 11], [17], [46, 9], [10], [28, 1]], ![[0, 42], [17], [33, 44], [10], [3, 52]]]
 h' := ![![[28, 52], [12, 45], [44, 21], [52, 50], [36, 13], [0, 1]], ![[0, 1], [0, 8], [49, 32], [21, 3], [29, 40], [28, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [34, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [29, 25, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2528, -3, 145]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59, -11, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84505, 650420, 135356]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-84505, 650420, 135356]] 
 ![![53, 0, 0], ![45, 1, 0], ![25, 0, 1]] where
  M :=![![![-84505, 650420, 135356], ![-812136, 6250867, 1300840], ![-3496452, 26911572, 5600447]]]
  hmulB := by decide  
  f := ![![![-17069, -1892, 852]], ![![-14589, -1289, 652]], ![![-7789, -2440, 755]]]
  g := ![![![-617685, 650420, 135356], ![-5936267, 6250867, 1300840], ![-25557139, 26911572, 5600447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![17069, 1892, -852]] ![![-84505, 650420, 135356]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [7, 24, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 5, 37], [15, 53, 22], [0, 1]]
 g := ![![[3, 10, 1], [48, 41, 21], [41, 3], [13, 13, 36], [1]], ![[28, 33, 27, 40], [25, 11, 54, 24], [20, 49], [42, 53, 58, 55], [28, 13, 53, 31]], ![[29, 53, 11, 57], [10, 24, 0, 29], [28, 16], [4, 24, 7, 49], [21, 5, 29, 28]]]
 h' := ![![[38, 5, 37], [18, 51, 58], [29, 57, 32], [27, 0, 48], [52, 35, 53], [0, 1]], ![[15, 53, 22], [2, 31, 5], [0, 19, 29], [9, 14, 7], [42, 11, 33], [38, 5, 37]], ![[0, 1], [35, 36, 55], [40, 42, 57], [0, 45, 4], [42, 13, 32], [15, 53, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 25], []]
 b := ![[], [38, 22, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [7, 24, 6, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19529, -229097, -215704]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![331, -3883, -3656]
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


def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-626, 3997, -913]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-626, 3997, -913]] 
 ![![61, 0, 0], ![19, 1, 0], ![54, 0, 1]] where
  M :=![![![-626, 3997, -913], ![5478, -34975, 7994], ![-26721, 170613, -38972]]]
  hmulB := by decide  
  f := ![![![834622, -1415, -19843]], ![![261916, -444, -6227]], ![![738009, -1251, -17546]]]
  g := ![![![-447, 3997, -913], ![3907, -34975, 7994], ![-19080, 170613, -38972]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -15, -3]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![2, -15, -3]] 
 ![![61, 0, 0], ![22, 1, 0], ![52, 0, 1]] where
  M :=![![![2, -15, -3], ![18, -139, -30], ![81, -621, -124]]]
  hmulB := by decide  
  f := ![![![1394, -3, -33]], ![![506, -1, -12]], ![![1187, -3, -28]]]
  g := ![![![8, -15, -3], ![76, -139, -30], ![331, -621, -124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-626, 3997, -913]] ![![-626, 3997, -913]]
  ![![46683715, -298066866, 68104992]] where
 M := ![![![46683715, -298066866, 68104992]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI61N1 : IdealMulLeCertificate' Table 
  ![![46683715, -298066866, 68104992]] ![![2, -15, -3]]
  ![![61, 0, 0]] where
 M := ![![![244668194, -1562161383, 356935827]]]
 hmul := by decide  
 g := ![![![![4010954, -25609203, 5851407]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42989, -8632, 966]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![42989, -8632, 966]] 
 ![![67, 0, 0], ![0, 67, 0], ![35, 65, 1]] where
  M :=![![![42989, -8632, 966], ![-5796, 74929, -17264], ![54690, -365442, 83561]]]
  hmulB := by decide  
  f := ![![![-714157, 5496740, 1143902]], ![![-6863412, 52826467, 10993480]], ![![-7472627, 57515487, 11969291]]]
  g := ![![![137, -1066, 966], ![8932, 17867, -17264], ![-42835, -86521, 83561]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [49, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 66], [0, 1]]
 g := ![![[2, 26], [38, 25], [15], [65], [23], [1]], ![[0, 41], [0, 42], [15], [65], [23], [1]]]
 h' := ![![[36, 66], [14, 48], [21, 5], [32, 22], [1, 47], [18, 36], [0, 1]], ![[0, 1], [0, 19], [0, 62], [20, 45], [18, 20], [41, 31], [36, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [30, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [49, 31, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4, 419, 293]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-153, -278, 293]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-714157, 5496740, 1143902]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-714157, 5496740, 1143902]] 
 ![![67, 0, 0], ![4, 1, 0], ![57, 0, 1]] where
  M :=![![![-714157, 5496740, 1143902], ![-6863412, 52826467, 10993480], ![-29548734, 227431374, 47329727]]]
  hmulB := by decide  
  f := ![![![42989, -8632, 966]], ![![2480, 603, -200]], ![![37389, -12798, 2069]]]
  g := ![![![-1311993, 5496740, 1143902], ![-12608920, 52826467, 10993480], ![-54284607, 227431374, 47329727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![42989, -8632, 966]] ![![-714157, 5496740, 1143902]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -12, 2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1, -12, 2]] 
 ![![71, 0, 0], ![0, 71, 0], ![36, 65, 1]] where
  M :=![![![1, -12, 2], ![-12, 73, -24], ![78, -510, 85]]]
  hmulB := by decide  
  f := ![![![-85, 0, 2]], ![![-12, -1, 0]], ![![-54, -1, 1]]]
  g := ![![![-1, -2, 2], ![12, 23, -24], ![-42, -85, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [56, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 70], [0, 1]]
 g := ![![[59, 25], [64, 50], [18, 10], [49], [24], [1]], ![[32, 46], [10, 21], [64, 61], [49], [24], [1]]]
 h' := ![![[33, 70], [37, 5], [57, 11], [30, 9], [17, 7], [15, 33], [0, 1]], ![[0, 1], [60, 66], [65, 60], [43, 62], [35, 64], [39, 38], [33, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [8, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [56, 38, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3622, 35157, 20162]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10274, -17963, 20162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 0, -2]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![85, 0, -2]] 
 ![![71, 0, 0], ![12, 1, 0], ![64, 0, 1]] where
  M :=![![![85, 0, -2], ![12, 1, 0], ![-6, 6, 1]]]
  hmulB := by decide  
  f := ![![![-1, 12, -2]], ![![0, 1, 0]], ![![-2, 18, -3]]]
  g := ![![![3, 0, -2], ![0, 1, 0], ![-2, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1, -12, 2]] ![![85, 0, -2]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1934, -14677, -3055]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1934, -14677, -3055]] 
 ![![73, 0, 0], ![0, 73, 0], ![63, 66, 1]] where
  M :=![![![1934, -14677, -3055], ![18330, -141053, -29354], ![78897, -607269, -126376]]]
  hmulB := by decide  
  f := ![![![-826, 5291, -1209]], ![![7254, -46313, 10582]], ![![5361, -34212, 7817]]]
  g := ![![![2663, 2561, -3055], ![25584, 24607, -29354], ![110145, 105939, -126376]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [41, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 72], [0, 1]]
 g := ![![[39, 57], [25], [54], [47, 71], [49], [1]], ![[0, 16], [25], [54], [33, 2], [49], [1]]]
 h' := ![![[7, 72], [47, 35], [14, 68], [44, 28], [37, 61], [32, 7], [0, 1]], ![[0, 1], [0, 38], [52, 5], [21, 45], [26, 12], [8, 66], [7, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [12, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [41, 66, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45, 297, 114]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99, -99, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-826, 5291, -1209]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-826, 5291, -1209]] 
 ![![73, 0, 0], ![14, 1, 0], ![41, 0, 1]] where
  M :=![![![-826, 5291, -1209], ![7254, -46313, 10582], ![-35373, 225849, -51604]]]
  hmulB := by decide  
  f := ![![![1934, -14677, -3055]], ![![622, -4747, -988]], ![![2167, -16562, -3447]]]
  g := ![![![-347, 5291, -1209], ![3038, -46313, 10582], ![-14815, 225849, -51604]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1934, -14677, -3055]] ![![-826, 5291, -1209]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3619, 6, 86]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-3619, 6, 86]] 
 ![![79, 0, 0], ![0, 79, 0], ![36, 46, 1]] where
  M :=![![![-3619, 6, 86], ![-516, -1, 12], ![222, -6, -7]]]
  hmulB := by decide  
  f := ![![![-1, 6, -2]], ![![12, -79, 12]], ![![6, -40, 5]]]
  g := ![![![-85, -50, 86], ![-12, -7, 12], ![6, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [54, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 78], [0, 1]]
 g := ![![[44, 67], [56, 25], [28, 22], [40, 26], [36], [1]], ![[37, 12], [64, 54], [54, 57], [42, 53], [36], [1]]]
 h' := ![![[73, 78], [57, 15], [68, 5], [52, 38], [24, 37], [25, 73], [0, 1]], ![[0, 1], [46, 64], [38, 74], [61, 41], [39, 42], [61, 6], [73, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [29, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [54, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51, 1212, 1098]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-501, -624, 1098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 6, -2]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1, 6, -2]] 
 ![![79, 0, 0], ![66, 1, 0], ![1, 0, 1]] where
  M :=![![![-1, 6, -2], ![12, -79, 12], ![-42, 258, -85]]]
  hmulB := by decide  
  f := ![![![-3619, 6, 86]], ![![-3030, 5, 72]], ![![-43, 0, 1]]]
  g := ![![![-5, 6, -2], ![66, -79, 12], ![-215, 258, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-3619, 6, 86]] ![![-1, 6, -2]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB172I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB172I1 : PrimesBelowBoundCertificateInterval O 31 79 172 where
  m := 11
  g := ![2, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB172I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N0, I61N1]
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
    · exact ![43, 43, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
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
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
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
  β := ![I37N1, I43N0, I43N1, I47N0, I47N1, I47N2, I53N1, I61N0, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N0, I43N0, I43N1], [I47N0, I47N1, I47N2], [I53N1], [], [I61N0, I61N0, I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
