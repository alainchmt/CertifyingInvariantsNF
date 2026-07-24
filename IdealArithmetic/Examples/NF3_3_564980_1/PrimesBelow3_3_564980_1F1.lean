
import IdealArithmetic.Examples.NF3_3_564980_1.RI3_3_564980_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -55, -12]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-44, -55, -12]] 
 ![![37, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![-44, -55, -12], ![-439, -548, -122], ![-2204, -2754, -603]]]
  hmulB := by decide  
  f := ![![![5544, 117, -134]], ![![1985, 42, -48]], ![![4762, 100, -115]]]
  g := ![![![30, -55, -12], ![301, -548, -122], ![1504, -2754, -603]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48, -65, 14]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-48, -65, 14]] 
 ![![37, 0, 0], ![23, 1, 0], ![32, 0, 1]] where
  M :=![![![-48, -65, 14], ![383, 540, -116], ![-1562, -2212, 475]]]
  hmulB := by decide  
  f := ![![![-92, -93, -20]], ![![-77, -83, -18]], ![![-180, -206, -45]]]
  g := ![![![27, -65, 14], ![-225, 540, -116], ![922, -2212, 475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2645, -56, 64]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-2645, -56, 64]] 
 ![![37, 0, 0], ![36, 1, 0], ![0, 0, 1]] where
  M :=![![![-2645, -56, 64], ![1992, 43, -48], ![576, 16, -13]]]
  hmulB := by decide  
  f := ![![![-209, -296, 64]], ![![-156, -221, 48]], ![![-192, -272, 59]]]
  g := ![![![-17, -56, 64], ![12, 43, -48], ![0, 16, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-44, -55, -12]] ![![-48, -65, 14]]
  ![![-209, -296, 64]] where
 M := ![![![-209, -296, 64]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-209, -296, 64]] ![![-2645, -56, 64]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![8, 1, 0]] 
 ![![41, 0, 0], ![8, 1, 0], ![30, 0, 1]] where
  M :=![![![8, 1, 0], ![1, 8, 2], ![32, 42, 9]]]
  hmulB := by decide  
  f := ![![![12, 9, -2]], ![![1, 0, 0]], ![![14, 14, -3]]]
  g := ![![![0, 1, 0], ![-3, 8, 2], ![-14, 42, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -28, 6]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-19, -28, 6]] 
 ![![41, 0, 0], ![24, 1, 0], ![20, 0, 1]] where
  M :=![![![-19, -28, 6], ![164, 233, -50], ![-674, -954, 205]]]
  hmulB := by decide  
  f := ![![![65, 16, 2]], ![![40, 13, 2]], ![![46, 26, 5]]]
  g := ![![![13, -28, 6], ![-108, 233, -50], ![442, -954, 205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![8, 1, 0]] ![![8, 1, 0]]
  ![![65, 16, 2]] where
 M := ![![![65, 16, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![65, 16, 2]] ![![-19, -28, 6]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1035, 22, -25]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1035, 22, -25]] 
 ![![43, 0, 0], ![0, 43, 0], ![36, 6, 1]] where
  M :=![![![1035, 22, -25], ![-778, -15, 19], ![-221, -1, 7]]]
  hmulB := by decide  
  f := ![![![-2, -3, 1]], ![![29, 40, -5]], ![![1, 1, 1]]]
  g := ![![![45, 4, -25], ![-34, -3, 19], ![-11, -1, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [3, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 42], [0, 1]]
 g := ![![[11, 31], [16, 13], [6], [37, 14], [1]], ![[20, 12], [17, 30], [6], [5, 29], [1]]]
 h' := ![![[10, 42], [38, 17], [5, 23], [18, 36], [40, 10], [0, 1]], ![[0, 1], [36, 26], [20, 20], [34, 7], [11, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [5, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [3, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![248, 285, 112]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88, -9, 112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 3, -1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![2, 3, -1]] 
 ![![43, 0, 0], ![30, 1, 0], ![2, 0, 1]] where
  M :=![![![2, 3, -1], ![-29, -40, 5], ![59, 89, -37]]]
  hmulB := by decide  
  f := ![![![-1035, -22, 25]], ![![-704, -15, 17]], ![![-43, -1, 1]]]
  g := ![![![-2, 3, -1], ![27, -40, 5], ![-59, 89, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1035, 22, -25]] ![![2, 3, -1]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12361, 262, -299]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![12361, 262, -299]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 15, 1]] where
  M :=![![![12361, 262, -299], ![-9306, -197, 225], ![-2679, -59, 65]]]
  hmulB := by decide  
  f := ![![![-10, -13, -1]], ![![-45, -52, -27]], ![![-24, -29, -10]]]
  g := ![![![263, 101, -299], ![-198, -76, 225], ![-57, -22, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [11, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 46], [0, 1]]
 g := ![![[46, 27], [38, 36], [45, 36], [8, 27], [1]], ![[14, 20], [11, 11], [18, 11], [23, 20], [1]]]
 h' := ![![[11, 46], [5, 36], [22, 41], [6, 6], [36, 11], [0, 1]], ![[0, 1], [25, 11], [3, 6], [25, 41], [16, 36], [11, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [27, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [11, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![376, 5, 1238]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -395, 1238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -13, -1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-10, -13, -1]] 
 ![![47, 0, 0], ![16, 1, 0], ![37, 0, 1]] where
  M :=![![![-10, -13, -1], ![-45, -52, -27], ![-453, -583, -65]]]
  hmulB := by decide  
  f := ![![![12361, 262, -299]], ![![4010, 85, -97]], ![![9674, 205, -234]]]
  g := ![![![5, -13, -1], ![38, -52, -27], ![240, -583, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![12361, 262, -299]] ![![-10, -13, -1]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55910, -69831, -15405]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-55910, -69831, -15405]] 
 ![![53, 0, 0], ![5, 1, 0], ![41, 0, 1]] where
  M :=![![![-55910, -69831, -15405], ![-562791, -702920, -155067], ![-2804577, -3502887, -772751]]]
  hmulB := by decide  
  f := ![![![45509, 846, -1077]], ![![3659, 85, -90]], ![![34964, 573, -812]]]
  g := ![![![17450, -69831, -15405], ![175652, -702920, -155067], ![875333, -3502887, -772751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3466, 4329, 955]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![3466, 4329, 955]] 
 ![![53, 0, 0], ![42, 1, 0], ![46, 0, 1]] where
  M :=![![![3466, 4329, 955], ![34889, 43576, 9613], ![173863, 217153, 47905]]]
  hmulB := by decide  
  f := ![![![-16491, -370, 403]], ![![-12832, -285, 313]], ![![-14255, -333, 351]]]
  g := ![![![-4194, 4329, 955], ![-42217, 43576, 9613], ![-210381, 217153, 47905]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-55910, -69831, -15405]] ![![-55910, -69831, -15405]]
  ![![85630695106, 106951831965, 23594006382]] where
 M := ![![![85630695106, 106951831965, 23594006382]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![85630695106, 106951831965, 23594006382]] ![![3466, 4329, 955]]
  ![![53, 0, 0]] where
 M := ![![![8130363186257947, 10154737576691160, 2240176150235485]]]
 hmul := by decide  
 g := ![![![![153403078985999, 191598822201720, 42267474532745]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17309, -21618, -4769]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-17309, -21618, -4769]] 
 ![![59, 0, 0], ![0, 59, 0], ![45, 33, 1]] where
  M :=![![![-17309, -21618, -4769], ![-174226, -217607, -48005], ![-868229, -1084409, -239225]]]
  hmulB := by decide  
  f := ![![![-330, -331, 73]], ![![2005, 2736, -589]], ![![736, 1088, -233]]]
  g := ![![![3344, 2301, -4769], ![33661, 23162, -48005], ![167744, 115424, -239225]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 58], [0, 1]]
 g := ![![[30, 53], [7, 49], [21], [22, 9], [56, 1]], ![[48, 6], [37, 10], [21], [54, 50], [53, 58]]]
 h' := ![![[56, 58], [17, 42], [11, 7], [45, 27], [18, 3], [0, 1]], ![[0, 1], [9, 17], [49, 52], [23, 32], [9, 56], [56, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [12, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![160985, 155501, 191204]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143105, -104309, 191204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-330, -331, 73]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-330, -331, 73]] 
 ![![59, 0, 0], ![51, 1, 0], ![57, 0, 1]] where
  M :=![![![-330, -331, 73], ![2005, 2736, -589], ![-7891, -11201, 2405]]]
  hmulB := by decide  
  f := ![![![-17309, -21618, -4769]], ![![-17915, -22375, -4936]], ![![-31438, -39265, -8662]]]
  g := ![![![210, -331, 73], ![-1762, 2736, -589], ![7225, -11201, 2405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-17309, -21618, -4769]] ![![-330, -331, 73]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -39, 6]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-28, -39, 6]] 
 ![![61, 0, 0], ![0, 61, 0], ![36, 24, 1]] where
  M :=![![![-28, -39, 6], ![153, 224, -72], ![-1026, -1416, 185]]]
  hmulB := by decide  
  f := ![![![992, 21, -24]], ![![-747, -16, 18]], ![![288, 6, -7]]]
  g := ![![![-4, -3, 6], ![45, 32, -72], ![-126, -96, 185]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [39, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 60], [0, 1]]
 g := ![![[35, 36], [20], [44, 15], [19, 4], [38, 1]], ![[0, 25], [20], [4, 46], [49, 57], [15, 60]]]
 h' := ![![[38, 60], [16, 6], [53, 9], [52, 36], [43, 2], [0, 1]], ![[0, 1], [0, 55], [29, 52], [17, 25], [58, 59], [38, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [49, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [39, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![603, 524, 947]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-549, -364, 947]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![992, 21, -24]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![992, 21, -24]] 
 ![![61, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![992, 21, -24], ![-747, -16, 18], ![-216, -6, 5]]]
  hmulB := by decide  
  f := ![![![-28, -39, 6]], ![![-3, -4, 0]], ![![-26, -36, 5]]]
  g := ![![![20, 21, -24], ![-15, -16, 18], ![-4, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-28, -39, 6]] ![![992, 21, -24]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [13, 40, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 30, 51], [25, 36, 16], [0, 1]]
 g := ![![[10, 33, 21], [27, 59, 19], [24, 36], [63, 9], [29, 1], []], ![[60, 45, 58, 58], [16, 8, 51, 3], [37, 19], [48, 17], [66, 23], [32, 55]], ![[43, 65, 59, 4], [23, 3, 41, 4], [14, 6], [47, 23], [13, 29], [0, 55]]]
 h' := ![![[4, 30, 51], [51, 54, 17], [5, 30, 32], [7, 18, 61], [25, 33, 64], [0, 0, 1], [0, 1]], ![[25, 36, 16], [33, 59, 16], [55, 15, 2], [0, 15, 32], [17, 24, 34], [2, 54, 36], [4, 30, 51]], ![[0, 1], [33, 21, 34], [52, 22, 33], [57, 34, 41], [47, 10, 36], [22, 13, 30], [25, 36, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 8], []]
 b := ![[], [4, 39, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [13, 40, 38, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29279, -35912, -10452]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-437, -536, -156]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5570, -117, 135]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-5570, -117, 135]] 
 ![![71, 0, 0], ![0, 71, 0], ![35, 37, 1]] where
  M :=![![![-5570, -117, 135], ![4203, 100, -99], ![1251, 81, -17]]]
  hmulB := by decide  
  f := ![![![89, 126, -27]], ![![-738, -1045, 225]], ![![-298, -422, 91]]]
  g := ![![![-145, -72, 135], ![108, 53, -99], ![26, 10, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [43, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 70], [0, 1]]
 g := ![![[38, 38], [42, 1], [36, 24], [54], [1], [1]], ![[0, 33], [41, 70], [12, 47], [54], [1], [1]]]
 h' := ![![[70, 70], [40, 40], [14, 70], [59, 33], [31, 14], [28, 70], [0, 1]], ![[0, 1], [0, 31], [15, 1], [26, 38], [17, 57], [29, 1], [70, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [49, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [43, 1, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4391, 5216, 1229]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-544, -567, 1229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 126, -27]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![89, 126, -27]] 
 ![![71, 0, 0], ![67, 1, 0], ![28, 0, 1]] where
  M :=![![![89, 126, -27], ![-738, -1045, 225], ![3033, 4293, -919]]]
  hmulB := by decide  
  f := ![![![-5570, -117, 135]], ![![-5197, -109, 126]], ![![-2179, -45, 53]]]
  g := ![![![-107, 126, -27], ![887, -1045, 225], ![-3646, 4293, -919]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-5570, -117, 135]] ![![89, 126, -27]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, 139, 31]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![100, 139, 31]] 
 ![![73, 0, 0], ![0, 73, 0], ![15, 61, 1]] where
  M :=![![![100, 139, 31], ![1131, 1402, 309], ![5595, 6985, 1541]]]
  hmulB := by decide  
  f := ![![![-29, -32, 7]], ![![192, 265, -57]], ![![144, 200, -43]]]
  g := ![![![-5, -24, 31], ![-48, -239, 309], ![-240, -1192, 1541]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [31, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 72], [0, 1]]
 g := ![![[11, 2], [6], [61], [15, 1], [65], [1]], ![[59, 71], [6], [61], [39, 72], [65], [1]]]
 h' := ![![[24, 72], [69, 32], [6, 15], [46, 39], [41, 72], [42, 24], [0, 1]], ![[0, 1], [34, 41], [1, 58], [33, 34], [17, 1], [34, 49], [24, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [33, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [31, 49, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-297, -288, 243]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -207, 243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -32, 7]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-29, -32, 7]] 
 ![![73, 0, 0], ![23, 1, 0], ![28, 0, 1]] where
  M :=![![![-29, -32, 7], ![192, 265, -57], ![-765, -1085, 233]]]
  hmulB := by decide  
  f := ![![![100, 139, 31]], ![![47, 63, 14]], ![![115, 149, 33]]]
  g := ![![![7, -32, 7], ![-59, 265, -57], ![242, -1085, 233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![100, 139, 31]] ![![-29, -32, 7]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [65, 34, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 38, 68], [43, 40, 11], [0, 1]]
 g := ![![[44, 73, 19], [78, 14, 13], [26, 55, 20], [26, 53, 19], [27, 1], []], ![[57, 73, 74, 47], [55, 54, 53, 58], [29, 20, 60, 60], [56, 31, 14, 70], [50, 20], [61, 42]], ![[43, 52, 18, 49], [36, 70, 41, 4], [0, 35, 48, 52], [47, 53, 55, 76], [72, 22], [39, 42]]]
 h' := ![![[63, 38, 68], [65, 6, 16], [48, 57, 31], [48, 68, 40], [62, 44, 63], [0, 0, 1], [0, 1]], ![[43, 40, 11], [33, 51, 21], [50, 11, 60], [68, 48, 62], [5, 32, 61], [4, 63, 40], [63, 38, 68]], ![[0, 1], [12, 22, 42], [35, 11, 67], [22, 42, 56], [53, 3, 34], [25, 16, 38], [43, 40, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 3], []]
 b := ![[], [18, 17, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [65, 34, 52, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292063, 340411, 164794]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3697, 4309, 2086]
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
  g := ![3, 3, 2, 2, 3, 2, 2, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB168I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
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
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N0
      exact NI41N1
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
      exact NI53N0
      exact NI53N1
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
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I43N1, I47N1, I53N0, I53N1, I59N1, I61N1, I71N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N0, I41N1], [I43N1], [I47N1], [I53N0, I53N0, I53N1], [I59N1], [I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
