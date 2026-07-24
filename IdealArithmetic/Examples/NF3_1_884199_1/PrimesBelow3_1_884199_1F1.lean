
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [30, 13, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 8, 6], [21, 28, 31], [0, 1]]
 g := ![![[9, 29, 11], [3, 7], [5, 9, 21], [10, 1], []], ![[19, 8, 21, 24], [24, 30], [33, 4, 5, 22], [30, 7], [12, 36]], ![[36, 20, 6, 18], [5, 27], [29, 16, 32, 32], [33, 27], [24, 36]]]
 h' := ![![[26, 8, 6], [25, 28, 23], [35, 14, 28], [33, 25, 13], [0, 0, 1], [0, 1]], ![[21, 28, 31], [29, 12, 35], [34, 18, 17], [18, 11, 33], [20, 31, 28], [26, 8, 6]], ![[0, 1], [5, 34, 16], [28, 5, 29], [2, 1, 28], [17, 6, 8], [21, 28, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 31], []]
 b := ![[], [15, 6, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [30, 13, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6414838, -2004623, -426980]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-173374, -54179, -11540]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-48, 2, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-48, 2, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![34, 2, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-48, 2, 1], ![327, 12, 6], ![545, 225, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -2, 41]], ![![-2, 0, 1], ![3, 0, 6], ![5, 5, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 40], [0, 1]]
 g := ![![[10, 1], [5], [10], [4, 18], [1]], ![[0, 40], [5], [10], [29, 23], [1]]]
 h' := ![![[31, 40], [31, 40], [6, 28], [37, 25], [40, 31], [0, 1]], ![[0, 1], [0, 1], [13, 13], [33, 16], [17, 10], [31, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [11, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![537, 3314, 1493]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1225, 8, 1493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-6, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![31, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-6, 1, 0], ![0, -5, 3], ![327, 58, -6]]]
  hmulB := by decide  
  f := ![![![91, -15, 0], ![615, 0, 0]], ![![73, -12, 0], ![493, 0, 0]], ![![65, -9, -1], ![439, 14, 0]]]
  g := ![![![1, 0, 0], ![-35, 41, 0], ![-31, 0, 41]], ![![-1, 1, 0], ![2, -5, 3], ![-37, 58, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-48, 2, 1]] ![![41, 0, 0], ![-6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-246, 41, 0]], ![![-1968, 82, 41], ![615, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-6, 1, 0]]], ![![![-48, 2, 1]], ![![15, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![282, 7, -5]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![282, 7, -5]] 
 ![![43, 0, 0], ![2, 1, 0], ![41, 0, 1]] where
  M :=![![![282, 7, -5], ![-1635, -1, 21], ![2834, -139, -8]]]
  hmulB := by decide  
  f := ![![![-2927, -751, -142]], ![![-1216, -312, -59]], ![![-8142, -2089, -395]]]
  g := ![![![11, 7, -5], ![-58, -1, 21], ![80, -139, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![17, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![17, 1, 0]] 
 ![![43, 0, 0], ![17, 1, 0], ![27, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![17, 1, 0], ![0, 18, 3], ![327, 58, 17]]]
  hmulB := by decide  
  f := ![![![511, 30, 0], ![-1290, 0, 0]], ![![187, 11, 0], ![-472, 0, 0]], ![![309, 6, -2], ![-780, 29, 0]]]
  g := ![![![1, 0, 0], ![-17, 43, 0], ![-27, 0, 43]], ![![0, 1, 0], ![-9, 18, 3], ![-26, 58, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, 1, 0]] 
 ![![43, 0, 0], ![23, 1, 0], ![31, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, 1, 0], ![0, -19, 3], ![327, 58, -20]]]
  hmulB := by decide  
  f := ![![![761, -38, 0], ![1634, 0, 0]], ![![421, -21, 0], ![904, 0, 0]], ![![557, -15, -2], ![1196, 29, 0]]]
  g := ![![![1, 0, 0], ![-23, 43, 0], ![-31, 0, 43]], ![![-1, 1, 0], ![8, -19, 3], ![-9, 58, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![282, 7, -5]] ![![43, 0, 0], ![17, 1, 0]]
  ![![43, 0, 0], ![-46, -22, 1]] where
 M := ![![![12126, 301, -215], ![3159, 118, -64]]]
 hmul := by decide  
 g := ![![![![190, -37, -3], ![-86, 0, 0]], ![![51, -8, -1], ![-21, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-46, -22, 1]] ![![43, 0, 0], ![-20, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-860, 43, 0]], ![![-1978, -946, 43], ![1247, 430, -86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-20, 1, 0]]], ![![![-46, -22, 1]], ![![29, 10, -2]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [41, 12, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 2, 7], [14, 44, 40], [0, 1]]
 g := ![![[9, 28, 34], [46, 19, 27], [41, 14, 18], [6, 21, 1], []], ![[0, 13, 14, 2], [21, 45, 4, 28], [21, 12, 26, 9], [33, 23, 20, 16], [23, 2]], ![[35, 42, 24, 22], [5, 46, 7, 39], [11, 28, 29, 33], [17, 15, 30, 19], [37, 2]]]
 h' := ![![[7, 2, 7], [41, 12, 38], [11, 42, 36], [36, 7, 21], [0, 0, 1], [0, 1]], ![[14, 44, 40], [40, 33, 17], [34, 1, 45], [17, 40, 33], [46, 46, 44], [7, 2, 7]], ![[0, 1], [19, 2, 39], [43, 4, 13], [29, 0, 40], [42, 1, 2], [14, 44, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 45], []]
 b := ![[], [13, 11, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [41, 12, 26, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167602, -30738, -21855]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3566, -654, -465]
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


def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-26, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-26, 1, 0]] 
 ![![53, 0, 0], ![27, 1, 0], ![13, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-26, 1, 0], ![0, -25, 3], ![327, 58, -26]]]
  hmulB := by decide  
  f := ![![![27, 849, -102], ![53, 1802, 0]], ![![27, 424, -51], ![54, 901, 0]], ![![13, 208, -25], ![26, 442, 0]]]
  g := ![![![1, 0, 0], ![-27, 53, 0], ![-13, 0, 53]], ![![-1, 1, 0], ![12, -25, 3], ![-17, 58, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-2, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-2, 1, 0]] 
 ![![53, 0, 0], ![51, 1, 0], ![17, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-2, 1, 0], ![0, -1, 3], ![327, 58, -2]]]
  hmulB := by decide  
  f := ![![![3, 25, -78], ![53, 1378, 0]], ![![1, 25, -75], ![1, 1325, 0]], ![![1, 8, -25], ![18, 442, 0]]]
  g := ![![![1, 0, 0], ![-51, 53, 0], ![-17, 0, 53]], ![![-1, 1, 0], ![0, -1, 3], ![-49, 58, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-26, 1, 0]] ![![53, 0, 0], ![-26, 1, 0]]
  ![![53, 0, 0], ![-22, -17, 1]] where
 M := ![![![2809, 0, 0], ![-1378, 53, 0]], ![![-1378, 53, 0], ![676, -51, 3]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![-4, 18, -1], ![53, 0, 0]]], ![![![-4, 18, -1], ![53, 0, 0]], ![![14, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-22, -17, 1]] ![![53, 0, 0], ![-2, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-106, 53, 0]], ![![-1166, -901, 53], ![371, 53, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-2, 1, 0]]], ![![![-22, -17, 1]], ![![7, 1, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![190366, 8916, -4221]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![190366, 8916, -4221]] 
 ![![59, 0, 0], ![0, 59, 0], ![58, 9, 1]] where
  M :=![![![190366, 8916, -4221], ![-1380267, -45536, 26748], ![3375621, 57039, -54452]]]
  hmulB := by decide  
  f := ![![![16166900, 4148007, 784368]], ![![256488336, 65808251, 12444021]], ![![76558939, 19643037, 3714403]]]
  g := ![![![7376, 795, -4221], ![-49689, -4852, 26748], ![110743, 9273, -54452]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [41, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 58], [0, 1]]
 g := ![![[3, 36], [18, 21], [26], [7, 20], [54, 1]], ![[0, 23], [31, 38], [26], [25, 39], [49, 58]]]
 h' := ![![[54, 58], [29, 53], [1, 32], [8, 47], [28, 43], [0, 1]], ![[0, 1], [0, 6], [18, 27], [9, 12], [49, 16], [54, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [48, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [41, 5, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3862, 6955, 2805]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2692, -310, 2805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16166900, -4148007, -784368]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-16166900, -4148007, -784368]] 
 ![![59, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![-16166900, -4148007, -784368], ![-256488336, -65808251, -12444021], ![-1270902177, -326080518, -61660244]]]
  hmulB := by decide  
  f := ![![![-190366, -8916, 4221]], ![![-79855, -4064, 1836]], ![![-63667, -1269, 1066]]]
  g := ![![![2002340, -4148007, -784368], ![31767182, -65808251, -12444021], ![157406693, -326080518, -61660244]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![190366, 8916, -4221]] ![![-16166900, -4148007, -784368]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [32, 39, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22, 51], [26, 38, 10], [0, 1]]
 g := ![![[19, 57, 22], [23, 12], [48, 53, 47], [9, 4, 52], [1]], ![[8, 45, 7, 17], [38, 46], [54, 20, 3, 7], [42, 22, 22, 37], [21, 12, 11, 37]], ![[22, 21, 4, 50], [52, 13], [26, 39, 60, 40], [16, 19, 15, 7], [46, 57, 55, 24]]]
 h' := ![![[2, 22, 51], [56, 36, 49], [50, 15, 16], [17, 57, 13], [29, 22, 28], [0, 1]], ![[26, 38, 10], [43, 25, 38], [51, 31, 31], [35, 16, 46], [7, 37, 51], [2, 22, 51]], ![[0, 1], [47, 0, 35], [53, 15, 14], [37, 49, 2], [0, 2, 43], [26, 38, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 28], []]
 b := ![[], [1, 12, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [32, 39, 33, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6391946, -1981341, -418338]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104786, -32481, -6858]
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


def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-30, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-30, 1, 0]] 
 ![![67, 0, 0], ![37, 1, 0], ![45, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-30, 1, 0], ![0, -29, 3], ![327, 58, -30]]]
  hmulB := by decide  
  f := ![![![1501, -50, 0], ![3350, 0, 0]], ![![871, -29, 0], ![1944, 0, 0]], ![![1035, -15, -2], ![2310, 45, 0]]]
  g := ![![![1, 0, 0], ![-37, 67, 0], ![-45, 0, 67]], ![![-1, 1, 0], ![14, -29, 3], ![-7, 58, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-19, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-19, 1, 0]] 
 ![![67, 0, 0], ![48, 1, 0], ![20, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-19, 1, 0], ![0, -18, 3], ![327, 58, -19]]]
  hmulB := by decide  
  f := ![![![1217, -64, 0], ![4288, 0, 0]], ![![856, -45, 0], ![3016, 0, 0]], ![![382, -8, -2], ![1346, 45, 0]]]
  g := ![![![1, 0, 0], ![-48, 67, 0], ![-20, 0, 67]], ![![-1, 1, 0], ![12, -18, 3], ![-31, 58, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-30, 1, 0]] ![![67, 0, 0], ![-19, 1, 0]]
  ![![67, 0, 0], ![-11, -16, 1]] where
 M := ![![![4489, 0, 0], ![-1273, 67, 0]], ![![-2010, 67, 0], ![570, -48, 3]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![-8, 17, -1], ![67, 0, 0]]], ![![![-19, 17, -1], ![67, 0, 0]], ![![9, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-11, -16, 1]] ![![67, 0, 0], ![-19, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1273, 67, 0]], ![![-737, -1072, 67], ![536, 335, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-19, 1, 0]]], ![![![-11, -16, 1]], ![![8, 5, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![561301, -22358, -2628]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![561301, -22358, -2628]] 
 ![![71, 0, 0], ![0, 71, 0], ![25, 64, 1]] where
  M :=![![![561301, -22358, -2628], ![-859356, 386519, -67074], ![-7024614, -1583216, 408877]]]
  hmulB := by decide  
  f := ![![![-730226749, -187357234, -35428344]], ![![-11585068488, -2972427935, -562071702]], ![![-11508509549, -2952784898, -558357299]]]
  g := ![![![8831, 2054, -2628], ![11514, 65905, -67074], ![-242909, -390864, 408877]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [48, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 70], [0, 1]]
 g := ![![[41, 37], [70, 32], [20, 9], [37], [45], [1]], ![[0, 34], [0, 39], [58, 62], [37], [45], [1]]]
 h' := ![![[20, 70], [48, 26], [34, 48], [3, 68], [2, 45], [23, 20], [0, 1]], ![[0, 1], [0, 45], [0, 23], [14, 3], [50, 26], [68, 51], [20, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [67, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [48, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![353151, 279809, 100871]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30544, -86985, 100871]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![730226749, 187357234, 35428344]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![730226749, 187357234, 35428344]] 
 ![![71, 0, 0], ![21, 1, 0], ![59, 0, 1]] where
  M :=![![![730226749, 187357234, 35428344], ![11585068488, 2972427935, 562071702], ![57404126022, 14728409068, 2785070701]]]
  hmulB := by decide  
  f := ![![![-561301, 22358, 2628]], ![![-153915, 1169, 1722]], ![![-367495, 40878, -3575]]]
  g := ![![![-74571091, 187357234, 35428344], ![-1183072515, 2972427935, 562071702], ![-5862135715, 14728409068, 2785070701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![561301, -22358, -2628]] ![![730226749, 187357234, 35428344]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![4, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![4, 1, 0]] 
 ![![73, 0, 0], ![4, 1, 0], ![42, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![4, 1, 0], ![0, 5, 3], ![327, 58, 4]]]
  hmulB := by decide  
  f := ![![![197, 49, 0], ![-3577, 0, 0]], ![![4, 1, 0], ![-72, 0, 0]], ![![114, 25, -2], ![-2070, 49, 0]]]
  g := ![![![1, 0, 0], ![-4, 73, 0], ![-42, 0, 73]], ![![0, 1, 0], ![-2, 5, 3], ![-1, 58, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![15, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![15, 1, 0]] 
 ![![73, 0, 0], ![15, 1, 0], ![66, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![15, 1, 0], ![0, 16, 3], ![327, 58, 15]]]
  hmulB := by decide  
  f := ![![![466, 31, 0], ![-2263, 0, 0]], ![![90, 6, 0], ![-437, 0, 0]], ![![432, 18, -2], ![-2098, 49, 0]]]
  g := ![![![1, 0, 0], ![-15, 73, 0], ![-66, 0, 73]], ![![0, 1, 0], ![-6, 16, 3], ![-21, 58, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-20, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-20, 1, 0]] 
 ![![73, 0, 0], ![53, 1, 0], ![68, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-20, 1, 0], ![0, -19, 3], ![327, 58, -20]]]
  hmulB := by decide  
  f := ![![![661, -33, 0], ![2409, 0, 0]], ![![481, -24, 0], ![1753, 0, 0]], ![![596, -17, -2], ![2172, 49, 0]]]
  g := ![![![1, 0, 0], ![-53, 73, 0], ![-68, 0, 73]], ![![-1, 1, 0], ![11, -19, 3], ![-19, 58, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![4, 1, 0]] ![![73, 0, 0], ![15, 1, 0]]
  ![![73, 0, 0], ![-53, 31, 1]] where
 M := ![![![5329, 0, 0], ![1095, 73, 0]], ![![292, 73, 0], ![60, 20, 3]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![3, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-53, 31, 1]] ![![73, 0, 0], ![-20, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1460, 73, 0]], ![![-3869, 2263, 73], ![1387, -584, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-20, 1, 0]]], ![![![-53, 31, 1]], ![![19, -8, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-50, 31, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-50, 31, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![29, 31, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-50, 31, 1], ![327, 39, 93], ![10028, 1907, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -31, 79]], ![![-1, 0, 1], ![-30, -36, 93], ![124, 21, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [66, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 78], [0, 1]]
 g := ![![[41, 13], [4, 32], [1, 65], [50, 65], [5], [1]], ![[18, 66], [75, 47], [44, 14], [14, 14], [5], [1]]]
 h' := ![![[59, 78], [52, 31], [13, 43], [18, 12], [76, 12], [13, 59], [0, 1]], ![[0, 1], [64, 48], [22, 36], [15, 67], [73, 67], [18, 20], [59, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [44, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [66, 20, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2990, 1717, 588]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-178, -209, 588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-14, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-14, 1, 0]] 
 ![![79, 0, 0], ![65, 1, 0], ![71, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-14, 1, 0], ![0, -13, 3], ![327, 58, -14]]]
  hmulB := by decide  
  f := ![![![519, -37, 0], ![2923, 0, 0]], ![![421, -30, 0], ![2371, 0, 0]], ![![459, -24, -2], ![2585, 53, 0]]]
  g := ![![![1, 0, 0], ![-65, 79, 0], ![-71, 0, 79]], ![![-1, 1, 0], ![8, -13, 3], ![-31, 58, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-50, 31, 1]] ![![79, 0, 0], ![-14, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1106, 79, 0]], ![![-3950, 2449, 79], ![1027, -395, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-14, 1, 0]]], ![![![-50, 31, 1]], ![![13, -5, 1]]]]
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


lemma PB267I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB267I1 : PrimesBelowBoundCertificateInterval O 31 79 267 where
  m := 11
  g := ![1, 2, 3, 1, 3, 2, 1, 3, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB267I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
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
      exact NI79N1
  β := ![I41N1, I43N0, I43N1, I43N2, I53N0, I53N1, I59N1, I67N0, I67N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [], [I53N0, I53N0, I53N1], [I59N1], [], [I67N0, I67N1, I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
