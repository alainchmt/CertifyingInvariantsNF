
import IdealArithmetic.Examples.NF3_1_280904_4.RI3_1_280904_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![8, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![8, 1, 0]] 
 ![![37, 0, 0], ![8, 1, 0], ![24, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![8, 1, 0], ![1, 8, 2], ![-99, -7, 9]]]
  hmulB := by decide  
  f := ![![![-401, -3468, -868], ![-148, 16058, 0]], ![![-85, -743, -186], ![-36, 3441, 0]], ![![-256, -2249, -563], ![-115, 10416, 0]]]
  g := ![![![1, 0, 0], ![-8, 37, 0], ![-24, 0, 37]], ![![0, 1, 0], ![-3, 8, 2], ![-7, -7, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![1, 14, 2], ![-99, -7, 15]]]
  hmulB := by decide  
  f := ![![![179, 3467, 496], ![185, -9176, 0]], ![![65, 1300, 186], ![75, -3441, 0]], ![![148, 2998, 429], ![178, -7936, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-32, 0, 37]], ![![0, 1, 0], ![-7, 14, 2], ![-13, -7, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![8, 1, 0]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0], ![1, 11, 1]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![296, 37, 0], ![113, 22, 2]]]
 hmul := by decide  
 g := ![![![![36, -11, -1], ![37, 0, 0]], ![![13, -10, -1], ![37, 0, 0]]], ![![![7, -10, -1], ![37, 0, 0]], ![![3, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![1, 11, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![37, 407, 37], ![-74, 148, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![1, 11, 1]], ![![-2, 4, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![14, 11, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 11, 1], ![-88, 7, 23], ![-1142, -130, 18]]]
  hmulB := by decide  
  f := ![![![-13, -11, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -11, 41]], ![![0, 0, 1], ![-10, -6, 23], ![-34, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [39, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40], [0, 1]]
 g := ![![[1, 20], [25], [9], [16, 4], [1]], ![[0, 21], [25], [9], [24, 37], [1]]]
 h' := ![![[2, 40], [11, 15], [17, 5], [32, 3], [2, 2], [0, 1]], ![[0, 1], [0, 26], [27, 36], [38, 38], [6, 39], [2, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [7, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [39, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-606, -277, -96]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 19, -96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![1, 18, 2], ![-99, -7, 19]]]
  hmulB := by decide  
  f := ![![![211, 6041, 672], ![287, -13776, 0]], ![![93, 2643, 294], ![124, -6027, 0]], ![![121, 3389, 377], ![155, -7728, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-23, 0, 41]], ![![0, 1, 0], ![-9, 18, 2], ![-10, -7, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![14, 11, 1]] ![![41, 0, 0], ![18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![738, 41, 0]], ![![574, 451, 41], ![164, 205, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![18, 1, 0]]], ![![![14, 11, 1]], ![![4, 5, 1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [2, 9, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 8, 31], [15, 34, 12], [0, 1]]
 g := ![![[19, 36, 36], [40, 6, 35], [27, 41], [4, 20, 1], []], ![[18, 32, 41, 9], [27, 37, 38, 38], [24, 17], [20, 0, 23, 17], [22, 15]], ![[27, 29, 31, 26], [2, 39, 34, 7], [16, 21], [6, 10, 28, 37], [41, 15]]]
 h' := ![![[5, 8, 31], [6, 29, 6], [10, 31, 11], [35, 10, 27], [0, 0, 1], [0, 1]], ![[15, 34, 12], [37, 32, 28], [42, 39, 2], [2, 40, 24], [24, 24, 34], [5, 8, 31]], ![[0, 1], [9, 25, 9], [27, 16, 30], [4, 36, 35], [14, 19, 8], [15, 34, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 34], []]
 b := ![[], [16, 5, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [2, 9, 23, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![620705, 52503, 4171]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14435, 1221, 97]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, -11, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, -11, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![3, 36, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, -11, 1], ![-110, -4, -21], ![1036, 24, -15]]]
  hmulB := by decide  
  f := ![![![-2, 11, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -36, 47]], ![![0, -1, 1], ![-1, 16, -21], ![23, 12, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [38, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 46], [0, 1]]
 g := ![![[12, 9], [24, 21], [45, 37], [35, 8], [1]], ![[44, 38], [36, 26], [46, 10], [6, 39], [1]]]
 h' := ![![[14, 46], [28, 3], [29, 31], [33, 32], [9, 14], [0, 1]], ![[0, 1], [23, 44], [40, 16], [11, 15], [17, 33], [14, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [11, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [38, 33, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-215681, -230041, -24220]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3043, 13657, -24220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![21, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![21, 1, 0]] 
 ![![47, 0, 0], ![21, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![21, 1, 0], ![1, 21, 2], ![-99, -7, 22]]]
  hmulB := by decide  
  f := ![![![16, 755, 72], ![47, -1692, 0]], ![![-5, 335, 32], ![48, -752, 0]], ![![6, 241, 23], ![13, -540, 0]]]
  g := ![![![1, 0, 0], ![-21, 47, 0], ![-15, 0, 47]], ![![0, 1, 0], ![-10, 21, 2], ![-6, -7, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![3, -11, 1]] ![![47, 0, 0], ![21, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![987, 47, 0]], ![![141, -517, 47], ![-47, -235, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![21, 1, 0]]], ![![![3, -11, 1]], ![![-1, -5, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![26, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![26, 1, 0]] 
 ![![53, 0, 0], ![26, 1, 0], ![7, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![26, 1, 0], ![1, 26, 2], ![-99, -7, 27]]]
  hmulB := by decide  
  f := ![![![-554, -22530, -1734], ![-636, 45951, 0]], ![![-269, -11044, -850], ![-317, 22525, 0]], ![![-82, -2976, -229], ![-66, 6069, 0]]]
  g := ![![![1, 0, 0], ![-26, 53, 0], ![-7, 0, 53]], ![![0, 1, 0], ![-13, 26, 2], ![-2, -7, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-26, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-26, 1, 0]] 
 ![![53, 0, 0], ![27, 1, 0], ![7, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-26, 1, 0], ![1, -26, 2], ![-99, -7, -25]]]
  hmulB := by decide  
  f := ![![![-19, 1870, -144], ![106, 3816, 0]], ![![-9, 935, -72], ![54, 1908, 0]], ![![-3, 247, -19], ![13, 504, 0]]]
  g := ![![![1, 0, 0], ![-27, 53, 0], ![-7, 0, 53]], ![![-1, 1, 0], ![13, -26, 2], ![5, -7, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1208, 435, 80]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![1208, 435, 80]] 
 ![![53, 0, 0], ![52, 1, 0], ![0, 0, 1]] where
  M :=![![![1208, 435, 80], ![-7485, 648, 950], ![-47305, -7285, 1083]]]
  hmulB := by decide  
  f := ![![![-7622534, 1053905, -361410]], ![![-6783741, 937932, -321640]], ![![-1607205, 222215, -76203]]]
  g := ![![![-404, 435, 80], ![-777, 648, 950], ![6255, -7285, 1083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![26, 1, 0]] ![![53, 0, 0], ![-26, 1, 0]]
  ![![7622534, -1053905, 361410]] where
 M := ![![![2809, 0, 0], ![-1378, 53, 0]], ![![1378, 53, 0], ![-675, 0, 2]]]
 hmul := by decide  
 g := ![![![![-64024, -23055, -4240]], ![![38893, 10662, 1130]]], ![![![-23923, -11958, -3030]], ![![17170, 5815, 978]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![7622534, -1053905, 361410]] ![![1208, 435, 80]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![26, 23, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![26, 23, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![26, 23, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![26, 23, 1], ![-76, 19, 47], ![-2330, -214, 42]]]
  hmulB := by decide  
  f := ![![![-25, -23, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -23, 59]], ![![0, 0, 1], ![-22, -18, 47], ![-58, -20, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [44, 6, 1] where
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
 g := ![![[35, 28], [20, 7], [41], [53, 5], [53, 1]], ![[44, 31], [37, 52], [41], [23, 54], [47, 58]]]
 h' := ![![[53, 58], [5, 38], [42, 19], [28, 10], [28, 51], [0, 1]], ![[0, 1], [13, 21], [46, 40], [27, 49], [17, 8], [53, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [11, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [44, 6, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-298, -1253, -193]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![80, 54, -193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![12, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![12, 1, 0]] 
 ![![59, 0, 0], ![12, 1, 0], ![17, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![12, 1, 0], ![1, 12, 2], ![-99, -7, 13]]]
  hmulB := by decide  
  f := ![![![74, 1019, 170], ![59, -5015, 0]], ![![5, 203, 34], ![60, -1003, 0]], ![![14, 293, 49], ![53, -1445, 0]]]
  g := ![![![1, 0, 0], ![-12, 59, 0], ![-17, 0, 59]], ![![0, 1, 0], ![-3, 12, 2], ![-4, -7, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![26, 23, 1]] ![![59, 0, 0], ![12, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![708, 59, 0]], ![![1534, 1357, 59], ![236, 295, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![12, 1, 0]]], ![![![26, 23, 1]], ![![4, 5, 1]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [16, 31, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 0, 10], [1, 60, 51], [0, 1]]
 g := ![![[10, 53, 56], [40, 1], [24, 36, 49], [58, 14, 27], [1]], ![[48, 37, 2, 37], [1, 19], [42, 38, 44, 26], [29, 9, 41, 53], [59, 33, 27, 24]], ![[3, 58, 10, 59], [46, 56], [53, 24, 53, 28], [3, 40, 29, 55], [40, 59, 39, 37]]]
 h' := ![![[23, 0, 10], [50, 42, 42], [43, 8, 1], [48, 3, 54], [45, 30, 24], [0, 1]], ![[1, 60, 51], [33, 8, 12], [54, 6, 18], [47, 19, 37], [60, 22, 32], [23, 0, 10]], ![[0, 1], [32, 11, 7], [6, 47, 42], [0, 39, 31], [32, 9, 5], [1, 60, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 38], []]
 b := ![[], [1, 60, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [16, 31, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72407, -13359, 1220]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1187, -219, 20]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34, 5, -2]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-34, 5, -2]] 
 ![![67, 0, 0], ![0, 67, 0], ![17, 31, 1]] where
  M :=![![![-34, 5, -2], ![203, -20, 8], ![-389, 71, -15]]]
  hmulB := by decide  
  f := ![![![4, 1, 0]], ![![1, 4, 2]], ![![0, 2, 1]]]
  g := ![![![0, 1, -2], ![1, -4, 8], ![-2, 8, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [38, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 66], [0, 1]]
 g := ![![[37, 14], [16, 33], [35], [64], [1], [1]], ![[51, 53], [49, 34], [35], [64], [1], [1]]]
 h' := ![![[1, 66], [62, 58], [36, 10], [48, 13], [66, 59], [29, 1], [0, 1]], ![[0, 1], [53, 9], [46, 57], [61, 54], [58, 8], [30, 66], [1, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [63, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [38, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11228, 55, 983]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-417, -454, 983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![4, 1, 0]] 
 ![![67, 0, 0], ![4, 1, 0], ![26, 0, 1]] where
  M :=![![![4, 1, 0], ![1, 4, 2], ![-99, -7, 5]]]
  hmulB := by decide  
  f := ![![![-34, 5, -2]], ![![1, 0, 0]], ![![-19, 3, -1]]]
  g := ![![![0, 1, 0], ![-1, 4, 2], ![-3, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-34, 5, -2]] ![![4, 1, 0]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4140, 755, -44]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![4140, 755, -44]] 
 ![![71, 0, 0], ![7, 1, 0], ![47, 0, 1]] where
  M :=![![![4140, 755, -44], ![5111, 4448, 1466], ![-72413, -2953, 5203]]]
  hmulB := by decide  
  f := ![![![27472042, -3798333, 1302542]], ![![838793, -115973, 39770]], ![![22509665, -3112226, 1067259]]]
  g := ![![![13, 755, -44], ![-1337, 4448, 1466], ![-4173, -2953, 5203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![31, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![31, 1, 0]] 
 ![![71, 0, 0], ![31, 1, 0], ![17, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![31, 1, 0], ![1, 31, 2], ![-99, -7, 32]]]
  hmulB := by decide  
  f := ![![![-133, -5114, -330], ![-71, 11715, 0]], ![![-72, -2232, -144], ![1, 5112, 0]], ![![-48, -1225, -79], ![20, 2805, 0]]]
  g := ![![![1, 0, 0], ![-31, 71, 0], ![-17, 0, 71]], ![![0, 1, 0], ![-14, 31, 2], ![-6, -7, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![32, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![32, 1, 0]] 
 ![![71, 0, 0], ![32, 1, 0], ![21, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![32, 1, 0], ![1, 32, 2], ![-99, -7, 33]]]
  hmulB := by decide  
  f := ![![![57, 3838, 240], ![142, -8520, 0]], ![![22, 1727, 108], ![72, -3834, 0]], ![![11, 1135, 71], ![55, -2520, 0]]]
  g := ![![![1, 0, 0], ![-32, 71, 0], ![-21, 0, 71]], ![![0, 1, 0], ![-15, 32, 2], ![-8, -7, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![4140, 755, -44]] ![![71, 0, 0], ![31, 1, 0]]
  ![![71, 0, 0], ![38, 19, 1]] where
 M := ![![![293940, 53605, -3124], ![133451, 27853, 102]]]
 hmul := by decide  
 g := ![![![![3152, 261, -70], ![1846, 0, 0]], ![![1407, 156, -11], ![883, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![38, 19, 1]] ![![71, 0, 0], ![32, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2272, 71, 0]], ![![2698, 1349, 71], ![1136, 639, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![32, 1, 0]]], ![![![38, 19, 1]], ![![16, 9, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73397, 10148, -3480]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-73397, 10148, -3480]] 
 ![![73, 0, 0], ![13, 1, 0], ![62, 0, 1]] where
  M :=![![![-73397, 10148, -3480], ![354668, -49037, 16816], ![-820212, 113404, -38889]]]
  hmulB := by decide  
  f := ![![![1771, 348, -8]], ![![331, 87, 8]], ![![1038, 268, 23]]]
  g := ![![![143, 10148, -3480], ![-691, -49037, 16816], ![1598, 113404, -38889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 4, 2]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-3, 4, 2]] 
 ![![73, 0, 0], ![66, 1, 0], ![49, 0, 1]] where
  M :=![![![-3, 4, 2], ![-194, -17, 10], ![-502, -134, -13]]]
  hmulB := by decide  
  f := ![![![1561, -216, 74]], ![![1308, -181, 62]], ![![1287, -178, 61]]]
  g := ![![![-5, 4, 2], ![6, -17, 10], ![123, -134, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-73397, 10148, -3480]] ![![-3, 4, 2]]
  ![![-1561, 216, -74]] where
 M := ![![![-1561, 216, -74]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-1561, 216, -74]] ![![-3, 4, 2]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![14, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![14, 1, 0]] 
 ![![79, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![14, 1, 0], ![1, 14, 2], ![-99, -7, 15]]]
  hmulB := by decide  
  f := ![![![-858, -12611, -1802], ![-237, 71179, 0]], ![![-159, -2226, -318], ![1, 12561, 0]], ![![-238, -3353, -479], ![-7, 18921, 0]]]
  g := ![![![1, 0, 0], ![-14, 79, 0], ![-21, 0, 79]], ![![0, 1, 0], ![-3, 14, 2], ![-4, -7, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![19, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![19, 1, 0]] 
 ![![79, 0, 0], ![19, 1, 0], ![57, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![19, 1, 0], ![1, 19, 2], ![-99, -7, 20]]]
  hmulB := by decide  
  f := ![![![-1478, -31341, -3300], ![-711, 130350, 0]], ![![-358, -7522, -792], ![-157, 31284, 0]], ![![-1064, -22613, -2381], ![-523, 94050, 0]]]
  g := ![![![1, 0, 0], ![-19, 79, 0], ![-57, 0, 79]], ![![0, 1, 0], ![-6, 19, 2], ![-14, -7, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-34, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-34, 1, 0]] 
 ![![79, 0, 0], ![45, 1, 0], ![15, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-34, 1, 0], ![1, -34, 2], ![-99, -7, -33]]]
  hmulB := by decide  
  f := ![![![1887, -92999, 5472], ![-1975, -216144, 0]], ![![1083, -52958, 3116], ![-1105, -123082, 0]], ![![391, -17659, 1039], ![-299, -41040, 0]]]
  g := ![![![1, 0, 0], ![-45, 79, 0], ![-15, 0, 79]], ![![-1, 1, 0], ![19, -34, 2], ![9, -7, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![14, 1, 0]] ![![79, 0, 0], ![19, 1, 0]]
  ![![79, 0, 0], ![15, -23, 1]] where
 M := ![![![6241, 0, 0], ![1501, 79, 0]], ![![1106, 79, 0], ![267, 33, 2]]]
 hmul := by decide  
 g := ![![![![64, 23, -1], ![79, 0, 0]], ![![4, 24, -1], ![79, 0, 0]]], ![![![-1, 24, -1], ![79, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![15, -23, 1]] ![![79, 0, 0], ![-34, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2686, 79, 0]], ![![1185, -1817, 79], ![-632, 790, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-34, 1, 0]]], ![![![15, -23, 1]], ![![-8, 10, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB150I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB150I1 : PrimesBelowBoundCertificateInterval O 31 79 150 where
  m := 11
  g := ![3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB150I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N0, I37N1, I41N1, I47N1, I53N0, I53N1, I53N2, I59N1, I67N1, I71N0, I71N1, I71N2, I73N0, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N1], [I41N1], [], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [], [I67N1], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
