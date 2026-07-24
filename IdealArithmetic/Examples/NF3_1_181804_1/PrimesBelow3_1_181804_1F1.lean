
import IdealArithmetic.Examples.NF3_1_181804_1.RI3_1_181804_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, -13, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, -13, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![25, 24, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, -13, 1], ![82, -16, -13], ![-1066, 134, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -24, 37]], ![![-1, -1, 1], ![11, 8, -13], ![-18, 14, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [13, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 36], [0, 1]]
 g := ![![[13, 28], [28], [4, 30], [34], [1]], ![[17, 9], [28], [3, 7], [34], [1]]]
 h' := ![![[16, 36], [9, 19], [22, 18], [23, 17], [24, 16], [0, 1]], ![[0, 1], [17, 18], [14, 19], [36, 20], [21, 21], [16, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [32, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [13, 21, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![177, 53, -24]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, 17, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![16, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 1, 0], ![0, 13, 1], ![82, -4, 13]]]
  hmulB := by decide  
  f := ![![![157, 12, 0], ![-444, 0, 0]], ![![39, 3, 0], ![-110, 0, 0]], ![![70, 5, 0], ![-198, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 37, 0], ![-16, 0, 37]], ![![0, 1, 0], ![-5, 13, 1], ![-2, -4, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-12, -13, 1]] ![![37, 0, 0], ![13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![481, 37, 0]], ![![-444, -481, 37], ![-74, -185, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![13, 1, 0]]], ![![![-12, -13, 1]], ![![-2, -5, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 8, 2]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 8, 2]] 
 ![![41, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![41, 8, 2], ![164, 33, 8], ![656, 132, 33]]]
  hmulB := by decide  
  f := ![![![33, 0, -2]], ![![-4, 1, 0]], ![![0, -4, 1]]]
  g := ![![![1, 8, 2], ![4, 33, 8], ![16, 132, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![0, 18, 1], ![82, -4, 18]]]
  hmulB := by decide  
  f := ![![![181, 10, 0], ![-410, 0, 0]], ![![90, 5, 0], ![-204, 0, 0]], ![![8, 0, 0], ![-18, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-8, 18, 1], ![2, -4, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![0, -18, 1], ![82, -4, -18]]]
  hmulB := by decide  
  f := ![![![433, -24, 0], ![984, 0, 0]], ![![235, -13, 0], ![534, 0, 0]], ![![44, -2, 0], ![100, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-4, 0, 41]], ![![-1, 1, 0], ![10, -18, 1], ![6, -4, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 8, 2]] ![![41, 0, 0], ![18, 1, 0]]
  ![![41, 0, 0], ![0, 18, 1]] where
 M := ![![![1681, 328, 82], ![902, 177, 44]]]
 hmul := by decide  
 g := ![![![![41, -10, 1], ![41, 0, 0]], ![![22, 3, 1], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![0, 18, 1]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![0, 738, 41], ![82, -328, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-18, 1, 0]]], ![![![0, 18, 1]], ![![2, -8, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, 1, 0]] 
 ![![43, 0, 0], ![23, 1, 0], ![30, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, 1, 0], ![0, -20, 1], ![82, -4, -20]]]
  hmulB := by decide  
  f := ![![![721, -36, 0], ![1548, 0, 0]], ![![381, -19, 0], ![818, 0, 0]], ![![530, -26, 0], ![1138, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 43, 0], ![-30, 0, 43]], ![![-1, 1, 0], ![10, -20, 1], ![18, -4, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![43, 0, 0], ![40, 1, 0], ![34, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![82, -4, -3]]]
  hmulB := by decide  
  f := ![![![13, 3, 1]], ![![14, 3, 1]], ![![16, 4, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![8, -4, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-20, 1, 0]] ![![43, 0, 0], ![-20, 1, 0]]
  ![![13, 3, 1]] where
 M := ![![![1849, 0, 0], ![-860, 43, 0]], ![![-860, 43, 0], ![400, -40, 1]]]
 hmul := by decide  
 g := ![![![![-129, 43, 0]], ![![60, -23, 1]]], ![![![60, -23, 1]], ![![-26, 12, -1]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![13, 3, 1]] ![![-3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-16, -11, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-16, -11, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![31, 36, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-16, -11, 1], ![82, -20, -11], ![-902, 126, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -36, 47]], ![![-1, -1, 1], ![9, 8, -11], ![-6, 18, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [40, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[42, 8], [42, 17], [38, 24], [16, 3], [1]], ![[44, 39], [11, 30], [44, 23], [5, 44], [1]]]
 h' := ![![[12, 46], [12, 33], [31, 8], [18, 27], [7, 12], [0, 1]], ![[0, 1], [32, 14], [33, 39], [13, 20], [10, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [11, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [40, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-978, 720, 67]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65, -36, 67]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![11, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![11, 1, 0]] 
 ![![47, 0, 0], ![11, 1, 0], ![20, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![11, 1, 0], ![0, 11, 1], ![82, -4, 11]]]
  hmulB := by decide  
  f := ![![![221, 20, 0], ![-940, 0, 0]], ![![55, 5, 0], ![-234, 0, 0]], ![![80, 7, 0], ![-340, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 47, 0], ![-20, 0, 47]], ![![0, 1, 0], ![-3, 11, 1], ![-2, -4, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-16, -11, 1]] ![![47, 0, 0], ![11, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![517, 47, 0]], ![![-752, -517, 47], ![-94, -141, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![11, 1, 0]]], ![![![-16, -11, 1]], ![![-2, -3, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-20, -20, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-20, -20, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![33, 33, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-20, -20, 1], ![82, -24, -20], ![-1640, 162, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -33, 53]], ![![-1, -1, 1], ![14, 12, -20], ![-16, 18, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [9, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 52], [0, 1]]
 g := ![![[2, 6], [28], [15, 17], [9], [35, 1]], ![[0, 47], [28], [27, 36], [9], [17, 52]]]
 h' := ![![[35, 52], [6, 18], [24, 44], [34, 32], [3, 50], [0, 1]], ![[0, 1], [0, 35], [27, 9], [41, 21], [4, 3], [35, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [43, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [9, 18, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2789, -20, 107]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -67, 107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, 1, 0]] 
 ![![53, 0, 0], ![20, 1, 0], ![24, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, 1, 0], ![0, 20, 1], ![82, -4, 20]]]
  hmulB := by decide  
  f := ![![![121, 6, 0], ![-318, 0, 0]], ![![20, 1, 0], ![-52, 0, 0]], ![![48, 2, 0], ![-126, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 53, 0], ![-24, 0, 53]], ![![0, 1, 0], ![-8, 20, 1], ![-6, -4, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-20, -20, 1]] ![![53, 0, 0], ![20, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1060, 53, 0]], ![![-1060, -1060, 53], ![-318, -424, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![20, 1, 0]]], ![![![-20, -20, 1]], ![![-6, -8, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![32, 21, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![32, 21, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![32, 21, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![32, 21, 1], ![82, 28, 21], ![1722, -2, 28]]]
  hmulB := by decide  
  f := ![![![-31, -21, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -21, 59]], ![![0, 0, 1], ![-10, -7, 21], ![14, -10, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [24, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 58], [0, 1]]
 g := ![![[43, 5], [37, 36], [25], [50, 22], [30, 1]], ![[16, 54], [55, 23], [25], [2, 37], [1, 58]]]
 h' := ![![[30, 58], [56, 8], [36, 6], [39, 54], [47, 50], [0, 1]], ![[0, 1], [1, 51], [39, 53], [7, 5], [13, 9], [30, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [4, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [24, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-438, 793, -128]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62, 59, -128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-21, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-21, 1, 0]] 
 ![![59, 0, 0], ![38, 1, 0], ![31, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-21, 1, 0], ![0, -21, 1], ![82, -4, -21]]]
  hmulB := by decide  
  f := ![![![1114, -53, 0], ![3127, 0, 0]], ![![736, -35, 0], ![2066, 0, 0]], ![![596, -28, 0], ![1673, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 59, 0], ![-31, 0, 59]], ![![-1, 1, 0], ![13, -21, 1], ![15, -4, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![32, 21, 1]] ![![59, 0, 0], ![-21, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1239, 59, 0]], ![![1888, 1239, 59], ![-590, -413, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-21, 1, 0]]], ![![![32, 21, 1]], ![![-10, -7, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-12, -17, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-12, -17, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![49, 44, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-12, -17, 1], ![82, -16, -17], ![-1394, 150, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -44, 61]], ![![-1, -1, 1], ![15, 12, -17], ![-10, 14, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [50, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 60], [0, 1]]
 g := ![![[31, 9], [16], [33, 52], [32, 5], [36, 1]], ![[50, 52], [16], [14, 9], [29, 56], [11, 60]]]
 h' := ![![[36, 60], [2, 3], [58, 4], [47, 33], [30, 26], [0, 1]], ![[0, 1], [49, 58], [19, 57], [15, 28], [51, 35], [36, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [43, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [50, 25, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![214, 49, -28]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, 21, -28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![17, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![17, 1, 0]] 
 ![![61, 0, 0], ![17, 1, 0], ![16, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![17, 1, 0], ![0, 17, 1], ![82, -4, 17]]]
  hmulB := by decide  
  f := ![![![239, 14, 0], ![-854, 0, 0]], ![![51, 3, 0], ![-182, 0, 0]], ![![56, 3, 0], ![-200, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 61, 0], ![-16, 0, 61]], ![![0, 1, 0], ![-5, 17, 1], ![-2, -4, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-12, -17, 1]] ![![61, 0, 0], ![17, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1037, 61, 0]], ![![-732, -1037, 61], ![-122, -305, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![17, 1, 0]]], ![![![-12, -17, 1]], ![![-2, -5, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![33, -30, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![33, -30, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![33, 37, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![33, -30, 1], ![82, 29, -30], ![-2460, 202, 29]]]
  hmulB := by decide  
  f := ![![![-32, 30, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -37, 67]], ![![0, -1, 1], ![16, 17, -30], ![-51, -13, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [52, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 66], [0, 1]]
 g := ![![[58, 35], [9, 49], [37], [23], [1], [1]], ![[23, 32], [27, 18], [37], [23], [1], [1]]]
 h' := ![![[66, 66], [1, 13], [52, 7], [57, 38], [39, 36], [15, 66], [0, 1]], ![[0, 1], [55, 54], [45, 60], [19, 29], [3, 31], [16, 1], [66, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [56, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [52, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3170, -13, 360]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-130, -199, 360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![30, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![30, 1, 0]] 
 ![![67, 0, 0], ![30, 1, 0], ![38, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![30, 1, 0], ![0, 30, 1], ![82, -4, 30]]]
  hmulB := by decide  
  f := ![![![601, 20, 0], ![-1340, 0, 0]], ![![270, 9, 0], ![-602, 0, 0]], ![![314, 10, 0], ![-700, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 67, 0], ![-38, 0, 67]], ![![0, 1, 0], ![-14, 30, 1], ![-14, -4, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![33, -30, 1]] ![![67, 0, 0], ![30, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2010, 67, 0]], ![![2211, -2010, 67], ![1072, -871, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![30, 1, 0]]], ![![![33, -30, 1]], ![![16, -13, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![35, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![35, 1, 0]] 
 ![![71, 0, 0], ![35, 1, 0], ![53, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![35, 1, 0], ![0, 35, 1], ![82, -4, 35]]]
  hmulB := by decide  
  f := ![![![526, 15, 0], ![-1065, 0, 0]], ![![210, 6, 0], ![-425, 0, 0]], ![![368, 10, 0], ![-745, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 71, 0], ![-53, 0, 71]], ![![0, 1, 0], ![-18, 35, 1], ![-23, -4, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-18, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-18, 1, 0]] 
 ![![71, 0, 0], ![53, 1, 0], ![31, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-18, 1, 0], ![0, -18, 1], ![82, -4, -18]]]
  hmulB := by decide  
  f := ![![![109, -6, 0], ![426, 0, 0]], ![![91, -5, 0], ![356, 0, 0]], ![![77, -4, 0], ![302, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 71, 0], ![-31, 0, 71]], ![![-1, 1, 0], ![13, -18, 1], ![12, -4, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-17, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-17, 1, 0]] 
 ![![71, 0, 0], ![54, 1, 0], ![66, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-17, 1, 0], ![0, -17, 1], ![82, -4, -17]]]
  hmulB := by decide  
  f := ![![![919, -54, 0], ![3834, 0, 0]], ![![698, -41, 0], ![2912, 0, 0]], ![![872, -51, 0], ![3638, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 71, 0], ![-66, 0, 71]], ![![-1, 1, 0], ![12, -17, 1], ![20, -4, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![35, 1, 0]] ![![71, 0, 0], ![-18, 1, 0]]
  ![![71, 0, 0], ![9, 17, 1]] where
 M := ![![![5041, 0, 0], ![-1278, 71, 0]], ![![2485, 71, 0], ![-630, 17, 1]]]
 hmul := by decide  
 g := ![![![![62, -17, -1], ![71, 0, 0]], ![![-18, 1, 0], ![0, 0, 0]]], ![![![26, -16, -1], ![71, 0, 0]], ![![-9, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![9, 17, 1]] ![![71, 0, 0], ![-17, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1207, 71, 0]], ![![639, 1207, 71], ![-71, -284, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-17, 1, 0]]], ![![![9, 17, 1]], ![![-1, -4, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![36, -18, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![36, -18, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![36, 55, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![36, -18, 1], ![82, 32, -18], ![-1476, 154, 32]]]
  hmulB := by decide  
  f := ![![![-35, 18, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -55, 73]], ![![0, -1, 1], ![10, 14, -18], ![-36, -22, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [21, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 72], [0, 1]]
 g := ![![[13, 70], [37], [64], [59, 4], [69], [1]], ![[29, 3], [37], [64], [62, 69], [69], [1]]]
 h' := ![![[19, 72], [45, 17], [47, 16], [2, 65], [14, 2], [52, 19], [0, 1]], ![[0, 1], [3, 56], [59, 57], [69, 8], [52, 71], [48, 54], [19, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [62, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [21, 54, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-524, 262, -47]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 39, -47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![18, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![18, 1, 0]] 
 ![![73, 0, 0], ![18, 1, 0], ![41, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![18, 1, 0], ![0, 18, 1], ![82, -4, 18]]]
  hmulB := by decide  
  f := ![![![667, 37, 0], ![-2701, 0, 0]], ![![162, 9, 0], ![-656, 0, 0]], ![![383, 21, 0], ![-1551, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 73, 0], ![-41, 0, 73]], ![![0, 1, 0], ![-5, 18, 1], ![-8, -4, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![36, -18, 1]] ![![73, 0, 0], ![18, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1314, 73, 0]], ![![2628, -1314, 73], ![730, -292, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![18, 1, 0]]], ![![![36, -18, 1]], ![![10, -4, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 6, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-39, 6, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![40, 6, 1]] where
  M :=![![![-39, 6, 1], ![82, -43, 6], ![492, 58, -43]]]
  hmulB := by decide  
  f := ![![![19, 4, 1]], ![![82, 15, 4]], ![![20, 4, 1]]]
  g := ![![![-1, 0, 1], ![-2, -1, 6], ![28, 4, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [35, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 78], [0, 1]]
 g := ![![[23, 18], [62, 5], [17, 4], [44, 50], [67], [1]], ![[69, 61], [66, 74], [36, 75], [5, 29], [67], [1]]]
 h' := ![![[64, 78], [42, 27], [37, 20], [40, 77], [65, 45], [44, 64], [0, 1]], ![[0, 1], [32, 52], [53, 59], [70, 2], [22, 34], [32, 15], [64, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [37, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [35, 15, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363, 327, 15]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 3, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -4, -1]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-19, -4, -1]] 
 ![![79, 0, 0], ![73, 1, 0], ![43, 0, 1]] where
  M :=![![![-19, -4, -1], ![-82, -15, -4], ![-328, -66, -15]]]
  hmulB := by decide  
  f := ![![![39, -6, -1]], ![![35, -5, -1]], ![![15, -4, 0]]]
  g := ![![![4, -4, -1], ![15, -15, -4], ![65, -66, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-39, 6, 1]] ![![-19, -4, -1]]
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


lemma PB121I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB121I1 : PrimesBelowBoundCertificateInterval O 31 79 121 where
  m := 11
  g := ![2, 3, 3, 2, 2, 2, 2, 2, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB121I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
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
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N1
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
      exact NI61N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N0, I43N1, I47N1, I53N1, I59N1, I61N1, I67N1, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N0, I43N0, I43N1], [I47N1], [I53N1], [I59N1], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
