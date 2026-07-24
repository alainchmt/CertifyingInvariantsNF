
import IdealArithmetic.Examples.NF3_1_469300_2.RI3_1_469300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-48, -11, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-48, -11, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![26, 26, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-48, -11, 1], ![380, 47, -11], ![-4180, -665, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -26, 37]], ![![-2, -1, 1], ![18, 9, -11], ![-146, -51, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [26, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 36], [0, 1]]
 g := ![![[23, 10], [1], [12, 3], [36], [1]], ![[0, 27], [1], [31, 34], [36], [1]]]
 h' := ![![[31, 36], [8, 26], [21, 36], [36, 22], [11, 31], [0, 1]], ![[0, 1], [0, 11], [27, 1], [15, 15], [10, 6], [31, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [36, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [26, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![786, 564, 90]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -48, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![0, 11, 1], ![380, 95, 11]]]
  hmulB := by decide  
  f := ![![![166, 15, 0], ![-555, 0, 0]], ![![44, 4, 0], ![-147, 0, 0]], ![![114, 10, 0], ![-381, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-4, 11, 1], ![-26, 95, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-48, -11, 1]] ![![37, 0, 0], ![11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![407, 37, 0]], ![![-1776, -407, 37], ![-148, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![11, 1, 0]]], ![![![-48, -11, 1]], ![![-4, -2, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-62, -22, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-62, -22, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![20, 19, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-62, -22, 1], ![380, 33, -22], ![-8360, -1710, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -19, 41]], ![![-2, -1, 1], ![20, 11, -22], ![-220, -57, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40], [0, 1]]
 g := ![![[15, 40], [37], [18], [2, 20], [1]], ![[0, 1], [37], [18], [15, 21], [1]]]
 h' := ![![[15, 40], [29, 9], [22, 23], [2, 10], [1, 15], [0, 1]], ![[0, 1], [0, 32], [39, 18], [29, 31], [21, 26], [15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [16, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4545, 2232, 931]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-565, -377, 931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-19, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-19, 1, 0]] 
 ![![41, 0, 0], ![22, 1, 0], ![8, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-19, 1, 0], ![0, -19, 1], ![380, 95, -19]]]
  hmulB := by decide  
  f := ![![![400, -21, 0], ![861, 0, 0]], ![![210, -11, 0], ![452, 0, 0]], ![![104, -5, 0], ![224, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 41, 0], ![-8, 0, 41]], ![![-1, 1, 0], ![10, -19, 1], ![-38, 95, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-62, -22, 1]] ![![41, 0, 0], ![-19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-779, 41, 0]], ![![-2542, -902, 41], ![1558, 451, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-19, 1, 0]]], ![![![-62, -22, 1]], ![![38, 11, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-81, -10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-81, -10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 33, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-81, -10, 1], ![380, 14, -10], ![-3800, -570, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -33, 43]], ![![-2, -1, 1], ![10, 8, -10], ![-90, -24, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 36, 1] where
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
 g := ![![[37, 10], [12, 15], [21], [40, 6], [1]], ![[21, 33], [31, 28], [21], [39, 37], [1]]]
 h' := ![![[7, 42], [29, 15], [20, 31], [25, 8], [6, 7], [0, 1]], ![[0, 1], [5, 28], [22, 12], [38, 35], [12, 36], [7, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [16, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [37, 36, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1069, 98, 188]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -142, 188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![0, 10, 1], ![380, 95, 10]]]
  hmulB := by decide  
  f := ![![![111, 11, 0], ![-473, 0, 0]], ![![10, 1, 0], ![-42, 0, 0]], ![![73, 7, 0], ![-311, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-29, 0, 43]], ![![0, 1, 0], ![-3, 10, 1], ![-20, 95, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-81, -10, 1]] ![![43, 0, 0], ![10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![430, 43, 0]], ![![-3483, -430, 43], ![-430, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![10, 1, 0]]], ![![![-81, -10, 1]], ![![-10, -2, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-22, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-22, 1, 0]] 
 ![![47, 0, 0], ![25, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-22, 1, 0], ![0, -22, 1], ![380, 95, -22]]]
  hmulB := by decide  
  f := ![![![507, -23, 0], ![1081, 0, 0]], ![![309, -14, 0], ![659, 0, 0]], ![![385, -17, 0], ![821, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 47, 0], ![-33, 0, 47]], ![![-1, 1, 0], ![11, -22, 1], ![-27, 95, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-14, 1, 0]] 
 ![![47, 0, 0], ![33, 1, 0], ![39, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-14, 1, 0], ![0, -14, 1], ![380, 95, -14]]]
  hmulB := by decide  
  f := ![![![603, -43, 0], ![2021, 0, 0]], ![![421, -30, 0], ![1411, 0, 0]], ![![495, -35, 0], ![1659, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 47, 0], ![-39, 0, 47]], ![![-1, 1, 0], ![9, -14, 1], ![-47, 95, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-11, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-11, 1, 0]] 
 ![![47, 0, 0], ![36, 1, 0], ![20, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-11, 1, 0], ![0, -11, 1], ![380, 95, -11]]]
  hmulB := by decide  
  f := ![![![397, -36, 0], ![1692, 0, 0]], ![![298, -27, 0], ![1270, 0, 0]], ![![168, -15, 0], ![716, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 47, 0], ![-20, 0, 47]], ![![-1, 1, 0], ![8, -11, 1], ![-60, 95, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-22, 1, 0]] ![![47, 0, 0], ![-14, 1, 0]]
  ![![47, 0, 0], ![-68, 11, 1]] where
 M := ![![![2209, 0, 0], ![-658, 47, 0]], ![![-1034, 47, 0], ![308, -36, 1]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![54, -10, -1], ![47, 0, 0]]], ![![![46, -10, -1], ![47, 0, 0]], ![![8, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-68, 11, 1]] ![![47, 0, 0], ![-11, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-517, 47, 0]], ![![-3196, 517, 47], ![1128, -94, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-11, 1, 0]]], ![![![-68, 11, 1]], ![![24, -2, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [39, 44, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 42, 23], [21, 10, 30], [0, 1]]
 g := ![![[11], [45, 13], [20, 10, 16], [38, 44], [1]], ![[27, 21, 25, 12], [7, 25], [37, 48, 34, 32], [2, 16], [27, 41, 36, 30]], ![[40, 6, 8, 41], [16, 47], [26, 23, 49, 50], [49, 38], [32, 30, 20, 23]]]
 h' := ![![[48, 42, 23], [7, 8], [15, 39, 38], [39, 44, 49], [14, 9, 16], [0, 1]], ![[21, 10, 30], [20, 18, 25], [44, 19, 5], [13, 10, 18], [41, 45, 49], [48, 42, 23]], ![[0, 1], [16, 27, 28], [51, 48, 10], [44, 52, 39], [10, 52, 41], [21, 10, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 11], []]
 b := ![[], [27, 40, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [39, 44, 37, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3014799, -1594929, -200393]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56883, -30093, -3781]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [2, 2, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 55, 47], [37, 3, 12], [0, 1]]
 g := ![![[25, 21, 49], [9, 18, 19], [5, 36], [50, 38, 51], [1]], ![[49, 0, 18, 42], [14, 19, 18, 18], [32, 53], [51, 49, 32, 14], [35, 45, 27, 42]], ![[41, 5, 31, 5], [15, 24, 35, 57], [48, 57], [1, 50, 58, 27], [20, 57, 13, 17]]]
 h' := ![![[9, 55, 47], [41, 12, 52], [19, 39, 45], [18, 5, 6], [57, 57, 46], [0, 1]], ![[37, 3, 12], [29, 28, 12], [12, 55, 21], [31, 16, 17], [10, 48, 44], [9, 55, 47]], ![[0, 1], [40, 19, 54], [41, 24, 52], [45, 38, 36], [50, 13, 28], [37, 3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 16], []]
 b := ![[], [0, 16, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [2, 2, 13, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243198, -93102, -9204]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4122, -1578, -156]
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

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![3, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![3, 1, 0]] 
 ![![61, 0, 0], ![3, 1, 0], ![52, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![3, 1, 0], ![0, 3, 1], ![380, 95, 3]]]
  hmulB := by decide  
  f := ![![![112, 37, 0], ![-2257, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![94, 31, 0], ![-1894, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 61, 0], ![-52, 0, 61]], ![![0, 1, 0], ![-1, 3, 1], ![-1, 95, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![13, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![13, 1, 0]] 
 ![![61, 0, 0], ![13, 1, 0], ![14, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![13, 1, 0], ![0, 13, 1], ![380, 95, 13]]]
  hmulB := by decide  
  f := ![![![404, 31, 0], ![-1891, 0, 0]], ![![78, 6, 0], ![-365, 0, 0]], ![![94, 7, 0], ![-440, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 61, 0], ![-14, 0, 61]], ![![0, 1, 0], ![-3, 13, 1], ![-17, 95, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-16, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-16, 1, 0]] 
 ![![61, 0, 0], ![45, 1, 0], ![49, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-16, 1, 0], ![0, -16, 1], ![380, 95, -16]]]
  hmulB := by decide  
  f := ![![![801, -50, 0], ![3050, 0, 0]], ![![593, -37, 0], ![2258, 0, 0]], ![![645, -40, 0], ![2456, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 61, 0], ![-49, 0, 61]], ![![-1, 1, 0], ![11, -16, 1], ![-51, 95, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![3, 1, 0]] ![![61, 0, 0], ![13, 1, 0]]
  ![![61, 0, 0], ![-83, 16, 1]] where
 M := ![![![3721, 0, 0], ![793, 61, 0]], ![![183, 61, 0], ![39, 16, 1]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![13, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-83, 16, 1]] ![![61, 0, 0], ![-16, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-976, 61, 0]], ![![-5063, 976, 61], ![1708, -244, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-16, 1, 0]]], ![![![-83, 16, 1]], ![![28, -4, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [60, 18, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 22, 56], [12, 44, 11], [0, 1]]
 g := ![![[45, 28, 17], [11, 10, 39], [30, 29], [46, 39], [59, 1], []], ![[35, 62, 14, 21], [39, 16, 55, 47], [9, 47], [60, 47], [25, 60], [22, 54]], ![[52, 61, 37, 61], [15, 63, 6, 43], [24, 14], [22, 49], [63, 15], [0, 54]]]
 h' := ![![[47, 22, 56], [10, 30, 34], [15, 30, 21], [41, 20, 30], [11, 17, 46], [0, 0, 1], [0, 1]], ![[12, 44, 11], [22, 10, 27], [61, 26, 58], [47, 32, 28], [30, 3, 28], [18, 40, 44], [47, 22, 56]], ![[0, 1], [40, 27, 6], [49, 11, 55], [45, 15, 9], [5, 47, 60], [10, 27, 22], [12, 44, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 7], []]
 b := ![[], [63, 26, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [60, 18, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4967447, 1694363, 138623]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![74141, 25289, 2069]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [41, 45, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 41, 36], [7, 29, 35], [0, 1]]
 g := ![![[17, 52, 57], [17, 10, 1], [60, 48, 38], [], [20, 1], []], ![[50, 34, 6, 4], [70, 19, 70, 5], [66, 53, 37, 57], [65, 10], [61, 60], [46, 18]], ![[48, 41, 29, 42], [61, 42, 13, 39], [42, 45, 8, 65], [34, 10], [29, 48], [47, 18]]]
 h' := ![![[13, 41, 36], [13, 18, 25], [25, 66, 1], [30, 55, 40], [32, 53], [0, 0, 1], [0, 1]], ![[7, 29, 35], [64, 1, 24], [18, 41, 62], [12, 25, 16], [11, 43, 62], [58, 33, 29], [13, 41, 36]], ![[0, 1], [49, 52, 22], [29, 35, 8], [58, 62, 15], [48, 46, 9], [39, 38, 41], [7, 29, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 14], []]
 b := ![[], [38, 36, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [41, 45, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81366, -7952, -3124]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1146, -112, -44]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-70, 5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-70, 5, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![3, 5, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-70, 5, 1], ![380, 25, 5], ![1900, 855, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -5, 73]], ![![-1, 0, 1], ![5, 0, 5], ![25, 10, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [9, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 72], [0, 1]]
 g := ![![[45, 65], [9], [38], [28, 48], [67], [1]], ![[0, 8], [9], [38], [6, 25], [67], [1]]]
 h' := ![![[33, 72], [62, 49], [17, 70], [40, 29], [62, 11], [64, 33], [0, 1]], ![[0, 1], [0, 24], [64, 3], [48, 44], [60, 62], [58, 40], [33, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [67, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [9, 40, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1529, 1940, 461]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -5, 461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-5, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-5, 1, 0]] 
 ![![73, 0, 0], ![68, 1, 0], ![48, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-5, 1, 0], ![0, -5, 1], ![380, 95, -5]]]
  hmulB := by decide  
  f := ![![![241, -48, 0], ![3504, 0, 0]], ![![226, -45, 0], ![3286, 0, 0]], ![![156, -31, 0], ![2268, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 73, 0], ![-48, 0, 73]], ![![-1, 1, 0], ![4, -5, 1], ![-80, 95, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-70, 5, 1]] ![![73, 0, 0], ![-5, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-365, 73, 0]], ![![-5110, 365, 73], ![730, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-5, 1, 0]]], ![![![-70, 5, 1]], ![![10, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-94, 1, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-94, 1, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![64, 1, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-94, 1, 1], ![380, 1, 1], ![380, 475, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -1, 79]], ![![-2, 0, 1], ![4, 0, 1], ![4, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [38, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 78], [0, 1]]
 g := ![![[77, 52], [45, 9], [8, 22], [34, 32], [9], [1]], ![[0, 27], [18, 70], [21, 57], [17, 47], [9], [1]]]
 h' := ![![[76, 78], [28, 62], [12, 3], [51, 41], [75, 43], [41, 76], [0, 1]], ![[0, 1], [0, 17], [3, 76], [7, 38], [25, 36], [50, 3], [76, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [63, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [38, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15152, -2350, 494]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-592, -36, 494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-1, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-1, 1, 0]] 
 ![![79, 0, 0], ![78, 1, 0], ![78, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-1, 1, 0], ![0, -1, 1], ![380, 95, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![237, 0, 0]], ![![2, -1, 0], ![80, 0, 0]], ![![2, -1, 0], ![80, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 79, 0], ![-78, 0, 79]], ![![-1, 1, 0], ![0, -1, 1], ![-88, 95, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-94, 1, 1]] ![![79, 0, 0], ![-1, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-79, 79, 0]], ![![-7426, 79, 79], ![474, 0, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-1, 1, 0]]], ![![![-94, 1, 1]], ![![6, 0, 0]]]]
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


lemma PB194I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB194I1 : PrimesBelowBoundCertificateInterval O 31 79 194 where
  m := 11
  g := ![2, 2, 2, 3, 1, 1, 3, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB194I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N0, I47N1, I47N2, I61N0, I61N1, I61N2, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [], [], [I61N0, I61N1, I61N2], [], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
