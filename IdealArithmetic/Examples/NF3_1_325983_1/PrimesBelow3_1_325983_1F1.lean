
import IdealArithmetic.Examples.NF3_1_325983_1.RI3_1_325983_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, -6, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, -6, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 31, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, -6, 1], ![105, -5, -30], ![-651, 105, 1]]]
  hmulB := by decide  
  f := ![![![-14, 6, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -31, 37]], ![![0, -1, 1], ![15, 25, -30], ![-18, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [10, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36], [0, 1]]
 g := ![![[6, 26], [10], [9, 3], [11], [1]], ![[0, 11], [10], [14, 34], [11], [1]]]
 h' := ![![[14, 36], [8, 10], [21, 11], [27, 22], [27, 14], [0, 1]], ![[0, 1], [0, 27], [27, 26], [2, 15], [1, 23], [14, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [11, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [10, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2089, 1155, -1321]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![592, 1138, -1321]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, 1, 0]] 
 ![![37, 0, 0], ![30, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, 1, 0], ![0, -6, 5], ![105, -14, -7]]]
  hmulB := by decide  
  f := ![![![155, -22, 0], ![814, 0, 0]], ![![134, -19, 0], ![704, 0, 0]], ![![158, -20, -2], ![830, 15, 0]]]
  g := ![![![1, 0, 0], ![-30, 37, 0], ![-36, 0, 37]], ![![-1, 1, 0], ![0, -6, 5], ![21, -14, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, -6, 1]] ![![37, 0, 0], ![-7, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-259, 37, 0]], ![![555, -222, 37], ![0, 37, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-7, 1, 0]]], ![![![15, -6, 1]], ![![0, 1, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![5, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![5, 1, 0]] 
 ![![41, 0, 0], ![5, 1, 0], ![35, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![5, 1, 0], ![0, 6, 5], ![105, -14, 5]]]
  hmulB := by decide  
  f := ![![![156, 31, 0], ![-1271, 0, 0]], ![![10, 2, 0], ![-81, 0, 0]], ![![130, 21, -4], ![-1059, 33, 0]]]
  g := ![![![1, 0, 0], ![-5, 41, 0], ![-35, 0, 41]], ![![0, 1, 0], ![-5, 6, 5], ![0, -14, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![11, 1, 0]] 
 ![![41, 0, 0], ![11, 1, 0], ![31, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![11, 1, 0], ![0, 12, 5], ![105, -14, 11]]]
  hmulB := by decide  
  f := ![![![100, 9, 0], ![-369, 0, 0]], ![![22, 2, 0], ![-81, 0, 0]], ![![74, -3, -4], ![-273, 33, 0]]]
  g := ![![![1, 0, 0], ![-11, 41, 0], ![-31, 0, 41]], ![![0, 1, 0], ![-7, 12, 5], ![-2, -14, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-17, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-17, 1, 0]] 
 ![![41, 0, 0], ![24, 1, 0], ![3, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-17, 1, 0], ![0, -16, 5], ![105, -14, -17]]]
  hmulB := by decide  
  f := ![![![562, -33, 0], ![1353, 0, 0]], ![![324, -19, 0], ![780, 0, 0]], ![![66, 9, -4], ![159, 33, 0]]]
  g := ![![![1, 0, 0], ![-24, 41, 0], ![-3, 0, 41]], ![![-1, 1, 0], ![9, -16, 5], ![12, -14, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![5, 1, 0]] ![![41, 0, 0], ![11, 1, 0]]
  ![![41, 0, 0], ![11, -13, 1]] where
 M := ![![![1681, 0, 0], ![451, 41, 0]], ![![205, 41, 0], ![55, 17, 5]]]
 hmul := by decide  
 g := ![![![![30, 13, -1], ![41, 0, 0]], ![![0, 14, -1], ![41, 0, 0]]], ![![![-6, 14, -1], ![41, 0, 0]], ![![0, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![11, -13, 1]] ![![41, 0, 0], ![-17, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-697, 41, 0]], ![![451, -533, 41], ![-82, 205, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-17, 1, 0]]], ![![![11, -13, 1]], ![![-2, 5, -2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-17, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-17, 1, 0]] 
 ![![43, 0, 0], ![26, 1, 0], ![23, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-17, 1, 0], ![0, -16, 5], ![105, -14, -17]]]
  hmulB := by decide  
  f := ![![![715, -42, 0], ![1806, 0, 0]], ![![426, -25, 0], ![1076, 0, 0]], ![![403, -14, -3], ![1018, 26, 0]]]
  g := ![![![1, 0, 0], ![-26, 43, 0], ![-23, 0, 43]], ![![-1, 1, 0], ![7, -16, 5], ![20, -14, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-10, 1, 0]] 
 ![![43, 0, 0], ![33, 1, 0], ![25, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-10, 1, 0], ![0, -9, 5], ![105, -14, -10]]]
  hmulB := by decide  
  f := ![![![211, -21, 0], ![903, 0, 0]], ![![161, -16, 0], ![689, 0, 0]], ![![125, -7, -3], ![535, 26, 0]]]
  g := ![![![1, 0, 0], ![-33, 43, 0], ![-25, 0, 43]], ![![-1, 1, 0], ![4, -9, 5], ![19, -14, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-17, 1, 0]] ![![43, 0, 0], ![-17, 1, 0]]
  ![![43, 0, 0], ![-11, 2, 1]] where
 M := ![![![1849, 0, 0], ![-731, 43, 0]], ![![-731, 43, 0], ![289, -33, 5]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![-6, -1, -1], ![43, 0, 0]]], ![![![-6, -1, -1], ![43, 0, 0]], ![![8, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-11, 2, 1]] ![![43, 0, 0], ![-10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-430, 43, 0]], ![![-473, 86, 43], ![215, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-10, 1, 0]]], ![![![-11, 2, 1]], ![![5, -1, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [15, 4, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 20], [36, 44, 27], [0, 1]]
 g := ![![[25, 12, 7], [0, 36, 24], [27, 42, 25], [2, 37, 1], []], ![[4, 45], [39, 25, 44, 44], [10, 29, 35, 30], [33, 3, 46, 39], [28, 24]], ![[35, 44, 35, 1], [9, 26, 20, 9], [4, 44, 24, 21], [41, 9, 8, 14], [21, 24]]]
 h' := ![![[1, 2, 20], [0, 19, 17], [18, 21, 20], [17, 1, 5], [0, 0, 1], [0, 1]], ![[36, 44, 27], [40, 25], [25, 35, 31], [38, 12, 5], [4, 2, 44], [1, 2, 20]], ![[0, 1], [18, 3, 30], [43, 38, 43], [23, 34, 37], [41, 45, 2], [36, 44, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 25], []]
 b := ![[], [19, 15, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [15, 4, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![644699, -165205, 69137]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13717, -3515, 1471]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-12, -15, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-12, -15, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 38, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-12, -15, 1], ![105, -41, -75], ![-1596, 231, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -38, 53]], ![![-1, -1, 1], ![60, 53, -75], ![-10, 23, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [52, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 52], [0, 1]]
 g := ![![[33, 52], [7], [13, 37], [52], [33, 1]], ![[0, 1], [7], [15, 16], [52], [13, 52]]]
 h' := ![![[33, 52], [17, 30], [13, 31], [28, 39], [33, 30], [0, 1]], ![[0, 1], [0, 23], [29, 22], [43, 14], [16, 23], [33, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [1, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [52, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2847, 21, 94]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, -67, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, 1, 0]] 
 ![![53, 0, 0], ![22, 1, 0], ![26, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, 1, 0], ![0, 23, 5], ![105, -14, 22]]]
  hmulB := by decide  
  f := ![![![507, 23, 0], ![-1219, 0, 0]], ![![198, 9, 0], ![-476, 0, 0]], ![![218, -4, -3], ![-524, 32, 0]]]
  g := ![![![1, 0, 0], ![-22, 53, 0], ![-26, 0, 53]], ![![0, 1, 0], ![-12, 23, 5], ![-3, -14, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-12, -15, 1]] ![![53, 0, 0], ![22, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1166, 53, 0]], ![![-636, -795, 53], ![-159, -371, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![22, 1, 0]]], ![![![-12, -15, 1]], ![![-3, -7, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![4, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![4, 1, 0]] 
 ![![59, 0, 0], ![4, 1, 0], ![55, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![4, 1, 0], ![0, 5, 5], ![105, -14, 4]]]
  hmulB := by decide  
  f := ![![![53, 13, 0], ![-767, 0, 0]], ![![-4, -1, 0], ![60, 0, 0]], ![![49, 11, -1], ![-709, 12, 0]]]
  g := ![![![1, 0, 0], ![-4, 59, 0], ![-55, 0, 59]], ![![0, 1, 0], ![-5, 5, 5], ![-1, -14, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![20, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![20, 1, 0]] 
 ![![59, 0, 0], ![20, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![20, 1, 0], ![0, 21, 5], ![105, -14, 20]]]
  hmulB := by decide  
  f := ![![![21, 1, 0], ![-59, 0, 0]], ![![-20, -1, 0], ![60, 0, 0]], ![![6, -4, -1], ![-16, 12, 0]]]
  g := ![![![1, 0, 0], ![-20, 59, 0], ![-34, 0, 59]], ![![0, 1, 0], ![-10, 21, 5], ![-5, -14, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-25, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-25, 1, 0]] 
 ![![59, 0, 0], ![34, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-25, 1, 0], ![0, -24, 5], ![105, -14, -25]]]
  hmulB := by decide  
  f := ![![![1001, -40, 0], ![2360, 0, 0]], ![![576, -23, 0], ![1358, 0, 0]], ![![973, -34, -1], ![2294, 12, 0]]]
  g := ![![![1, 0, 0], ![-34, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![9, -24, 5], ![34, -14, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![4, 1, 0]] ![![59, 0, 0], ![20, 1, 0]]
  ![![59, 0, 0], ![16, 5, 1]] where
 M := ![![![3481, 0, 0], ![1180, 59, 0]], ![![236, 59, 0], ![80, 25, 5]]]
 hmul := by decide  
 g := ![![![![43, -5, -1], ![59, 0, 0]], ![![4, -4, -1], ![59, 0, 0]]], ![![![-12, -4, -1], ![59, 0, 0]], ![![0, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![16, 5, 1]] ![![59, 0, 0], ![-25, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1475, 59, 0]], ![![944, 295, 59], ![-295, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-25, 1, 0]]], ![![![16, 5, 1]], ![![-5, -2, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [29, 28, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 49, 50], [52, 11, 11], [0, 1]]
 g := ![![[29, 2, 56], [34, 20], [30, 19, 56], [13, 23, 16], [1]], ![[49, 56, 38, 59], [28, 57], [8, 9, 24, 55], [58, 5, 48, 40], [8, 40, 19, 11]], ![[30, 15, 40, 40], [50, 47], [56, 55], [54, 33, 56, 2], [54, 55, 45, 50]]]
 h' := ![![[13, 49, 50], [2, 7, 19], [45, 11, 9], [50, 54, 19], [32, 33, 4], [0, 1]], ![[52, 11, 11], [39, 57, 10], [34, 60, 39], [27, 42, 42], [13, 35, 47], [13, 49, 50]], ![[0, 1], [26, 58, 32], [45, 51, 13], [17, 26], [23, 54, 10], [52, 11, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 52], []]
 b := ![[], [35, 21, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [29, 28, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2138294, 744322, -401990]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35054, 12202, -6590]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![7, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![7, 1, 0]] 
 ![![67, 0, 0], ![7, 1, 0], ![29, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![7, 1, 0], ![0, 8, 5], ![105, -14, 7]]]
  hmulB := by decide  
  f := ![![![281, 40, 0], ![-2680, 0, 0]], ![![21, 3, 0], ![-200, 0, 0]], ![![121, 14, -2], ![-1154, 27, 0]]]
  g := ![![![1, 0, 0], ![-7, 67, 0], ![-29, 0, 67]], ![![0, 1, 0], ![-3, 8, 5], ![0, -14, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 1, 0]] 
 ![![67, 0, 0], ![11, 1, 0], ![54, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 1, 0], ![0, 12, 5], ![105, -14, 11]]]
  hmulB := by decide  
  f := ![![![562, 51, 0], ![-3417, 0, 0]], ![![88, 8, 0], ![-535, 0, 0]], ![![450, 36, -2], ![-2736, 27, 0]]]
  g := ![![![1, 0, 0], ![-11, 67, 0], ![-54, 0, 67]], ![![0, 1, 0], ![-6, 12, 5], ![-5, -14, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-19, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-19, 1, 0]] 
 ![![67, 0, 0], ![48, 1, 0], ![12, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-19, 1, 0], ![0, -18, 5], ![105, -14, -19]]]
  hmulB := by decide  
  f := ![![![1217, -64, 0], ![4288, 0, 0]], ![![856, -45, 0], ![3016, 0, 0]], ![![214, -4, -2], ![754, 27, 0]]]
  g := ![![![1, 0, 0], ![-48, 67, 0], ![-12, 0, 67]], ![![-1, 1, 0], ![12, -18, 5], ![15, -14, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![7, 1, 0]] ![![67, 0, 0], ![11, 1, 0]]
  ![![67, 0, 0], ![2, -23, 1]] where
 M := ![![![4489, 0, 0], ![737, 67, 0]], ![![469, 67, 0], ![77, 19, 5]]]
 hmul := by decide  
 g := ![![![![65, 23, -1], ![67, 0, 0]], ![![11, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![1, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![2, -23, 1]] ![![67, 0, 0], ![-19, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1273, 67, 0]], ![![134, -1541, 67], ![67, 402, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-19, 1, 0]]], ![![![2, -23, 1]], ![![1, 6, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [5, 7, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 34, 68], [12, 36, 3], [0, 1]]
 g := ![![[66, 6, 10], [69, 34, 2], [44, 10, 27], [28, 27], [37, 1], []], ![[9, 49, 65, 34], [31, 12, 67, 63], [61, 62, 47, 67], [15, 40], [69, 18], [58, 9]], ![[9, 50, 58, 36], [40, 7, 34, 25], [19, 59, 24, 50], [38, 25], [14, 20], [52, 9]]]
 h' := ![![[25, 34, 68], [10, 35, 9], [64, 22, 12], [5, 8, 58], [28, 20, 13], [0, 0, 1], [0, 1]], ![[12, 36, 3], [66, 6, 6], [19, 45, 11], [39, 10, 5], [55, 19, 53], [51, 42, 36], [25, 34, 68]], ![[0, 1], [25, 30, 56], [1, 4, 48], [47, 53, 8], [38, 32, 5], [26, 29, 34], [12, 36, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 15], []]
 b := ![[], [66, 63, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [5, 7, 34, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1040860, 364940, -209024]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14660, 5140, -2944]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [41, 12, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 54, 71], [63, 18, 2], [0, 1]]
 g := ![![[10, 28, 65], [1, 1], [10, 12], [14, 59, 35], [18, 1], []], ![[29, 7, 28, 71], [27, 57], [19, 70], [53, 30, 0, 65], [34, 32], [2, 4]], ![[5, 18, 23, 36], [45, 55], [44, 50], [28, 3, 23, 64], [21, 69], [71, 4]]]
 h' := ![![[28, 54, 71], [64, 34, 24], [55, 28, 1], [10, 32, 31], [65, 35, 20], [0, 0, 1], [0, 1]], ![[63, 18, 2], [52, 39, 72], [8, 41, 35], [38, 0, 56], [47, 64, 71], [45, 62, 18], [28, 54, 71]], ![[0, 1], [4, 0, 50], [30, 4, 37], [3, 41, 59], [70, 47, 55], [36, 11, 54], [63, 18, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 56], []]
 b := ![[], [52, 52, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [41, 12, 55, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![765331270, -221650630, 122371068]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10483990, -3036310, 1676316]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [67, 62, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 52, 74], [77, 26, 5], [0, 1]]
 g := ![![[43, 39, 40], [12, 55, 11], [70, 39, 9], [37, 29, 26], [40, 1], []], ![[24, 12, 2, 66], [78, 35, 18, 47], [16, 54, 5, 53], [18, 49, 50, 3], [2, 44], [6, 25]], ![[24, 60, 3, 26], [54, 35, 18, 11], [77, 13, 71, 8], [31, 67, 39, 9], [49, 18], [75, 25]]]
 h' := ![![[42, 52, 74], [65, 46, 44], [50, 30, 66], [49, 65, 3], [6, 60, 37], [0, 0, 1], [0, 1]], ![[77, 26, 5], [68, 78, 45], [36, 64, 65], [71, 73, 69], [69, 43, 30], [19, 30, 26], [42, 52, 74]], ![[0, 1], [12, 34, 69], [9, 64, 27], [24, 20, 7], [75, 55, 12], [35, 49, 52], [77, 26, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 12], []]
 b := ![[], [3, 33, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [67, 62, 39, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![498016, -113918, 60988]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6304, -1442, 772]
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



lemma PB162I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB162I1 : PrimesBelowBoundCertificateInterval O 31 79 162 where
  m := 11
  g := ![2, 3, 3, 1, 2, 3, 1, 3, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB162I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
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
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N0, I41N1, I41N2, I43N0, I43N1, I53N1, I59N0, I59N1, I59N2, I67N0, I67N1, I67N2]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N0, I43N0, I43N1], [], [I53N1], [I59N0, I59N1, I59N2], [], [I67N0, I67N1, I67N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
