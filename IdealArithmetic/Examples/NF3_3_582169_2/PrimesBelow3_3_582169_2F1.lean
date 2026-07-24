
import IdealArithmetic.Examples.NF3_3_582169_2.RI3_3_582169_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [7, 16, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 21, 23], [23, 15, 14], [0, 1]]
 g := ![![[18, 4, 27], [21, 25], [3, 33, 10], [8, 1], []], ![[25, 2, 23, 13], [], [26, 5, 14, 24], [33, 3], [18, 11]], ![[19, 12, 30, 14], [14, 25], [9, 34, 7, 23], [30, 34], [27, 11]]]
 h' := ![![[22, 21, 23], [35, 4, 29], [16, 8, 5], [18, 13, 11], [0, 0, 1], [0, 1]], ![[23, 15, 14], [34, 15, 9], [21, 3], [24, 21, 20], [25, 4, 15], [22, 21, 23]], ![[0, 1], [34, 18, 36], [13, 26, 32], [24, 3, 6], [7, 33, 21], [23, 15, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 35], []]
 b := ![[], [11, 20, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [7, 16, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-734265, 494024, -51911]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19845, 13352, -1403]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![6, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![6, 1, 0]] 
 ![![41, 0, 0], ![6, 1, 0], ![5, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![6, 1, 0], ![0, 6, 1], ![-1639, 254, 7]]]
  hmulB := by decide  
  f := ![![![31, 5, 0], ![-205, 0, 0]], ![![-6, -1, 0], ![42, 0, 0]], ![![-5, -1, 0], ![35, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 41, 0], ![-5, 0, 41]], ![![0, 1, 0], ![-1, 6, 1], ![-78, 254, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![0, 14, 1], ![-1639, 254, 15]]]
  hmulB := by decide  
  f := ![![![15, 1, 0], ![-41, 0, 0]], ![![-14, -1, 0], ![42, 0, 0]], ![![-9, -1, 0], ![27, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-9, 0, 41]], ![![0, 1, 0], ![-5, 14, 1], ![-130, 254, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![20, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![20, 1, 0]] 
 ![![41, 0, 0], ![20, 1, 0], ![10, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![20, 1, 0], ![0, 20, 1], ![-1639, 254, 21]]]
  hmulB := by decide  
  f := ![![![181, 9, 0], ![-369, 0, 0]], ![![60, 3, 0], ![-122, 0, 0]], ![![10, 0, 0], ![-20, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 41, 0], ![-10, 0, 41]], ![![0, 1, 0], ![-10, 20, 1], ![-169, 254, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![6, 1, 0]] ![![41, 0, 0], ![14, 1, 0]]
  ![![41, 0, 0], ![-162, 20, 1]] where
 M := ![![![1681, 0, 0], ![574, 41, 0]], ![![246, 41, 0], ![84, 20, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-162, 20, 1]] ![![41, 0, 0], ![20, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![820, 41, 0]], ![![-6642, 820, 41], ![-4879, 492, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![20, 1, 0]]], ![![![-162, 20, 1]], ![![-119, 12, 1]]]]
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
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![3, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![3, 1, 0]] 
 ![![43, 0, 0], ![3, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![3, 1, 0], ![0, 3, 1], ![-1639, 254, 4]]]
  hmulB := by decide  
  f := ![![![76, 25, 0], ![-1075, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![58, 19, 0], ![-820, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 43, 0], ![-34, 0, 43]], ![![0, 1, 0], ![-1, 3, 1], ![-59, 254, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![15, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![15, 1, 0]] 
 ![![43, 0, 0], ![15, 1, 0], ![33, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![15, 1, 0], ![0, 15, 1], ![-1639, 254, 16]]]
  hmulB := by decide  
  f := ![![![226, 15, 0], ![-645, 0, 0]], ![![60, 4, 0], ![-171, 0, 0]], ![![156, 10, 0], ![-445, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 43, 0], ![-33, 0, 43]], ![![0, 1, 0], ![-6, 15, 1], ![-139, 254, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![0, -19, 1], ![-1639, 254, -18]]]
  hmulB := by decide  
  f := ![![![761, -40, 0], ![1720, 0, 0]], ![![438, -23, 0], ![990, 0, 0]], ![![484, -25, 0], ![1094, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-26, 0, 43]], ![![-1, 1, 0], ![10, -19, 1], ![-169, 254, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![3, 1, 0]] ![![43, 0, 0], ![15, 1, 0]]
  ![![43, 0, 0], ![-170, 18, 1]] where
 M := ![![![1849, 0, 0], ![645, 43, 0]], ![![129, 43, 0], ![45, 18, 1]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-170, 18, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-7310, 774, 43], ![1591, -258, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![-170, 18, 1]], ![![37, -6, 0]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [31, 5, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 43, 41], [18, 3, 6], [0, 1]]
 g := ![![[0, 7, 6], [15, 44, 16], [14, 46, 32], [37, 18, 1], []], ![[7, 9, 5, 30], [11, 33, 33, 35], [25, 0, 18, 5], [20, 12, 42, 40], [38, 36]], ![[13, 20, 27, 4], [16, 42, 4, 21], [22, 25, 15, 21], [11, 2, 0, 2], [26, 36]]]
 h' := ![![[0, 43, 41], [5, 45, 37], [36, 40, 4], [28, 9, 28], [0, 0, 1], [0, 1]], ![[18, 3, 6], [35, 2, 29], [24, 21, 7], [38, 9, 30], [44, 10, 3], [0, 43, 41]], ![[0, 1], [42, 0, 28], [3, 33, 36], [42, 29, 36], [35, 37, 43], [18, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 25], []]
 b := ![[], [11, 32, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [31, 5, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72656924, -22898259, 1803531]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1545892, -487197, 38373]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [16, 4, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 15, 36], [4, 37, 17], [0, 1]]
 g := ![![[44, 7, 13], [39, 46], [12, 28, 15], [29, 15], [1]], ![[7, 4, 24, 15], [38, 13], [36, 0, 17, 13], [44, 17], [28, 15, 3, 16]], ![[0, 43, 40, 28], [17, 28], [2, 49, 14, 11], [50, 17], [1, 29, 31, 37]]]
 h' := ![![[38, 15, 36], [41, 48, 38], [20, 50, 24], [4, 37, 42], [37, 49, 42], [0, 1]], ![[4, 37, 17], [32, 21, 7], [51, 24, 38], [34, 0, 24], [46, 21, 32], [38, 15, 36]], ![[0, 1], [0, 37, 8], [31, 32, 44], [20, 16, 40], [48, 36, 32], [4, 37, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 13], []]
 b := ![[], [1, 8, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [16, 4, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3616614, 1252284, -123013]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68238, 23628, -2321]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![29, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![29, 1, 0]] 
 ![![59, 0, 0], ![29, 1, 0], ![44, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![29, 1, 0], ![0, 29, 1], ![-1639, 254, 30]]]
  hmulB := by decide  
  f := ![![![378, 13, 0], ![-767, 0, 0]], ![![174, 6, 0], ![-353, 0, 0]], ![![276, 9, 0], ![-560, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 59, 0], ![-44, 0, 59]], ![![0, 1, 0], ![-15, 29, 1], ![-175, 254, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-24, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-24, 1, 0]] 
 ![![59, 0, 0], ![35, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-24, 1, 0], ![0, -24, 1], ![-1639, 254, -23]]]
  hmulB := by decide  
  f := ![![![1057, -44, 0], ![2596, 0, 0]], ![![649, -27, 0], ![1594, 0, 0]], ![![250, -10, 0], ![614, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 59, 0], ![-14, 0, 59]], ![![-1, 1, 0], ![14, -24, 1], ![-173, 254, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-6, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-6, 1, 0]] 
 ![![59, 0, 0], ![53, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-6, 1, 0], ![0, -6, 1], ![-1639, 254, -5]]]
  hmulB := by decide  
  f := ![![![73, -12, 0], ![708, 0, 0]], ![![67, -11, 0], ![650, 0, 0]], ![![37, -6, 0], ![360, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 59, 0], ![-23, 0, 59]], ![![-1, 1, 0], ![5, -6, 1], ![-254, 254, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![29, 1, 0]] ![![59, 0, 0], ![-24, 1, 0]]
  ![![59, 0, 0], ![-165, 5, 1]] where
 M := ![![![3481, 0, 0], ![-1416, 59, 0]], ![![1711, 59, 0], ![-696, 5, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![141, -4, -1], ![59, 0, 0]]], ![![![29, 1, 0], ![0, 0, 0]], ![![156, -5, -1], ![60, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-165, 5, 1]] ![![59, 0, 0], ![-6, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-354, 59, 0]], ![![-9735, 295, 59], ![-649, 59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-6, 1, 0]]], ![![![-165, 5, 1]], ![![-11, 1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![1, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![1, 1, 0]] 
 ![![61, 0, 0], ![1, 1, 0], ![60, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![1, 1, 0], ![0, 1, 1], ![-1639, 254, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![61, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![60, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 61, 0], ![-60, 0, 61]], ![![0, 1, 0], ![-1, 1, 1], ![-33, 254, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![2, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![2, 1, 0]] 
 ![![61, 0, 0], ![2, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![2, 1, 0], ![0, 2, 1], ![-1639, 254, 3]]]
  hmulB := by decide  
  f := ![![![59, 29, 0], ![-1769, 0, 0]], ![![-2, -1, 0], ![62, 0, 0]], ![![55, 27, 0], ![-1649, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 61, 0], ![-57, 0, 61]], ![![0, 1, 0], ![-1, 2, 1], ![-38, 254, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-4, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-4, 1, 0]] 
 ![![61, 0, 0], ![57, 1, 0], ![45, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-4, 1, 0], ![0, -4, 1], ![-1639, 254, -3]]]
  hmulB := by decide  
  f := ![![![193, -48, 0], ![2928, 0, 0]], ![![181, -45, 0], ![2746, 0, 0]], ![![145, -36, 0], ![2200, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 61, 0], ![-45, 0, 61]], ![![-1, 1, 0], ![3, -4, 1], ![-262, 254, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![1, 1, 0]] ![![61, 0, 0], ![2, 1, 0]]
  ![![61, 0, 0], ![-181, 3, 1]] where
 M := ![![![3721, 0, 0], ![122, 61, 0]], ![![61, 61, 0], ![2, 3, 1]]]
 hmul := by decide  
 g := ![![![![61, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-181, 3, 1]] ![![61, 0, 0], ![-4, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-244, 61, 0]], ![![-11041, 183, 61], ![-915, 61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-4, 1, 0]]], ![![![-181, 3, 1]], ![![-15, 1, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![31, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![31, 1, 0]] 
 ![![67, 0, 0], ![31, 1, 0], ![44, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![31, 1, 0], ![0, 31, 1], ![-1639, 254, 32]]]
  hmulB := by decide  
  f := ![![![342, 11, 0], ![-737, 0, 0]], ![![124, 4, 0], ![-267, 0, 0]], ![![170, 5, 0], ![-366, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 67, 0], ![-44, 0, 67]], ![![0, 1, 0], ![-15, 31, 1], ![-163, 254, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-27, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-27, 1, 0]] 
 ![![67, 0, 0], ![40, 1, 0], ![8, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-27, 1, 0], ![0, -27, 1], ![-1639, 254, -26]]]
  hmulB := by decide  
  f := ![![![244, -9, 0], ![603, 0, 0]], ![![136, -5, 0], ![336, 0, 0]], ![![38, -1, 0], ![94, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 67, 0], ![-8, 0, 67]], ![![-1, 1, 0], ![16, -27, 1], ![-173, 254, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-5, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-5, 1, 0]] 
 ![![67, 0, 0], ![62, 1, 0], ![42, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-5, 1, 0], ![0, -5, 1], ![-1639, 254, -4]]]
  hmulB := by decide  
  f := ![![![156, -31, 0], ![2077, 0, 0]], ![![146, -29, 0], ![1944, 0, 0]], ![![96, -19, 0], ![1278, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 67, 0], ![-42, 0, 67]], ![![-1, 1, 0], ![4, -5, 1], ![-257, 254, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![31, 1, 0]] ![![67, 0, 0], ![-27, 1, 0]]
  ![![67, 0, 0], ![-167, 4, 1]] where
 M := ![![![4489, 0, 0], ![-1809, 67, 0]], ![![2077, 67, 0], ![-837, 4, 1]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![140, -3, -1], ![67, 0, 0]]], ![![![31, 1, 0], ![0, 0, 0]], ![![157, -4, -1], ![68, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-167, 4, 1]] ![![67, 0, 0], ![-5, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-335, 67, 0]], ![![-11189, 268, 67], ![-804, 67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-5, 1, 0]]], ![![![-167, 4, 1]], ![![-12, 1, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![6, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![6, 1, 0]] 
 ![![71, 0, 0], ![6, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![6, 1, 0], ![0, 6, 1], ![-1639, 254, 7]]]
  hmulB := by decide  
  f := ![![![61, 10, 0], ![-710, 0, 0]], ![![-6, -1, 0], ![72, 0, 0]], ![![25, 4, 0], ![-290, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 71, 0], ![-35, 0, 71]], ![![0, 1, 0], ![-1, 6, 1], ![-48, 254, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![22, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![22, 1, 0]] 
 ![![71, 0, 0], ![22, 1, 0], ![13, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![22, 1, 0], ![0, 22, 1], ![-1639, 254, 23]]]
  hmulB := by decide  
  f := ![![![573, 26, 0], ![-1846, 0, 0]], ![![154, 7, 0], ![-496, 0, 0]], ![![95, 4, 0], ![-306, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 71, 0], ![-13, 0, 71]], ![![0, 1, 0], ![-7, 22, 1], ![-106, 254, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-29, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-29, 1, 0]] 
 ![![71, 0, 0], ![42, 1, 0], ![11, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-29, 1, 0], ![0, -29, 1], ![-1639, 254, -28]]]
  hmulB := by decide  
  f := ![![![1770, -61, 0], ![4331, 0, 0]], ![![1074, -37, 0], ![2628, 0, 0]], ![![302, -10, 0], ![739, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 71, 0], ![-11, 0, 71]], ![![-1, 1, 0], ![17, -29, 1], ![-169, 254, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![6, 1, 0]] ![![71, 0, 0], ![22, 1, 0]]
  ![![71, 0, 0], ![-152, 28, 1]] where
 M := ![![![5041, 0, 0], ![1562, 71, 0]], ![![426, 71, 0], ![132, 28, 1]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![22, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-152, 28, 1]] ![![71, 0, 0], ![-29, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2059, 71, 0]], ![![-10792, 1988, 71], ![2769, -710, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-29, 1, 0]]], ![![![-152, 28, 1]], ![![39, -10, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-33, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-33, 1, 0]] 
 ![![73, 0, 0], ![40, 1, 0], ![6, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-33, 1, 0], ![0, -33, 1], ![-1639, 254, -32]]]
  hmulB := by decide  
  f := ![![![1486, -45, 0], ![3285, 0, 0]], ![![826, -25, 0], ![1826, 0, 0]], ![![180, -5, 0], ![398, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 73, 0], ![-6, 0, 73]], ![![-1, 1, 0], ![18, -33, 1], ![-159, 254, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-28, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-28, 1, 0]] 
 ![![73, 0, 0], ![45, 1, 0], ![19, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-28, 1, 0], ![0, -28, 1], ![-1639, 254, -27]]]
  hmulB := by decide  
  f := ![![![1905, -68, 0], ![4964, 0, 0]], ![![1205, -43, 0], ![3140, 0, 0]], ![![515, -18, 0], ![1342, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 73, 0], ![-19, 0, 73]], ![![-1, 1, 0], ![17, -28, 1], ![-172, 254, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-13, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-13, 1, 0]] 
 ![![73, 0, 0], ![60, 1, 0], ![50, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-13, 1, 0], ![0, -13, 1], ![-1639, 254, -12]]]
  hmulB := by decide  
  f := ![![![664, -51, 0], ![3723, 0, 0]], ![![560, -43, 0], ![3140, 0, 0]], ![![458, -35, 0], ![2568, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 73, 0], ![-50, 0, 73]], ![![-1, 1, 0], ![10, -13, 1], ![-223, 254, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-33, 1, 0]] ![![73, 0, 0], ![-28, 1, 0]]
  ![![73, 0, 0], ![-171, 12, 1]] where
 M := ![![![5329, 0, 0], ![-2044, 73, 0]], ![![-2409, 73, 0], ![924, -61, 1]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![143, -11, -1], ![73, 0, 0]]], ![![![138, -11, -1], ![73, 0, 0]], ![![15, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-171, 12, 1]] ![![73, 0, 0], ![-13, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-949, 73, 0]], ![![-12483, 876, 73], ![584, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-13, 1, 0]]], ![![![-171, 12, 1]], ![![8, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [14, 38, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 46, 29], [37, 32, 50], [0, 1]]
 g := ![![[55, 9, 26], [25, 41, 36], [40, 73, 22], [63, 78, 73], [57, 1], []], ![[18, 9, 8, 43], [44, 70, 45, 12], [11, 52, 20, 28], [25, 77, 53, 71], [57, 76], [45, 51]], ![[38, 10], [15, 76, 78, 8], [74, 57, 40, 10], [16, 63, 65, 10], [66, 62], [24, 51]]]
 h' := ![![[20, 46, 29], [45, 26, 37], [72, 76, 6], [66, 54, 41], [71, 32, 51], [0, 0, 1], [0, 1]], ![[37, 32, 50], [34, 49, 42], [54, 71, 26], [11, 28, 34], [41, 49, 32], [7, 48, 32], [20, 46, 29]], ![[0, 1], [44, 4], [76, 11, 47], [19, 76, 4], [60, 77, 75], [6, 31, 46], [37, 32, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 40], []]
 b := ![[], [29, 0, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [14, 38, 22, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61400143, 20401671, -1649836]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-777217, 258249, -20884]
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



lemma PB170I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB170I1 : PrimesBelowBoundCertificateInterval O 31 79 170 where
  m := 11
  g := ![1, 3, 3, 1, 1, 3, 3, 3, 3, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB170I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
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
      exact NI41N1
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I41N0, I41N1, I41N2, I43N0, I43N1, I43N2, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N0, I43N1, I43N2], [], [], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
