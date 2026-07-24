
import IdealArithmetic.Examples.NF3_1_564300_3.RI3_1_564300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 14, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 14, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![11, 14, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 14, 1], ![30, -19, 70], ![420, -414, -19]]]
  hmulB := by decide  
  f := ![![![-10, -14, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -14, 37]], ![![0, 0, 1], ![-20, -27, 70], ![17, -4, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [35, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 36], [0, 1]]
 g := ![![[], [34], [], [], [1]], ![[], [34], [], [], [1]]]
 h' := ![![[0, 36], [31], [0, 16], [4], [2], [0, 1]], ![[0, 1], [31], [0, 21], [4], [2], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [0, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [35, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95, -54, -25]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 8, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![4, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![4, 1, 0]] 
 ![![37, 0, 0], ![4, 1, 0], ![19, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![4, 1, 0], ![0, 4, 5], ![30, -30, 4]]]
  hmulB := by decide  
  f := ![![![89, 22, 0], ![-814, 0, 0]], ![![4, 1, 0], ![-36, 0, 0]], ![![47, 10, -2], ![-430, 15, 0]]]
  g := ![![![1, 0, 0], ![-4, 37, 0], ![-19, 0, 37]], ![![0, 1, 0], ![-3, 4, 5], ![2, -30, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![11, 14, 1]] ![![37, 0, 0], ![4, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![148, 37, 0]], ![![407, 518, 37], ![74, 37, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![4, 1, 0]]], ![![![11, 14, 1]], ![![2, 1, 2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![35, -1, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![35, -1, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![35, 40, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![35, -1, 1], ![30, 5, -5], ![-30, 36, 5]]]
  hmulB := by decide  
  f := ![![![-34, 1, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -40, 41]], ![![0, -1, 1], ![5, 5, -5], ![-5, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [16, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[36, 18], [40], [4], [15, 4], [1]], ![[0, 23], [40], [4], [7, 37], [1]]]
 h' := ![![[39, 40], [21, 31], [13, 9], [6, 39], [25, 39], [0, 1]], ![[0, 1], [0, 10], [36, 32], [10, 2], [29, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [26, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [16, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-345, 414, -250]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![205, 254, -250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![5, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![5, 1, 0]] 
 ![![41, 0, 0], ![5, 1, 0], ![36, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![5, 1, 0], ![0, 5, 5], ![30, -30, 5]]]
  hmulB := by decide  
  f := ![![![126, 25, 0], ![-1025, 0, 0]], ![![10, 2, 0], ![-81, 0, 0]], ![![116, 19, -4], ![-944, 33, 0]]]
  g := ![![![1, 0, 0], ![-5, 41, 0], ![-36, 0, 41]], ![![0, 1, 0], ![-5, 5, 5], ![0, -30, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![35, -1, 1]] ![![41, 0, 0], ![5, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![205, 41, 0]], ![![1435, -41, 41], ![205, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![5, 1, 0]]], ![![![35, -1, 1]], ![![5, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![13, 17, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![13, 17, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![13, 17, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![13, 17, 1], ![30, -17, 85], ![510, -504, -17]]]
  hmulB := by decide  
  f := ![![![-12, -17, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -17, 43]], ![![0, 0, 1], ![-25, -34, 85], ![17, -5, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [39, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 42], [0, 1]]
 g := ![![[22, 15], [18, 25], [36], [24, 4], [1]], ![[9, 28], [25, 18], [36], [32, 39], [1]]]
 h' := ![![[2, 42], [29, 31], [29, 38], [10, 37], [4, 2], [0, 1]], ![[0, 1], [5, 12], [19, 5], [41, 6], [8, 41], [2, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [13, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [39, 41, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1451, -21, 62]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, -25, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![1, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![1, 1, 0]] 
 ![![43, 0, 0], ![1, 1, 0], ![17, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![1, 1, 0], ![0, 1, 5], ![30, -30, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![43, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 2], ![17, -17, 0]]]
  g := ![![![1, 0, 0], ![-1, 43, 0], ![-17, 0, 43]], ![![0, 1, 0], ![-2, 1, 5], ![1, -30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![13, 17, 1]] ![![43, 0, 0], ![1, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![43, 43, 0]], ![![559, 731, 43], ![43, 0, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![1, 1, 0]]], ![![![13, 17, 1]], ![![1, 0, 2]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 2, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 2, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![3, 2, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 2, 1], ![30, -27, 10], ![60, -54, -27]]]
  hmulB := by decide  
  f := ![![![-2, -2, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -2, 47]], ![![0, 0, 1], ![0, -1, 10], ![3, 0, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [41, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 46], [0, 1]]
 g := ![![[23, 32], [17, 34], [32, 9], [31, 9], [1]], ![[21, 15], [9, 13], [5, 38], [4, 38], [1]]]
 h' := ![![[44, 46], [8, 28], [4, 9], [45, 44], [6, 44], [0, 1]], ![[0, 1], [18, 19], [24, 38], [7, 3], [15, 3], [44, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [17, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [41, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135, 239, -280]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 17, -280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-10, 1, 0]] 
 ![![47, 0, 0], ![37, 1, 0], ![27, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-10, 1, 0], ![0, -10, 5], ![30, -30, -10]]]
  hmulB := by decide  
  f := ![![![371, -37, 0], ![1739, 0, 0]], ![![301, -30, 0], ![1411, 0, 0]], ![![231, -19, -2], ![1083, 19, 0]]]
  g := ![![![1, 0, 0], ![-37, 47, 0], ![-27, 0, 47]], ![![-1, 1, 0], ![5, -10, 5], ![30, -30, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![3, 2, 1]] ![![47, 0, 0], ![-10, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-470, 47, 0]], ![![141, 94, 47], ![0, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-10, 1, 0]]], ![![![3, 2, 1]], ![![0, -1, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![33, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![0, 10, 5], ![30, -30, 10]]]
  hmulB := by decide  
  f := ![![![141, 14, 0], ![-742, 0, 0]], ![![10, 1, 0], ![-52, 0, 0]], ![![81, 2, -3], ![-426, 32, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-33, 0, 53]], ![![0, 1, 0], ![-5, 10, 5], ![0, -30, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![39, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![0, 21, 5], ![30, -30, 21]]]
  hmulB := by decide  
  f := ![![![379, 18, 0], ![-954, 0, 0]], ![![147, 7, 0], ![-370, 0, 0]], ![![267, 0, -3], ![-672, 32, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-39, 0, 53]], ![![0, 1, 0], ![-12, 21, 5], ![-3, -30, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, 1, 0]] 
 ![![53, 0, 0], ![22, 1, 0], ![41, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, 1, 0], ![0, 22, 5], ![30, -30, 22]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-901, 0, 0]], ![![154, 7, 0], ![-370, 0, 0]], ![![315, 1, -3], ![-757, 32, 0]]]
  g := ![![![1, 0, 0], ![-22, 53, 0], ![-41, 0, 53]], ![![0, 1, 0], ![-13, 22, 5], ![-4, -30, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![10, 1, 0]] ![![53, 0, 0], ![21, 1, 0]]
  ![![53, 0, 0], ![42, -15, 1]] where
 M := ![![![2809, 0, 0], ![1113, 53, 0]], ![![530, 53, 0], ![210, 31, 5]]]
 hmul := by decide  
 g := ![![![![11, 15, -1], ![53, 0, 0]], ![![-21, 16, -1], ![53, 0, 0]]], ![![![-32, 16, -1], ![53, 0, 0]], ![![0, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![42, -15, 1]] ![![53, 0, 0], ![22, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1166, 53, 0]], ![![2226, -795, 53], ![954, -318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![22, 1, 0]]], ![![![42, -15, 1]], ![![18, -6, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [50, 16, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 42, 25], [12, 16, 34], [0, 1]]
 g := ![![[25, 9, 36], [48, 32, 19], [32, 17], [50, 28, 1], [1]], ![[44, 15, 29, 49], [48, 57, 55, 53], [35, 17], [8, 46, 24, 21], [29, 5, 34, 49]], ![[40, 34, 55, 47], [16, 55, 45, 42], [16, 9], [7, 33, 51, 38], [22, 51, 38, 10]]]
 h' := ![![[48, 42, 25], [19, 17, 53], [5, 11, 14], [37, 5, 31], [9, 43, 1], [0, 1]], ![[12, 16, 34], [46, 55, 34], [14, 33, 27], [17, 6, 31], [51, 18, 29], [48, 42, 25]], ![[0, 1], [18, 46, 31], [45, 15, 18], [45, 48, 56], [38, 57, 29], [12, 16, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 2], []]
 b := ![[], [17, 23, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [50, 16, 58, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5900, -5428, -2006]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![100, -92, -34]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![45, -8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![45, -8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![45, 53, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![45, -8, 1], ![30, 15, -40], ![-240, 246, 15]]]
  hmulB := by decide  
  f := ![![![-44, 8, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -53, 61]], ![![0, -1, 1], ![30, 35, -40], ![-15, -9, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [40, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 60], [0, 1]]
 g := ![![[24, 57], [20], [35, 52], [11, 52], [16, 1]], ![[21, 4], [20], [13, 9], [50, 9], [32, 60]]]
 h' := ![![[16, 60], [2, 22], [3, 52], [48, 33], [31, 33], [0, 1]], ![[0, 1], [49, 39], [42, 9], [27, 28], [10, 28], [16, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [51, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [40, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1226, -241, 1822]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1324, -1587, 1822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-21, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-21, 1, 0]] 
 ![![61, 0, 0], ![40, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-21, 1, 0], ![0, -21, 5], ![30, -30, -21]]]
  hmulB := by decide  
  f := ![![![883, -42, 0], ![2562, 0, 0]], ![![610, -29, 0], ![1770, 0, 0]], ![![670, -15, -4], ![1944, 49, 0]]]
  g := ![![![1, 0, 0], ![-40, 61, 0], ![-46, 0, 61]], ![![-1, 1, 0], ![10, -21, 5], ![36, -30, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![45, -8, 1]] ![![61, 0, 0], ![-21, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1281, 61, 0]], ![![2745, -488, 61], ![-915, 183, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-21, 1, 0]]], ![![![45, -8, 1]], ![![-15, 3, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![11, 31, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![11, 31, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![11, 31, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![11, 31, 1], ![30, -19, 155], ![930, -924, -19]]]
  hmulB := by decide  
  f := ![![![-10, -31, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -31, 67]], ![![0, 0, 1], ![-25, -72, 155], ![17, -5, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [59, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 66], [0, 1]]
 g := ![![[64, 25], [15, 9], [47], [16], [40], [1]], ![[0, 42], [0, 58], [47], [16], [40], [1]]]
 h' := ![![[43, 66], [53, 5], [62, 64], [50, 28], [49, 63], [8, 43], [0, 1]], ![[0, 1], [0, 62], [0, 3], [48, 39], [11, 4], [48, 24], [43, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [22, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [59, 24, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144, 252, -7]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 7, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![19, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![0, -21, 5], ![30, -30, -21]]]
  hmulB := by decide  
  f := ![![![505, -24, 0], ![1608, 0, 0]], ![![358, -17, 0], ![1140, 0, 0]], ![![157, 1, -2], ![500, 27, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-19, 0, 67]], ![![-1, 1, 0], ![13, -21, 5], ![27, -30, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![11, 31, 1]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![737, 2077, 67], ![-201, -670, 134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-21, 1, 0]]], ![![![11, 31, 1]], ![![-3, -10, 2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 1, 0]] 
 ![![71, 0, 0], ![25, 1, 0], ![17, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 1, 0], ![0, 25, 5], ![30, -30, 25]]]
  hmulB := by decide  
  f := ![![![701, 28, 0], ![-1988, 0, 0]], ![![225, 9, 0], ![-638, 0, 0]], ![![127, -15, -4], ![-360, 57, 0]]]
  g := ![![![1, 0, 0], ![-25, 71, 0], ![-17, 0, 71]], ![![0, 1, 0], ![-10, 25, 5], ![5, -30, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-17, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-17, 1, 0]] 
 ![![71, 0, 0], ![54, 1, 0], ![70, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-17, 1, 0], ![0, -17, 5], ![30, -30, -17]]]
  hmulB := by decide  
  f := ![![![919, -54, 0], ![3834, 0, 0]], ![![698, -41, 0], ![2912, 0, 0]], ![![896, -39, -4], ![3738, 57, 0]]]
  g := ![![![1, 0, 0], ![-54, 71, 0], ![-70, 0, 71]], ![![-1, 1, 0], ![8, -17, 5], ![40, -30, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-8, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-8, 1, 0]] 
 ![![71, 0, 0], ![63, 1, 0], ![44, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-8, 1, 0], ![0, -8, 5], ![30, -30, -8]]]
  hmulB := by decide  
  f := ![![![89, -11, 0], ![781, 0, 0]], ![![81, -10, 0], ![711, 0, 0]], ![![68, -2, -4], ![598, 57, 0]]]
  g := ![![![1, 0, 0], ![-63, 71, 0], ![-44, 0, 71]], ![![-1, 1, 0], ![4, -8, 5], ![32, -30, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![25, 1, 0]] ![![71, 0, 0], ![-17, 1, 0]]
  ![![71, 0, 0], ![-14, 30, 1]] where
 M := ![![![5041, 0, 0], ![-1207, 71, 0]], ![![1775, 71, 0], ![-425, 8, 5]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![-3, -29, -1], ![71, 0, 0]]], ![![![25, 1, 0], ![0, 0, 0]], ![![-5, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-14, 30, 1]] ![![71, 0, 0], ![-8, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-568, 71, 0]], ![![-994, 2130, 71], ![142, -284, 142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-8, 1, 0]]], ![![![-14, 30, 1]], ![![2, -4, 2]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![2, 3, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![2, 3, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![2, 3, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![2, 3, 1], ![30, -28, 15], ![90, -84, -28]]]
  hmulB := by decide  
  f := ![![![-1, -3, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -3, 73]], ![![0, 0, 1], ![0, -1, 15], ![2, 0, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [39, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 72], [0, 1]]
 g := ![![[17, 32], [23], [36], [20, 67], [36], [1]], ![[44, 41], [23], [36], [56, 6], [36], [1]]]
 h' := ![![[67, 72], [53, 55], [1, 60], [23, 6], [44, 33], [34, 67], [0, 1]], ![[0, 1], [15, 18], [6, 13], [60, 67], [65, 40], [70, 6], [67, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [11, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [39, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159, -90, -103]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 3, -103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-15, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-15, 1, 0]] 
 ![![73, 0, 0], ![58, 1, 0], ![28, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-15, 1, 0], ![0, -15, 5], ![30, -30, -15]]]
  hmulB := by decide  
  f := ![![![706, -47, 0], ![3431, 0, 0]], ![![556, -37, 0], ![2702, 0, 0]], ![![286, -10, -3], ![1390, 44, 0]]]
  g := ![![![1, 0, 0], ![-58, 73, 0], ![-28, 0, 73]], ![![-1, 1, 0], ![10, -15, 5], ![30, -30, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![2, 3, 1]] ![![73, 0, 0], ![-15, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1095, 73, 0]], ![![146, 219, 73], ![0, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-15, 1, 0]]], ![![![2, 3, 1]], ![![0, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![54, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![0, 21, 5], ![30, -30, 21]]]
  hmulB := by decide  
  f := ![![![799, 38, 0], ![-3002, 0, 0]], ![![189, 9, 0], ![-710, 0, 0]], ![![510, 20, -1], ![-1916, 16, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-54, 0, 79]], ![![0, 1, 0], ![-9, 21, 5], ![-6, -30, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-19, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-19, 1, 0]] 
 ![![79, 0, 0], ![60, 1, 0], ![70, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-19, 1, 0], ![0, -19, 5], ![30, -30, -19]]]
  hmulB := by decide  
  f := ![![![628, -33, 0], ![2607, 0, 0]], ![![476, -25, 0], ![1976, 0, 0]], ![![568, -26, -1], ![2358, 16, 0]]]
  g := ![![![1, 0, 0], ![-60, 79, 0], ![-70, 0, 79]], ![![-1, 1, 0], ![10, -19, 5], ![40, -30, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-2, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-2, 1, 0]] 
 ![![79, 0, 0], ![77, 1, 0], ![15, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-2, 1, 0], ![0, -2, 5], ![30, -30, -2]]]
  hmulB := by decide  
  f := ![![![85, -42, 0], ![3318, 0, 0]], ![![83, -41, 0], ![3240, 0, 0]], ![![17, -8, -1], ![664, 16, 0]]]
  g := ![![![1, 0, 0], ![-77, 79, 0], ![-15, 0, 79]], ![![-1, 1, 0], ![1, -2, 5], ![30, -30, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![21, 1, 0]] ![![79, 0, 0], ![-19, 1, 0]]
  ![![79, 0, 0], ![15, 32, 1]] where
 M := ![![![6241, 0, 0], ![-1501, 79, 0]], ![![1659, 79, 0], ![-399, 2, 5]]]
 hmul := by decide  
 g := ![![![![64, -32, -1], ![79, 0, 0]], ![![-19, 1, 0], ![0, 0, 0]]], ![![![6, -31, -1], ![79, 0, 0]], ![![-6, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![15, 32, 1]] ![![79, 0, 0], ![-2, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-158, 79, 0]], ![![1185, 2528, 79], ![0, -79, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-2, 1, 0]]], ![![![15, 32, 1]], ![![0, -1, 2]]]]
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


lemma PB213I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB213I1 : PrimesBelowBoundCertificateInterval O 31 79 213 where
  m := 11
  g := ![2, 2, 2, 2, 3, 1, 2, 2, 3, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB213I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
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
      exact NI79N2
  β := ![I37N1, I41N1, I43N1, I47N1, I53N0, I53N1, I53N2, I61N1, I67N1, I71N0, I71N1, I71N2, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
