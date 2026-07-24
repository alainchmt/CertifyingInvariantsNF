
import IdealArithmetic.Examples.NF3_1_374220_1.RI3_1_374220_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![25, 9, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![25, 9, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![25, 9, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![25, 9, 1], ![114, 7, 9], ![1026, -48, 7]]]
  hmulB := by decide  
  f := ![![![-24, -9, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -9, 37]], ![![0, 0, 1], ![-3, -2, 9], ![23, -3, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [18, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 36], [0, 1]]
 g := ![![[30, 21], [4], [5, 11], [3], [1]], ![[12, 16], [4], [22, 26], [3], [1]]]
 h' := ![![[15, 36], [36, 13], [21, 35], [11, 23], [19, 15], [0, 1]], ![[0, 1], [9, 24], [28, 2], [23, 14], [22, 22], [15, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [3, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [18, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246, 56, -39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 11, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-9, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-9, 1, 0]] 
 ![![37, 0, 0], ![28, 1, 0], ![30, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-9, 1, 0], ![0, -9, 1], ![114, -18, -9]]]
  hmulB := by decide  
  f := ![![![316, -35, 0], ![1295, 0, 0]], ![![244, -27, 0], ![1000, 0, 0]], ![![264, -29, 0], ![1082, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 37, 0], ![-30, 0, 37]], ![![-1, 1, 0], ![6, -9, 1], ![24, -18, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![25, 9, 1]] ![![37, 0, 0], ![-9, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-333, 37, 0]], ![![925, 333, 37], ![-111, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-9, 1, 0]]], ![![![25, 9, 1]], ![![-3, -2, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-5, 10, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-5, 10, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![36, 10, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-5, 10, 1], ![114, -23, 10], ![1140, -66, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -10, 41]], ![![-1, 0, 1], ![-6, -3, 10], ![48, 4, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [7, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 40], [0, 1]]
 g := ![![[3, 21], [18], [18], [12, 31], [1]], ![[13, 20], [18], [18], [17, 10], [1]]]
 h' := ![![[20, 40], [39, 12], [1, 31], [39, 31], [34, 20], [0, 1]], ![[0, 1], [33, 29], [6, 10], [3, 10], [24, 21], [20, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [34, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [7, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1381, 1204, -101]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 54, -101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-10, 1, 0]] 
 ![![41, 0, 0], ![31, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-10, 1, 0], ![0, -10, 1], ![114, -18, -10]]]
  hmulB := by decide  
  f := ![![![391, -39, 0], ![1599, 0, 0]], ![![301, -30, 0], ![1231, 0, 0]], ![![233, -23, 0], ![953, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 41, 0], ![-23, 0, 41]], ![![-1, 1, 0], ![7, -10, 1], ![22, -18, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-5, 10, 1]] ![![41, 0, 0], ![-10, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-410, 41, 0]], ![![-205, 410, 41], ![164, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-10, 1, 0]]], ![![![-5, 10, 1]], ![![4, -3, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [3, 22, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 31, 20], [27, 11, 23], [0, 1]]
 g := ![![[18, 21, 13], [8, 0, 4], [9, 21], [19, 16, 1], []], ![[16, 22, 26, 39], [1, 16, 7, 8], [2, 38], [39, 12, 28, 12], [29, 13]], ![[25, 31, 21, 24], [25, 10, 26, 16], [20, 1], [38, 39, 19, 1], [26, 13]]]
 h' := ![![[32, 31, 20], [19, 5, 20], [40, 16, 41], [29, 7, 35], [0, 0, 1], [0, 1]], ![[27, 11, 23], [42, 22, 19], [11, 32, 40], [24, 38, 9], [34, 17, 11], [32, 31, 20]], ![[0, 1], [16, 16, 4], [30, 38, 5], [41, 41, 42], [6, 26, 31], [27, 11, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 11], []]
 b := ![[], [3, 13, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [3, 22, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134375, -11180, -5977]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3125, -260, -139]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-4, -5, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-4, -5, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![43, 42, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-4, -5, 1], ![114, -22, -5], ![-570, 204, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -42, 47]], ![![-1, -1, 1], ![7, 4, -5], ![8, 24, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 46], [0, 1]]
 g := ![![[36, 25], [44, 9], [31, 42], [3, 4], [1]], ![[39, 22], [15, 38], [21, 5], [11, 43], [1]]]
 h' := ![![[2, 46], [39, 42], [20, 3], [8, 29], [34, 2], [0, 1]], ![[0, 1], [29, 5], [26, 44], [19, 18], [38, 45], [2, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [45, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-625, 1181, -302]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![263, 295, -302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![5, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![5, 1, 0]] 
 ![![47, 0, 0], ![5, 1, 0], ![22, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![5, 1, 0], ![0, 5, 1], ![114, -18, 5]]]
  hmulB := by decide  
  f := ![![![86, 17, 0], ![-799, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![36, 7, 0], ![-334, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 47, 0], ![-22, 0, 47]], ![![0, 1, 0], ![-1, 5, 1], ![2, -18, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-4, -5, 1]] ![![47, 0, 0], ![5, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![235, 47, 0]], ![![-188, -235, 47], ![94, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![5, 1, 0]]], ![![![-4, -5, 1]], ![![2, -1, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![7, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![7, 1, 0]] 
 ![![53, 0, 0], ![7, 1, 0], ![4, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![7, 1, 0], ![0, 7, 1], ![114, -18, 7]]]
  hmulB := by decide  
  f := ![![![211, 30, 0], ![-1590, 0, 0]], ![![21, 3, 0], ![-158, 0, 0]], ![![8, 1, 0], ![-60, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 53, 0], ![-4, 0, 53]], ![![0, 1, 0], ![-1, 7, 1], ![4, -18, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![11, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![11, 1, 0]] 
 ![![53, 0, 0], ![11, 1, 0], ![38, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![11, 1, 0], ![0, 11, 1], ![114, -18, 11]]]
  hmulB := by decide  
  f := ![![![232, 21, 0], ![-1113, 0, 0]], ![![44, 4, 0], ![-211, 0, 0]], ![![168, 15, 0], ![-806, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 53, 0], ![-38, 0, 53]], ![![0, 1, 0], ![-3, 11, 1], ![-2, -18, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![0, -18, 1], ![114, -18, -18]]]
  hmulB := by decide  
  f := ![![![91, -5, 0], ![265, 0, 0]], ![![73, -4, 0], ![213, 0, 0]], ![![97, -5, 0], ![283, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-47, 0, 53]], ![![-1, 1, 0], ![11, -18, 1], ![30, -18, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![7, 1, 0]] ![![53, 0, 0], ![11, 1, 0]]
  ![![53, 0, 0], ![24, 18, 1]] where
 M := ![![![2809, 0, 0], ![583, 53, 0]], ![![371, 53, 0], ![77, 18, 1]]]
 hmul := by decide  
 g := ![![![![29, -18, -1], ![53, 0, 0]], ![![-13, -17, -1], ![53, 0, 0]]], ![![![-17, -17, -1], ![53, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![24, 18, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![1272, 954, 53], ![-318, -318, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![24, 18, 1]], ![![-6, -6, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [58, 0, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 45, 24], [17, 13, 35], [0, 1]]
 g := ![![[19, 17, 3], [21, 57, 17], [55, 46], [17, 46, 57], [1]], ![[40, 17, 51, 58], [34, 12, 53, 14], [39, 17], [42, 45, 47, 30], [28, 49, 56, 18]], ![[42, 42, 13, 28], [39, 1, 54, 21], [6, 5], [13, 0, 24, 27], [48, 7, 45, 41]]]
 h' := ![![[19, 45, 24], [21, 39, 48], [49, 51, 31], [17, 47, 20], [1, 0, 36], [0, 1]], ![[17, 13, 35], [51, 32, 26], [2, 1, 34], [9, 45, 31], [43, 50, 55], [19, 45, 24]], ![[0, 1], [1, 47, 44], [41, 7, 53], [25, 26, 8], [5, 9, 27], [17, 13, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 2], []]
 b := ![[], [7, 46, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [58, 0, 23, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1652, 4602, -1003]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, 78, -17]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![28, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![28, 1, 0]] 
 ![![61, 0, 0], ![28, 1, 0], ![9, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![28, 1, 0], ![0, 28, 1], ![114, -18, 28]]]
  hmulB := by decide  
  f := ![![![449, 16, 0], ![-976, 0, 0]], ![![196, 7, 0], ![-426, 0, 0]], ![![69, 2, 0], ![-150, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 61, 0], ![-9, 0, 61]], ![![0, 1, 0], ![-13, 28, 1], ![6, -18, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-16, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-16, 1, 0]] 
 ![![61, 0, 0], ![45, 1, 0], ![49, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-16, 1, 0], ![0, -16, 1], ![114, -18, -16]]]
  hmulB := by decide  
  f := ![![![801, -50, 0], ![3050, 0, 0]], ![![593, -37, 0], ![2258, 0, 0]], ![![645, -40, 0], ![2456, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 61, 0], ![-49, 0, 61]], ![![-1, 1, 0], ![11, -16, 1], ![28, -18, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-12, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-12, 1, 0]] 
 ![![61, 0, 0], ![49, 1, 0], ![39, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-12, 1, 0], ![0, -12, 1], ![114, -18, -12]]]
  hmulB := by decide  
  f := ![![![697, -58, 0], ![3538, 0, 0]], ![![565, -47, 0], ![2868, 0, 0]], ![![459, -38, 0], ![2330, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 61, 0], ![-39, 0, 61]], ![![-1, 1, 0], ![9, -12, 1], ![24, -18, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![28, 1, 0]] ![![61, 0, 0], ![-16, 1, 0]]
  ![![61, 0, 0], ![40, 12, 1]] where
 M := ![![![3721, 0, 0], ![-976, 61, 0]], ![![1708, 61, 0], ![-448, 12, 1]]]
 hmul := by decide  
 g := ![![![![21, -12, -1], ![61, 0, 0]], ![![-16, 1, 0], ![0, 0, 0]]], ![![![-12, -11, -1], ![61, 0, 0]], ![![-8, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![40, 12, 1]] ![![61, 0, 0], ![-12, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-732, 61, 0]], ![![2440, 732, 61], ![-366, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-12, 1, 0]]], ![![![40, 12, 1]], ![![-6, -2, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, -9, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, -9, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![32, 58, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, -9, 1], ![114, 14, -9], ![-1026, 276, 14]]]
  hmulB := by decide  
  f := ![![![-31, 9, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -58, 67]], ![![0, -1, 1], ![6, 8, -9], ![-22, -8, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [13, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 66], [0, 1]]
 g := ![![[6, 33], [46, 36], [56], [59], [54], [1]], ![[45, 34], [52, 31], [56], [59], [54], [1]]]
 h' := ![![[56, 66], [5, 57], [48, 6], [46, 49], [3, 27], [54, 56], [0, 1]], ![[0, 1], [48, 10], [49, 61], [43, 18], [41, 40], [41, 11], [56, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [28, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [13, 11, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4357, -323, 356]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105, -313, 356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![9, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![9, 1, 0]] 
 ![![67, 0, 0], ![9, 1, 0], ![53, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![9, 1, 0], ![0, 9, 1], ![114, -18, 9]]]
  hmulB := by decide  
  f := ![![![118, 13, 0], ![-871, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![92, 10, 0], ![-679, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 67, 0], ![-53, 0, 67]], ![![0, 1, 0], ![-2, 9, 1], ![-3, -18, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![32, -9, 1]] ![![67, 0, 0], ![9, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![603, 67, 0]], ![![2144, -603, 67], ![402, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![9, 1, 0]]], ![![![32, -9, 1]], ![![6, -1, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-4, 7, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-4, 7, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![67, 7, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-4, 7, 1], ![114, -22, 7], ![798, -12, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -7, 71]], ![![-1, 0, 1], ![-5, -1, 7], ![32, 2, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [46, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 70], [0, 1]]
 g := ![![[11, 8], [49, 10], [9, 5], [3], [10], [1]], ![[10, 63], [30, 61], [35, 66], [3], [10], [1]]]
 h' := ![![[62, 70], [18, 24], [12, 62], [36, 54], [23, 28], [25, 62], [0, 1]], ![[0, 1], [15, 47], [22, 9], [47, 17], [55, 43], [35, 9], [62, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [38, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [46, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-646, 243, -16]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 5, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-7, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-7, 1, 0]] 
 ![![71, 0, 0], ![64, 1, 0], ![22, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-7, 1, 0], ![0, -7, 1], ![114, -18, -7]]]
  hmulB := by decide  
  f := ![![![442, -63, 0], ![4473, 0, 0]], ![![400, -57, 0], ![4048, 0, 0]], ![![148, -21, 0], ![1498, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 71, 0], ![-22, 0, 71]], ![![-1, 1, 0], ![6, -7, 1], ![20, -18, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-4, 7, 1]] ![![71, 0, 0], ![-7, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-497, 71, 0]], ![![-284, 497, 71], ![142, -71, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-7, 1, 0]]], ![![![-4, 7, 1]], ![![2, -1, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-19, -6, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-19, -6, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![54, 67, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-19, -6, 1], ![114, -37, -6], ![-684, 222, -37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -67, 73]], ![![-1, -1, 1], ![6, 5, -6], ![18, 37, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [29, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 72], [0, 1]]
 g := ![![[40, 23], [57], [4], [51, 41], [64], [1]], ![[5, 50], [57], [4], [14, 32], [64], [1]]]
 h' := ![![[8, 72], [45, 13], [26, 35], [54, 71], [7, 48], [44, 8], [0, 1]], ![[0, 1], [3, 60], [14, 38], [38, 2], [26, 25], [35, 65], [8, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [56, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [29, 65, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![485, 449, 59]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -48, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![6, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![6, 1, 0]] 
 ![![73, 0, 0], ![6, 1, 0], ![37, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![6, 1, 0], ![0, 6, 1], ![114, -18, 6]]]
  hmulB := by decide  
  f := ![![![307, 51, 0], ![-3723, 0, 0]], ![![18, 3, 0], ![-218, 0, 0]], ![![151, 25, 0], ![-1831, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 73, 0], ![-37, 0, 73]], ![![0, 1, 0], ![-1, 6, 1], ![0, -18, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-19, -6, 1]] ![![73, 0, 0], ![6, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![438, 73, 0]], ![![-1387, -438, 73], ![0, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![6, 1, 0]]], ![![![-19, -6, 1]], ![![0, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![22, -2, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![22, -2, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![22, 77, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![22, -2, 1], ![114, 4, -2], ![-228, 150, 4]]]
  hmulB := by decide  
  f := ![![![-21, 2, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -77, 79]], ![![0, -1, 1], ![2, 2, -2], ![-4, -2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [58, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 78], [0, 1]]
 g := ![![[18, 22], [15, 45], [58, 5], [55, 8], [52], [1]], ![[39, 57], [40, 34], [52, 74], [77, 71], [52], [1]]]
 h' := ![![[62, 78], [78, 41], [33, 19], [49, 20], [32, 61], [21, 62], [0, 1]], ![[0, 1], [13, 38], [26, 60], [25, 59], [22, 18], [73, 17], [62, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [69, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [58, 17, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4464, 966, 70]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -56, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![2, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![2, 1, 0]] 
 ![![79, 0, 0], ![2, 1, 0], ![75, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![2, 1, 0], ![0, 2, 1], ![114, -18, 2]]]
  hmulB := by decide  
  f := ![![![77, 38, 0], ![-3002, 0, 0]], ![![-2, -1, 0], ![80, 0, 0]], ![![73, 36, 0], ![-2846, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 79, 0], ![-75, 0, 79]], ![![0, 1, 0], ![-1, 2, 1], ![0, -18, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![22, -2, 1]] ![![79, 0, 0], ![2, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![158, 79, 0]], ![![1738, -158, 79], ![158, 0, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![2, 1, 0]]], ![![![22, -2, 1]], ![![2, 0, 0]]]]
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


lemma PB174I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB174I1 : PrimesBelowBoundCertificateInterval O 31 79 174 where
  m := 11
  g := ![2, 2, 1, 2, 3, 1, 3, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB174I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
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
  β := ![I37N1, I41N1, I47N1, I53N0, I53N1, I53N2, I61N0, I61N1, I61N2, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [], [I47N1], [I53N0, I53N1, I53N2], [], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
