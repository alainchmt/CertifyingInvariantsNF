
import IdealArithmetic.Examples.NF3_3_370548_2.RI3_3_370548_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [29, 18, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 14, 10], [7, 22, 27], [0, 1]]
 g := ![![[1, 6, 34], [3, 7], [8, 24, 3], [15, 1], []], ![[31, 7, 4, 33], [22, 28], [33, 15, 1, 1], [12, 3], [4, 26]], ![[24, 18, 30, 28], [5, 26], [20, 17, 11, 9], [1, 11], [24, 26]]]
 h' := ![![[8, 14, 10], [13, 12, 16], [27, 18, 28], [9, 34, 22], [0, 0, 1], [0, 1]], ![[7, 22, 27], [17, 8, 28], [10, 9, 19], [25, 34, 10], [22, 27, 22], [8, 14, 10]], ![[0, 1], [31, 17, 30], [19, 10, 27], [36, 6, 5], [19, 10, 14], [7, 22, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 15], []]
 b := ![[], [4, 31, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [29, 18, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23569, -10434, -1924]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-637, -282, -52]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [6, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 13, 32], [19, 27, 9], [0, 1]]
 g := ![![[24, 21, 23], [1, 2], [10, 32], [4, 39, 1], []], ![[17, 38, 12, 31], [21, 40], [24, 36], [6, 37, 7, 40], [14, 40]], ![[37, 19, 26, 23], [22, 23], [3, 23], [35, 6, 2, 4], [37, 40]]]
 h' := ![![[20, 13, 32], [37, 24, 33], [24, 11, 17], [17, 12, 27], [0, 0, 1], [0, 1]], ![[19, 27, 9], [39, 40, 19], [40, 24, 32], [15, 8, 6], [29, 34, 27], [20, 13, 32]], ![[0, 1], [37, 18, 30], [13, 6, 33], [21, 21, 8], [16, 7, 13], [19, 27, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 12], []]
 b := ![[], [33, 34, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [6, 0, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-101147, 58589, 57769]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2467, 1429, 1409]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [22, 22, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 24, 27], [5, 18, 16], [0, 1]]
 g := ![![[27, 0, 6], [8, 21, 41], [38, 15], [18, 13, 1], []], ![[30, 40, 4, 26], [28, 22, 23, 12], [1, 38], [20, 29, 18, 19], [23, 41]], ![[9, 13, 18, 16], [34, 19, 36, 16], [2, 9], [19, 35, 20, 14], [34, 41]]]
 h' := ![![[8, 24, 27], [39, 24, 36], [19, 16, 27], [34, 6, 12], [0, 0, 1], [0, 1]], ![[5, 18, 16], [14, 4, 6], [38, 41, 15], [24, 25, 34], [31, 8, 18], [8, 24, 27]], ![[0, 1], [17, 15, 1], [14, 29, 1], [31, 12, 40], [8, 35, 24], [5, 18, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [12, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [22, 22, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85312, 12814, -18748]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1984, 298, -436]
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


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![9, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![9, 1, 0]] 
 ![![47, 0, 0], ![9, 1, 0], ![30, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![9, 1, 0], ![0, 9, 2], ![138, 48, 9]]]
  hmulB := by decide  
  f := ![![![154, 17, 0], ![-799, 0, 0]], ![![18, 2, 0], ![-93, 0, 0]], ![![96, 6, -1], ![-498, 24, 0]]]
  g := ![![![1, 0, 0], ![-9, 47, 0], ![-30, 0, 47]], ![![0, 1, 0], ![-3, 9, 2], ![-12, 48, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![19, 1, 0]] 
 ![![47, 0, 0], ![19, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![19, 1, 0], ![0, 19, 2], ![138, 48, 19]]]
  hmulB := by decide  
  f := ![![![58, 3, 0], ![-141, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![52, -7, -1], ![-127, 24, 0]]]
  g := ![![![1, 0, 0], ![-19, 47, 0], ![-31, 0, 47]], ![![0, 1, 0], ![-9, 19, 2], ![-29, 48, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![9, 1, 0]] ![![47, 0, 0], ![19, 1, 0]]
  ![![47, 0, 0], ![-32, 14, 1]] where
 M := ![![![2209, 0, 0], ![893, 47, 0]], ![![423, 47, 0], ![171, 28, 2]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![19, 1, 0], ![0, 0, 0]]], ![![![9, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-32, 14, 1]] ![![47, 0, 0], ![19, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![893, 47, 0]], ![![-1504, 658, 47], ![-470, 282, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![19, 1, 0]]], ![![![-32, 14, 1]], ![![-10, 6, 1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![53, 0, 0], ![7, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 2], ![138, 48, 7]]]
  hmulB := by decide  
  f := ![![![47, 7, -2]], ![![1, 0, 0]], ![![20, 4, -1]]]
  g := ![![![0, 1, 0], ![-1, 7, 2], ![-4, 48, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-6, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-6, 1, 0]] 
 ![![53, 0, 0], ![47, 1, 0], ![35, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-6, 1, 0], ![0, -6, 2], ![138, 48, -6]]]
  hmulB := by decide  
  f := ![![![67, -11, 0], ![583, 0, 0]], ![![61, -10, 0], ![531, 0, 0]], ![![49, -5, -1], ![427, 27, 0]]]
  g := ![![![1, 0, 0], ![-47, 53, 0], ![-35, 0, 53]], ![![-1, 1, 0], ![4, -6, 2], ![-36, 48, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-1, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-1, 1, 0]] 
 ![![53, 0, 0], ![52, 1, 0], ![26, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-1, 1, 0], ![0, -1, 2], ![138, 48, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![159, 0, 0]], ![![2, -1, 0], ![54, 0, 0]], ![![2, -1, -1], ![80, 27, 0]]]
  g := ![![![1, 0, 0], ![-52, 53, 0], ![-26, 0, 53]], ![![-1, 1, 0], ![0, -1, 2], ![-44, 48, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![7, 1, 0]] ![![53, 0, 0], ![-6, 1, 0]]
  ![![53, 0, 0], ![-21, -26, 1]] where
 M := ![![![371, 53, 0], ![-42, 1, 2]]]
 hmul := by decide  
 g := ![![![![7, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-21, -26, 1]] ![![53, 0, 0], ![-1, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-53, 53, 0]], ![![-1113, -1378, 53], ![159, 53, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-1, 1, 0]]], ![![![-21, -26, 1]], ![![3, 1, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-27, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-27, 1, 0]] 
 ![![59, 0, 0], ![32, 1, 0], ![19, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-27, 1, 0], ![0, -27, 2], ![138, 48, -27]]]
  hmulB := by decide  
  f := ![![![1270, -47, 0], ![2773, 0, 0]], ![![676, -25, 0], ![1476, 0, 0]], ![![452, -3, -1], ![987, 30, 0]]]
  g := ![![![1, 0, 0], ![-32, 59, 0], ![-19, 0, 59]], ![![-1, 1, 0], ![14, -27, 2], ![-15, 48, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-22, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-22, 1, 0]] 
 ![![59, 0, 0], ![37, 1, 0], ![53, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-22, 1, 0], ![0, -22, 2], ![138, 48, -22]]]
  hmulB := by decide  
  f := ![![![1255, -57, 0], ![3363, 0, 0]], ![![793, -36, 0], ![2125, 0, 0]], ![![1105, -39, -1], ![2961, 30, 0]]]
  g := ![![![1, 0, 0], ![-37, 59, 0], ![-53, 0, 59]], ![![-1, 1, 0], ![12, -22, 2], ![-8, 48, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-10, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-10, 1, 0]] 
 ![![59, 0, 0], ![49, 1, 0], ![9, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-10, 1, 0], ![0, -10, 2], ![138, 48, -10]]]
  hmulB := by decide  
  f := ![![![81, -8, 0], ![472, 0, 0]], ![![71, -7, 0], ![414, 0, 0]], ![![31, 2, -1], ![182, 30, 0]]]
  g := ![![![1, 0, 0], ![-49, 59, 0], ![-9, 0, 59]], ![![-1, 1, 0], ![8, -10, 2], ![-36, 48, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-27, 1, 0]] ![![59, 0, 0], ![-22, 1, 0]]
  ![![59, 0, 0], ![-57, 5, 1]] where
 M := ![![![3481, 0, 0], ![-1298, 59, 0]], ![![-1593, 59, 0], ![594, -49, 2]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![35, -4, -1], ![59, 0, 0]]], ![![![30, -4, -1], ![59, 0, 0]], ![![12, -1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-57, 5, 1]] ![![59, 0, 0], ![-10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-590, 59, 0]], ![![-3363, 295, 59], ![708, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-10, 1, 0]]], ![![![-57, 5, 1]], ![![12, -1, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [26, 20, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 50, 27], [8, 10, 34], [0, 1]]
 g := ![![[23, 30, 15], [4, 58], [34, 31, 13], [1, 2, 34], [1]], ![[3, 15, 56, 22], [16, 9], [28, 28, 52, 14], [59, 17, 31, 13], [15, 47, 4, 41]], ![[1, 23, 54, 57], [45, 27], [2, 35, 15, 41], [13, 29, 1, 25], [4, 7, 5, 20]]]
 h' := ![![[12, 50, 27], [3, 42, 36], [31, 44, 34], [35, 55, 14], [35, 41, 20], [0, 1]], ![[8, 10, 34], [27, 0, 30], [4, 54, 3], [0, 22, 39], [57, 9, 26], [12, 50, 27]], ![[0, 1], [54, 19, 56], [2, 24, 24], [49, 45, 8], [42, 11, 15], [8, 10, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 34], []]
 b := ![[], [21, 8, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [26, 20, 41, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-114314, -103029, -40565]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1874, -1689, -665]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-313, -68, 18]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-313, -68, 18]] 
 ![![67, 0, 0], ![0, 67, 0], ![31, 26, 1]] where
  M :=![![![-313, -68, 18], ![2484, 551, -136], ![-9384, -2022, 551]]]
  hmulB := by decide  
  f := ![![![-427, -16, 10]], ![![1380, 53, -32]], ![![305, 12, -7]]]
  g := ![![![-13, -8, 18], ![100, 61, -136], ![-395, -244, 551]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [14, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 66], [0, 1]]
 g := ![![[31, 24], [4, 40], [54], [65], [19], [1]], ![[0, 43], [64, 27], [54], [65], [19], [1]]]
 h' := ![![[35, 66], [11, 15], [10, 24], [37, 11], [64, 20], [53, 35], [0, 1]], ![[0, 1], [0, 52], [46, 43], [20, 56], [27, 47], [5, 32], [35, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [57, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [14, 32, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![290, 133, 18]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -5, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-427, -16, 10]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-427, -16, 10]] 
 ![![67, 0, 0], ![15, 1, 0], ![55, 0, 1]] where
  M :=![![![-427, -16, 10], ![1380, 53, -32], ![-2208, -78, 53]]]
  hmulB := by decide  
  f := ![![![-313, -68, 18]], ![![-33, -7, 2]], ![![-397, -86, 23]]]
  g := ![![![-11, -16, 10], ![35, 53, -32], ![-59, -78, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-313, -68, 18]] ![![-427, -16, 10]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-47, -6, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-47, -6, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![24, 65, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-47, -6, 1], ![138, 1, -12], ![-828, -219, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -65, 71]], ![![-1, -1, 1], ![6, 11, -12], ![-12, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 70], [0, 1]]
 g := ![![[8, 5], [6, 57], [13, 57], [64], [48], [1]], ![[0, 66], [0, 14], [7, 14], [64], [48], [1]]]
 h' := ![![[41, 70], [13, 17], [40, 25], [16, 25], [16, 63], [14, 41], [0, 1]], ![[0, 1], [0, 54], [0, 46], [47, 46], [43, 8], [62, 30], [41, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [12, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [57, 30, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5332, 2501, 802]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-196, -699, 802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![12, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![12, 1, 0]] 
 ![![71, 0, 0], ![12, 1, 0], ![70, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![12, 1, 0], ![0, 12, 2], ![138, 48, 12]]]
  hmulB := by decide  
  f := ![![![49, 4, 0], ![-284, 0, 0]], ![![-12, -1, 0], ![72, 0, 0]], ![![50, -2, -1], ![-290, 36, 0]]]
  g := ![![![1, 0, 0], ![-12, 71, 0], ![-70, 0, 71]], ![![0, 1, 0], ![-4, 12, 2], ![-18, 48, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-47, -6, 1]] ![![71, 0, 0], ![12, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![852, 71, 0]], ![![-3337, -426, 71], ![-426, -71, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![12, 1, 0]]], ![![![-47, -6, 1]], ![![-6, -1, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![18, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![18, 1, 0]] 
 ![![73, 0, 0], ![18, 1, 0], ![57, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![18, 1, 0], ![0, 18, 2], ![138, 48, 18]]]
  hmulB := by decide  
  f := ![![![667, 37, 0], ![-2701, 0, 0]], ![![162, 9, 0], ![-656, 0, 0]], ![![543, 21, -1], ![-2199, 37, 0]]]
  g := ![![![1, 0, 0], ![-18, 73, 0], ![-57, 0, 73]], ![![0, 1, 0], ![-6, 18, 2], ![-24, 48, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-36, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-36, 1, 0]] 
 ![![73, 0, 0], ![37, 1, 0], ![9, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-36, 1, 0], ![0, -36, 2], ![138, 48, -36]]]
  hmulB := by decide  
  f := ![![![2629, -73, 0], ![5329, 0, 0]], ![![1369, -38, 0], ![2775, 0, 0]], ![![333, 9, -1], ![675, 37, 0]]]
  g := ![![![1, 0, 0], ![-37, 73, 0], ![-9, 0, 73]], ![![-1, 1, 0], ![18, -36, 2], ![-18, 48, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![18, 1, 0]] ![![73, 0, 0], ![18, 1, 0]]
  ![![73, 0, 0], ![-57, 18, 1]] where
 M := ![![![5329, 0, 0], ![1314, 73, 0]], ![![1314, 73, 0], ![324, 36, 2]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![18, 1, 0], ![0, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-57, 18, 1]] ![![73, 0, 0], ![-36, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2628, 73, 0]], ![![-4161, 1314, 73], ![2190, -657, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-36, 1, 0]]], ![![![-57, 18, 1]], ![![30, -9, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![79, 0, 0], ![5, 1, 0], ![27, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 2], ![138, 48, 5]]]
  hmulB := by decide  
  f := ![![![71, 5, -2]], ![![1, 0, 0]], ![![33, 3, -1]]]
  g := ![![![0, 1, 0], ![-1, 5, 2], ![-3, 48, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![10, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![10, 1, 0]] 
 ![![79, 0, 0], ![10, 1, 0], ![29, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![10, 1, 0], ![0, 10, 2], ![138, 48, 10]]]
  hmulB := by decide  
  f := ![![![61, 6, 0], ![-474, 0, 0]], ![![-10, -1, 0], ![80, 0, 0]], ![![11, -4, -1], ![-84, 40, 0]]]
  g := ![![![1, 0, 0], ![-10, 79, 0], ![-29, 0, 79]], ![![0, 1, 0], ![-2, 10, 2], ![-8, 48, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-15, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-15, 1, 0]] 
 ![![79, 0, 0], ![64, 1, 0], ![6, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-15, 1, 0], ![0, -15, 2], ![138, 48, -15]]]
  hmulB := by decide  
  f := ![![![961, -64, 0], ![5056, 0, 0]], ![![796, -53, 0], ![4188, 0, 0]], ![![84, 2, -1], ![442, 40, 0]]]
  g := ![![![1, 0, 0], ![-64, 79, 0], ![-6, 0, 79]], ![![-1, 1, 0], ![12, -15, 2], ![-36, 48, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![5, 1, 0]] ![![79, 0, 0], ![10, 1, 0]]
  ![![79, 0, 0], ![-54, -32, 1]] where
 M := ![![![395, 79, 0], ![50, 15, 2]]]
 hmul := by decide  
 g := ![![![![5, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-54, -32, 1]] ![![79, 0, 0], ![-15, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1185, 79, 0]], ![![-4266, -2528, 79], ![948, 474, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-15, 1, 0]]], ![![![-54, -32, 1]], ![![12, 6, -1]]]]
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


lemma PB136I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB136I1 : PrimesBelowBoundCertificateInterval O 31 79 136 where
  m := 11
  g := ![1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB136I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N0, I73N1]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
      exact NI59N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I47N0, I47N1, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I67N1, I71N1, I73N0, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [], [], [I47N0, I47N1, I47N1], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [], [I67N1], [I71N1], [I73N0, I73N0, I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
