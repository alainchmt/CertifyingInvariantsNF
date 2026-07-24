
import IdealArithmetic.Examples.NF3_1_567567_2.RI3_1_567567_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![25, -4, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![25, -4, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![25, 33, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![25, -4, 1], ![93, -6, -17], ![-468, 140, 2]]]
  hmulB := by decide  
  f := ![![![-24, 4, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -33, 37]], ![![0, -1, 1], ![14, 15, -17], ![-14, 2, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [17, 0, 1] where
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
 g := ![![[], [33], [], [], [1]], ![[], [33], [], [], [1]]]
 h' := ![![[0, 36], [31], [0, 12], [30], [20], [0, 1]], ![[0, 1], [31], [0, 25], [30], [20], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [0, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [17, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154, 520, -944]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![642, 856, -944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![17, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![17, 1, 0]] 
 ![![37, 0, 0], ![17, 1, 0], ![35, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![17, 1, 0], ![2, 18, 4], ![101, -27, 16]]]
  hmulB := by decide  
  f := ![![![-752, -9057, -2016], ![-555, 18648, 0]], ![![-343, -4151, -924], ![-258, 8547, 0]], ![![-704, -8567, -1907], ![-541, 17640, 0]]]
  g := ![![![1, 0, 0], ![-17, 37, 0], ![-35, 0, 37]], ![![0, 1, 0], ![-12, 18, 4], ![0, -27, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![25, -4, 1]] ![![37, 0, 0], ![17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![629, 37, 0]], ![![925, -148, 37], ![518, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![17, 1, 0]]], ![![![25, -4, 1]], ![![14, -2, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [28, 0, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 13, 40], [7, 27, 1], [0, 1]]
 g := ![![[17, 25, 23], [9, 2], [33, 9], [37, 23, 1], []], ![[24, 14, 12, 8], [25, 40], [30, 5], [35, 5, 7, 9], [38, 1]], ![[4, 7, 26, 39], [34, 23], [14, 18], [6, 13, 2, 5], [36, 1]]]
 h' := ![![[16, 13, 40], [37, 30, 8], [17, 17, 17], [30, 12, 3], [0, 0, 1], [0, 1]], ![[7, 27, 1], [39, 9, 22], [1, 11, 32], [12, 8, 28], [12, 19, 27], [16, 13, 40]], ![[0, 1], [37, 2, 11], [28, 13, 33], [25, 21, 10], [25, 22, 13], [7, 27, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 12], []]
 b := ![[], [31, 7, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [28, 0, 18, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![581708, -196800, 63345]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14188, -4800, 1545]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![32, 13, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![32, 13, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![32, 13, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![32, 13, 1], ![127, 18, 51], ![1249, -319, -8]]]
  hmulB := by decide  
  f := ![![![-31, -13, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -13, 43]], ![![0, 0, 1], ![-35, -15, 51], ![35, -5, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 42], [0, 1]]
 g := ![![[18, 10], [0, 1], [9], [0, 17], [1]], ![[36, 33], [19, 42], [9], [22, 26], [1]]]
 h' := ![![[19, 42], [0, 28], [31, 42], [0, 3], [13, 19], [0, 1]], ![[0, 1], [16, 15], [12, 1], [14, 40], [30, 24], [19, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [9, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![121095, 552960, -979224]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![731541, 308904, -979224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-8, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-8, 1, 0]] 
 ![![43, 0, 0], ![35, 1, 0], ![8, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-8, 1, 0], ![2, -7, 4], ![101, -27, -9]]]
  hmulB := by decide  
  f := ![![![-967, 3577, -2048], ![301, 22016, 0]], ![![-791, 2907, -1664], ![216, 17888, 0]], ![![-176, 665, -381], ![77, 4096, 0]]]
  g := ![![![1, 0, 0], ![-35, 43, 0], ![-8, 0, 43]], ![![-1, 1, 0], ![5, -7, 4], ![26, -27, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![32, 13, 1]] ![![43, 0, 0], ![-8, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-344, 43, 0]], ![![1376, 559, 43], ![-129, -86, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-8, 1, 0]]], ![![![32, 13, 1]], ![![-3, -2, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, -11, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, -11, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![16, 36, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, -11, 1], ![79, -22, -45], ![-1175, 329, 0]]]
  hmulB := by decide  
  f := ![![![-15, 11, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -36, 47]], ![![0, -1, 1], ![17, 34, -45], ![-25, 7, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[11, 25], [3, 9], [16, 42], [44, 4], [1]], ![[8, 22], [32, 38], [26, 5], [36, 43], [1]]]
 h' := ![![[45, 46], [8, 42], [27, 3], [39, 29], [34, 45], [0, 1]], ![[0, 1], [18, 5], [21, 44], [28, 18], [38, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1704, 1195, -1305]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![408, 1025, -1305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-2, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-2, 1, 0]] 
 ![![47, 0, 0], ![45, 1, 0], ![0, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-2, 1, 0], ![2, -1, 4], ![101, -27, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![12, 12, 0]]]
  g := ![![![1, 0, 0], ![-45, 47, 0], ![0, 0, 47]], ![![-1, 1, 0], ![1, -1, 4], ![28, -27, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![16, -11, 1]] ![![47, 0, 0], ![-2, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-94, 47, 0]], ![![752, -517, 47], ![47, 0, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-2, 1, 0]]], ![![![16, -11, 1]], ![![1, 0, -1]]]]
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
 ![![53, 0, 0], ![7, 1, 0], ![13, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![7, 1, 0], ![2, 8, 4], ![101, -27, 6]]]
  hmulB := by decide  
  f := ![![![512, 2125, 1064], ![159, -14098, 0]], ![![63, 279, 140], ![54, -1855, 0]], ![![124, 521, 261], ![51, -3458, 0]]]
  g := ![![![1, 0, 0], ![-7, 53, 0], ![-13, 0, 53]], ![![0, 1, 0], ![-2, 8, 4], ![4, -27, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![44, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![2, 22, 4], ![101, -27, 20]]]
  hmulB := by decide  
  f := ![![![376, 5275, 960], ![265, -12720, 0]], ![![148, 2088, 380], ![107, -5035, 0]], ![![307, 4379, 797], ![233, -10560, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-44, 0, 53]], ![![0, 1, 0], ![-12, 22, 4], ![-4, -27, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![25, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![25, 1, 0]] 
 ![![53, 0, 0], ![25, 1, 0], ![50, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![25, 1, 0], ![2, 26, 4], ![101, -27, 24]]]
  hmulB := by decide  
  f := ![![![-504, -8833, -1360], ![-371, 18020, 0]], ![![-245, -4157, -640], ![-158, 8480, 0]], ![![-475, -8333, -1283], ![-351, 17000, 0]]]
  g := ![![![1, 0, 0], ![-25, 53, 0], ![-50, 0, 53]], ![![0, 1, 0], ![-16, 26, 4], ![-8, -27, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![7, 1, 0]] ![![53, 0, 0], ![21, 1, 0]]
  ![![53, 0, 0], ![24, -6, 1]] where
 M := ![![![2809, 0, 0], ![1113, 53, 0]], ![![371, 53, 0], ![149, 29, 4]]]
 hmul := by decide  
 g := ![![![![29, 6, -1], ![53, 0, 0]], ![![-3, 7, -1], ![53, 0, 0]]], ![![![-17, 7, -1], ![53, 0, 0]], ![![1, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![24, -6, 1]] ![![53, 0, 0], ![25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1325, 53, 0]], ![![1272, -318, 53], ![689, -159, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![25, 1, 0]]], ![![![24, -6, 1]], ![![13, -3, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![34, -10, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![34, -10, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![34, 49, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![34, -10, 1], ![81, -3, -41], ![-1074, 302, 17]]]
  hmulB := by decide  
  f := ![![![-33, 10, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -49, 59]], ![![0, -1, 1], ![25, 34, -41], ![-28, -9, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [10, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 58], [0, 1]]
 g := ![![[37, 53], [0, 27], [9], [7, 41], [43, 1]], ![[15, 6], [40, 32], [9], [0, 18], [27, 58]]]
 h' := ![![[43, 58], [0, 42], [31, 26], [48, 3], [42, 10], [0, 1]], ![[0, 1], [36, 17], [28, 33], [0, 56], [0, 49], [43, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [48, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [10, 16, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![99, 488, -1040]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![601, 872, -1040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-18, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-18, 1, 0]] 
 ![![59, 0, 0], ![41, 1, 0], ![42, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-18, 1, 0], ![2, -17, 4], ![101, -27, -19]]]
  hmulB := by decide  
  f := ![![![3601, -34856, 8208], ![-1652, -121068, 0]], ![![2509, -24206, 5700], ![-1120, -84075, 0]], ![![2568, -24813, 5843], ![-1161, -86184, 0]]]
  g := ![![![1, 0, 0], ![-41, 59, 0], ![-42, 0, 59]], ![![-1, 1, 0], ![9, -17, 4], ![34, -27, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![34, -10, 1]] ![![59, 0, 0], ![-18, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1062, 59, 0]], ![![2006, -590, 59], ![-531, 177, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-18, 1, 0]]], ![![![34, -10, 1]], ![![-9, 3, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![33, -29, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![33, -29, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![33, 32, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![33, -29, 1], ![43, -23, -117], ![-2993, 815, 35]]]
  hmulB := by decide  
  f := ![![![-32, 29, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -32, 61]], ![![0, -1, 1], ![64, 61, -117], ![-68, -5, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [16, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 60], [0, 1]]
 g := ![![[10, 42], [1], [5, 46], [1, 15], [23, 1]], ![[0, 19], [1], [26, 15], [41, 46], [46, 60]]]
 h' := ![![[23, 60], [40, 46], [42, 1], [45, 31], [59, 25], [0, 1]], ![[0, 1], [0, 15], [4, 60], [26, 30], [24, 36], [23, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [60, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [16, 38, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63591, 15975, -51021]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28644, 27027, -51021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-5, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-5, 1, 0]] 
 ![![61, 0, 0], ![56, 1, 0], ![26, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-5, 1, 0], ![2, -4, 4], ![101, -27, -6]]]
  hmulB := by decide  
  f := ![![![-565, 1150, -1152], ![122, 17568, 0]], ![![-522, 1055, -1056], ![62, 16104, 0]], ![![-240, 490, -491], ![62, 7488, 0]]]
  g := ![![![1, 0, 0], ![-56, 61, 0], ![-26, 0, 61]], ![![-1, 1, 0], ![2, -4, 4], ![29, -27, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![33, -29, 1]] ![![61, 0, 0], ![-5, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-305, 61, 0]], ![![2013, -1769, 61], ![-122, 122, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-5, 1, 0]]], ![![![33, -29, 1]], ![![-2, 2, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, 11, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, 11, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![20, 11, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, 11, 1], ![123, 4, 43], ![1047, -265, -18]]]
  hmulB := by decide  
  f := ![![![-19, -11, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -11, 67]], ![![0, 0, 1], ![-11, -7, 43], ![21, -1, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [47, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 66], [0, 1]]
 g := ![![[23, 10], [8, 25], [49], [21], [14], [1]], ![[0, 57], [51, 42], [49], [21], [14], [1]]]
 h' := ![![[58, 66], [26, 55], [30, 5], [51, 7], [10, 50], [20, 58], [0, 1]], ![[0, 1], [0, 12], [52, 62], [55, 60], [29, 17], [34, 9], [58, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [22, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [47, 9, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-225, 94, -28]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 6, -28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![24, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![24, 1, 0]] 
 ![![67, 0, 0], ![24, 1, 0], ![18, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![24, 1, 0], ![2, 25, 4], ![101, -27, 23]]]
  hmulB := by decide  
  f := ![![![-1043, -15741, -2520], ![-603, 42210, 0]], ![![-378, -5622, -900], ![-200, 15075, 0]], ![![-282, -4229, -677], ![-157, 11340, 0]]]
  g := ![![![1, 0, 0], ![-24, 67, 0], ![-18, 0, 67]], ![![0, 1, 0], ![-10, 25, 4], ![5, -27, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![20, 11, 1]] ![![67, 0, 0], ![24, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1608, 67, 0]], ![![1340, 737, 67], ![603, 268, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![24, 1, 0]]], ![![![20, 11, 1]], ![![9, 4, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4599, -810, -1090]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![4599, -810, -1090]] 
 ![![71, 0, 0], ![0, 71, 0], ![12, 4, 1]] where
  M :=![![![4599, -810, -1090], ![-111710, 33219, -2150], ![-12050, -13010, 34839]]]
  hmulB := by decide  
  f := ![![![-15906271, -597190, -534510]], ![![-55179890, -2071691, -1854250]], ![![-6164822, -231454, -207161]]]
  g := ![![![249, 50, -1090], ![-1210, 589, -2150], ![-6058, -2146, 34839]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 30, 1] where
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
 g := ![![[37, 32], [70, 32], [12, 64], [19], [48], [1]], ![[0, 39], [33, 39], [9, 7], [19], [48], [1]]]
 h' := ![![[41, 70], [20, 48], [44, 23], [39, 63], [8, 44], [51, 41], [0, 1]], ![[0, 1], [0, 23], [64, 48], [66, 8], [37, 27], [28, 30], [41, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [32, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [20, 30, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127, 1709, -2324]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![391, 155, -2324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15906271, 597190, 534510]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![15906271, 597190, 534510]] 
 ![![71, 0, 0], ![56, 1, 0], ![19, 0, 1]] where
  M :=![![![15906271, 597190, 534510], ![55179890, 2071691, 1854250], ![26107550, 980190, 877311]]]
  hmulB := by decide  
  f := ![![![-4599, 810, 1090]], ![![-2054, 171, 890]], ![![-1061, 400, -199]]]
  g := ![![![-390029, 597190, 534510], ![-1353036, 2071691, 1854250], ![-640169, 980190, 877311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![4599, -810, -1090]] ![![15906271, 597190, 534510]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [8, 13, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 68, 45], [49, 4, 28], [0, 1]]
 g := ![![[9, 68, 16], [1, 57], [36, 55], [6, 72, 25], [50, 1], []], ![[12, 23, 42, 7], [43, 65], [53, 1], [57, 63, 51, 20], [3, 16], [60, 54]], ![[12, 42, 45, 45], [39, 50], [5, 57], [33, 25, 18, 31], [53, 25], [4, 54]]]
 h' := ![![[1, 68, 45], [46, 55, 69], [45, 48, 38], [25, 60, 37], [38, 72, 5], [0, 0, 1], [0, 1]], ![[49, 4, 28], [46, 14, 50], [68, 44, 49], [28, 38, 1], [51, 27, 48], [32, 19, 4], [1, 68, 45]], ![[0, 1], [54, 4, 27], [1, 54, 59], [25, 48, 35], [8, 47, 20], [33, 54, 68], [49, 4, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 22], []]
 b := ![[], [33, 1, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [8, 13, 23, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7633172, 3357635, -2494045]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104564, 45995, -34165]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-21, -34, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-21, -34, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![58, 45, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-21, -34, 1], ![33, -82, -137], ![-3498, 950, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -45, 79]], ![![-1, -1, 1], ![101, 77, -137], ![-34, 20, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [38, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 78], [0, 1]]
 g := ![![[57, 52], [58, 64], [18, 25], [72, 65], [62], [1]], ![[0, 27], [0, 15], [62, 54], [60, 14], [62], [1]]]
 h' := ![![[46, 78], [8, 17], [27, 8], [29, 5], [36, 67], [41, 46], [0, 1]], ![[0, 1], [0, 62], [0, 71], [22, 74], [37, 12], [24, 33], [46, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [3, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [38, 33, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5016, -930, -1074]
  a := ![-2, -6, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![852, 600, -1074]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-21, 1, 0]] 
 ![![79, 0, 0], ![58, 1, 0], ![14, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-21, 1, 0], ![2, -20, 4], ![101, -27, -22]]]
  hmulB := by decide  
  f := ![![![-1322, 14693, -2940], ![553, 58065, 0]], ![![-972, 10775, -2156], ![396, 42581, 0]], ![![-217, 2603, -521], ![163, 10290, 0]]]
  g := ![![![1, 0, 0], ![-58, 79, 0], ![-14, 0, 79]], ![![-1, 1, 0], ![14, -20, 4], ![25, -27, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-21, -34, 1]] ![![79, 0, 0], ![-21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1659, 79, 0]], ![![-1659, -2686, 79], ![474, 632, -158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-21, 1, 0]]], ![![![-21, -34, 1]], ![![6, 8, -2]]]]
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


lemma PB214I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB214I1 : PrimesBelowBoundCertificateInterval O 31 79 214 where
  m := 11
  g := ![2, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB214I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![389017]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I47N1, I53N0, I53N1, I53N2, I59N1, I61N1, I67N1, I71N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [I61N1], [I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
