
import IdealArithmetic.Examples.NF3_1_356631_2.RI3_1_356631_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [5, 25, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 24, 17], [25, 12, 20], [0, 1]]
 g := ![![[5, 2, 26], [30, 11], [14, 28, 33], [0, 1], []], ![[13, 26, 21, 19], [15, 33], [31, 32, 21, 14], [33, 33], [2, 30]], ![[2, 4, 14, 8], [15, 4], [30, 18, 30, 32], [8, 21], [36, 30]]]
 h' := ![![[12, 24, 17], [14, 11, 27], [4, 28, 23], [0, 32, 12], [0, 0, 1], [0, 1]], ![[25, 12, 20], [27, 19, 30], [18, 33, 12], [31, 26, 22], [23, 6, 12], [12, 24, 17]], ![[0, 1], [20, 7, 17], [24, 13, 2], [35, 16, 3], [1, 31, 24], [25, 12, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 23], []]
 b := ![[], [32, 27, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [5, 25, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33448, -9472, -2294]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-904, -256, -62]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-43, -11, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-43, -11, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![39, 30, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-43, -11, 1], ![189, -6, -33], ![-2079, -344, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -30, 41]], ![![-2, -1, 1], ![36, 24, -33], ![-45, -4, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [30, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 40], [0, 1]]
 g := ![![[38, 23], [33], [20], [32, 23], [1]], ![[17, 18], [33], [20], [11, 18], [1]]]
 h' := ![![[8, 40], [37, 8], [17, 19], [24, 15], [11, 8], [0, 1]], ![[0, 1], [19, 33], [5, 22], [21, 26], [34, 33], [8, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [35, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [30, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2270, 61, 438]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-472, -319, 438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-8, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-8, 1, 0]] 
 ![![41, 0, 0], ![33, 1, 0], ![6, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-8, 1, 0], ![0, -8, 3], ![189, 37, -8]]]
  hmulB := by decide  
  f := ![![![305, -38, 0], ![1558, 0, 0]], ![![249, -31, 0], ![1272, 0, 0]], ![![54, -4, -1], ![276, 14, 0]]]
  g := ![![![1, 0, 0], ![-33, 41, 0], ![-6, 0, 41]], ![![-1, 1, 0], ![6, -8, 3], ![-24, 37, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-43, -11, 1]] ![![41, 0, 0], ![-8, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-328, 41, 0]], ![![-1763, -451, 41], ![533, 82, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-8, 1, 0]]], ![![![-43, -11, 1]], ![![13, 2, -1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [40, 21, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 0, 6], [10, 42, 37], [0, 1]]
 g := ![![[37, 2, 41], [33, 42, 13], [40, 1], [0, 35, 1], []], ![[4, 24, 38, 16], [24, 16, 7, 38], [4, 24], [39, 32, 40, 6], [13, 36]], ![[23, 6, 1, 3], [2, 13, 6, 30], [33, 10], [18, 7], [25, 36]]]
 h' := ![![[25, 0, 6], [13, 30, 27], [34, 23, 20], [0, 19, 42], [0, 0, 1], [0, 1]], ![[10, 42, 37], [29, 17, 24], [0, 11, 32], [26, 36, 29], [19, 7, 42], [25, 0, 6]], ![[0, 1], [7, 39, 35], [23, 9, 34], [15, 31, 15], [3, 36], [10, 42, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 27], []]
 b := ![[], [21, 7, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [40, 21, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-151489, 12298, -19780]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3523, 286, -460]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16294, -4493, -1078]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-16294, -4493, -1078]] 
 ![![47, 0, 0], ![0, 47, 0], ![5, 22, 1]] where
  M :=![![![-16294, -4493, -1078], ![-203742, -56180, -13479], ![-849177, -234155, -56180]]]
  hmulB := by decide  
  f := ![![![-365, -50, 19]], ![![3591, 338, -150]], ![![1441, 139, -61]]]
  g := ![![![-232, 409, -1078], ![-2901, 5114, -13479], ![-12091, 21315, -56180]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [35, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 46], [0, 1]]
 g := ![![[18, 36], [1, 16], [35, 7], [17, 32], [1]], ![[39, 11], [26, 31], [43, 40], [20, 15], [1]]]
 h' := ![![[28, 46], [12, 41], [44, 4], [16, 17], [12, 28], [0, 1]], ![[0, 1], [32, 6], [15, 43], [22, 30], [44, 19], [28, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [45, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [35, 19, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1079, 366, 273]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -120, 273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365, 50, -19]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![365, 50, -19]] 
 ![![47, 0, 0], ![28, 1, 0], ![5, 0, 1]] where
  M :=![![![365, 50, -19], ![-3591, -338, 150], ![9450, 653, -338]]]
  hmulB := by decide  
  f := ![![![16294, 4493, 1078]], ![![14042, 3872, 929]], ![![19801, 5460, 1310]]]
  g := ![![![-20, 50, -19], ![109, -338, 150], ![-152, 653, -338]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-16294, -4493, -1078]] ![![365, 50, -19]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [22, 2, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 29, 14], [38, 23, 39], [0, 1]]
 g := ![![[34, 19, 29], [11, 17], [18, 2, 4], [45, 17], [1]], ![[6, 50, 28, 2], [33, 25], [5, 52, 8, 8], [6, 43], [32, 2, 26, 41]], ![[8, 14, 31, 27], [3, 40], [32, 9, 15, 8], [18, 4], [10, 11, 22, 12]]]
 h' := ![![[47, 29, 14], [12, 32, 33], [28, 19, 32], [24, 48, 2], [31, 51, 32], [0, 1]], ![[38, 23, 39], [31, 22, 41], [11, 29, 48], [17, 41, 29], [34, 3, 19], [47, 29, 14]], ![[0, 1], [15, 52, 32], [9, 5, 26], [3, 17, 22], [9, 52, 2], [38, 23, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 6], []]
 b := ![[], [43, 17, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [22, 2, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25493, -6572, -1431]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-481, -124, -27]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-51, -29, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-51, -29, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![8, 30, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-51, -29, 1], ![189, -14, -87], ![-5481, -1010, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -30, 59]], ![![-1, -1, 1], ![15, 44, -87], ![-91, -10, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [35, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 58], [0, 1]]
 g := ![![[21, 27], [44, 51], [7], [49, 19], [32, 1]], ![[0, 32], [24, 8], [7], [8, 40], [5, 58]]]
 h' := ![![[32, 58], [53, 26], [7, 13], [55, 19], [1, 45], [0, 1]], ![[0, 1], [0, 33], [10, 46], [14, 40], [25, 14], [32, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [27, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [35, 27, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7245, 2020, 1149]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -550, 1149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, 1, 0]] 
 ![![59, 0, 0], ![28, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, 1, 0], ![0, 28, 3], ![189, 37, 28]]]
  hmulB := by decide  
  f := ![![![365, 13, 0], ![-767, 0, 0]], ![![140, 5, 0], ![-294, 0, 0]], ![![42, -8, -1], ![-88, 20, 0]]]
  g := ![![![1, 0, 0], ![-28, 59, 0], ![-14, 0, 59]], ![![0, 1, 0], ![-14, 28, 3], ![-21, 37, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-51, -29, 1]] ![![59, 0, 0], ![28, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1652, 59, 0]], ![![-3009, -1711, 59], ![-1239, -826, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![28, 1, 0]]], ![![![-51, -29, 1]], ![![-21, -14, -1]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [20, 26, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 31, 41], [50, 29, 20], [0, 1]]
 g := ![![[46, 43, 22], [41, 19], [8, 53, 49], [36, 30, 12], [1]], ![[23, 33, 35, 16], [50, 25], [29, 0, 9, 1], [19, 43, 39, 49], [50, 5, 12, 52]], ![[8, 57, 16, 9], [35, 41], [45, 9, 58, 20], [17, 31, 33, 36], [46, 54, 8, 9]]]
 h' := ![![[56, 31, 41], [14, 42, 49], [23, 35, 18], [12, 23, 54], [41, 35, 45], [0, 1]], ![[50, 29, 20], [52, 23, 32], [25, 45, 5], [1, 33, 8], [34, 10, 56], [56, 31, 41]], ![[0, 1], [28, 57, 41], [22, 42, 38], [57, 5, 60], [6, 16, 21], [50, 29, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 42], []]
 b := ![[], [11, 7, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [20, 26, 16, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51606, 3477, -1830]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![846, 57, -30]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [20, 10, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 15, 2], [18, 51, 65], [0, 1]]
 g := ![![[27, 47, 9], [52, 51, 21], [3, 25], [44, 24], [14, 1], []], ![[52, 65, 54, 48], [9, 35, 40, 7], [59, 4], [16, 35], [3, 55], [49, 4]], ![[21, 14, 6, 22], [30, 17, 7, 56], [54, 9], [52, 47], [65, 24], [53, 4]]]
 h' := ![![[63, 15, 2], [32, 65, 3], [8, 17, 50], [1, 39, 5], [55, 41, 52], [0, 0, 1], [0, 1]], ![[18, 51, 65], [29, 44, 15], [47, 59, 38], [50, 16, 65], [13, 44, 54], [41, 47, 51], [63, 15, 2]], ![[0, 1], [66, 25, 49], [29, 58, 46], [38, 12, 64], [41, 49, 28], [1, 20, 15], [18, 51, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 21], []]
 b := ![[], [60, 52, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [20, 10, 53, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![219827, 76179, 21909]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3281, 1137, 327]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![27, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![27, 1, 0]] 
 ![![71, 0, 0], ![27, 1, 0], ![41, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![27, 1, 0], ![0, 27, 3], ![189, 37, 27]]]
  hmulB := by decide  
  f := ![![![703, 26, 0], ![-1846, 0, 0]], ![![243, 9, 0], ![-638, 0, 0]], ![![409, 6, -1], ![-1074, 24, 0]]]
  g := ![![![1, 0, 0], ![-27, 71, 0], ![-41, 0, 71]], ![![0, 1, 0], ![-12, 27, 3], ![-27, 37, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-25, 1, 0]] 
 ![![71, 0, 0], ![46, 1, 0], ![52, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-25, 1, 0], ![0, -25, 3], ![189, 37, -25]]]
  hmulB := by decide  
  f := ![![![1601, -64, 0], ![4544, 0, 0]], ![![1026, -41, 0], ![2912, 0, 0]], ![![1162, -38, -1], ![3298, 24, 0]]]
  g := ![![![1, 0, 0], ![-46, 71, 0], ![-52, 0, 71]], ![![-1, 1, 0], ![14, -25, 3], ![-3, 37, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5759, -1588, -381]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-5759, -1588, -381]] 
 ![![71, 0, 0], ![69, 1, 0], ![46, 0, 1]] where
  M :=![![![-5759, -1588, -381], ![-72009, -19856, -4764], ![-300132, -82759, -19856]]]
  hmulB := by decide  
  f := ![![![3140, 149, -96]], ![![2796, 139, -87]], ![![2431, 89, -68]]]
  g := ![![![1709, -1588, -381], ![21369, -19856, -4764], ![89065, -82759, -19856]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![27, 1, 0]] ![![71, 0, 0], ![-25, 1, 0]]
  ![![-3140, -149, 96]] where
 M := ![![![5041, 0, 0], ![-1775, 71, 0]], ![![1917, 71, 0], ![-675, 2, 3]]]
 hmul := by decide  
 g := ![![![![408889, 112748, 27051]], ![![-71966, -19844, -4761]]], ![![![227502, 62732, 15051]], ![![-40041, -11041, -2649]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-3140, -149, 96]] ![![-5759, -1588, -381]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-55, -33, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-55, -33, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![18, 40, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-55, -33, 1], ![189, -18, -99], ![-6237, -1158, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -40, 73]], ![![-1, -1, 1], ![27, 54, -99], ![-81, -6, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [35, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 72], [0, 1]]
 g := ![![[25, 48], [54], [24], [46, 16], [1], [1]], ![[0, 25], [54], [24], [62, 57], [1], [1]]]
 h' := ![![[1, 72], [11, 62], [52, 45], [69, 43], [22, 4], [38, 1], [0, 1]], ![[0, 1], [0, 11], [24, 28], [39, 30], [26, 69], [39, 72], [1, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [21, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [35, 72, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7377, -1988, 600]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-249, -356, 600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![26, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![26, 1, 0]] 
 ![![73, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![26, 1, 0], ![0, 26, 3], ![189, 37, 26]]]
  hmulB := by decide  
  f := ![![![703, 27, 0], ![-1971, 0, 0]], ![![234, 9, 0], ![-656, 0, 0]], ![![142, -12, -2], ![-398, 49, 0]]]
  g := ![![![1, 0, 0], ![-26, 73, 0], ![-18, 0, 73]], ![![0, 1, 0], ![-10, 26, 3], ![-17, 37, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-55, -33, 1]] ![![73, 0, 0], ![26, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1898, 73, 0]], ![![-4015, -2409, 73], ![-1241, -876, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![26, 1, 0]]], ![![![-55, -33, 1]], ![![-17, -12, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-38, -37, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-38, -37, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![41, 42, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-38, -37, 1], ![189, -1, -111], ![-6993, -1306, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -42, 79]], ![![-1, -1, 1], ![60, 59, -111], ![-88, -16, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [35, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 78], [0, 1]]
 g := ![![[68, 62], [57, 31], [20, 25], [6, 19], [21], [1]], ![[1, 17], [63, 48], [7, 54], [53, 60], [21], [1]]]
 h' := ![![[69, 78], [59, 46], [11, 49], [27, 5], [16, 16], [44, 69], [0, 1]], ![[0, 1], [73, 33], [74, 30], [56, 74], [14, 63], [65, 10], [69, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [20, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [35, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44, -47, 76]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40, -41, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![32, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![32, 1, 0]] 
 ![![79, 0, 0], ![32, 1, 0], ![1, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![32, 1, 0], ![0, 32, 3], ![189, 37, 32]]]
  hmulB := by decide  
  f := ![![![833, 26, 0], ![-2054, 0, 0]], ![![288, 9, 0], ![-710, 0, 0]], ![![-17, -22, -2], ![42, 53, 0]]]
  g := ![![![1, 0, 0], ![-32, 79, 0], ![-1, 0, 79]], ![![0, 1, 0], ![-13, 32, 3], ![-13, 37, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-38, -37, 1]] ![![79, 0, 0], ![32, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2528, 79, 0]], ![![-3002, -2923, 79], ![-1027, -1185, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![32, 1, 0]]], ![![![-38, -37, 1]], ![![-13, -15, -1]]]]
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


lemma PB169I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB169I1 : PrimesBelowBoundCertificateInterval O 31 79 169 where
  m := 11
  g := ![1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB169I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
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
  β := ![I41N1, I47N1, I59N1, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[], [I41N1], [], [I47N1], [], [I59N1], [], [], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
