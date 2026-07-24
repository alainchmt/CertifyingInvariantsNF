
import IdealArithmetic.Examples.NF3_1_536787_1.RI3_1_536787_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [5, 21, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 24, 35], [28, 12, 2], [0, 1]]
 g := ![![[13, 2, 10], [30, 27], [14, 25, 34], [0, 1], []], ![[19, 26, 28, 5], [15, 7], [31, 18, 25, 14], [34, 33], [15, 4]], ![[20, 4, 31, 6], [15, 30], [30, 24, 4, 32], [6, 21], [11, 4]]]
 h' := ![![[9, 24, 35], [14, 27, 11], [4, 25, 8], [0, 32, 16], [0, 0, 1], [0, 1]], ![[28, 12, 2], [27, 13, 4], [18, 7, 9], [14, 26, 17], [6, 23, 12], [9, 24, 35]], ![[0, 1], [20, 34, 22], [24, 5, 20], [17, 16, 4], [26, 14, 24], [28, 12, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 6], []]
 b := ![[], [18, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [5, 21, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20017, -444, -444]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-541, -12, -12]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![16, -4, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![16, -4, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![16, 37, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![16, -4, 1], ![141, 16, -4], ![-564, 141, 16]]]
  hmulB := by decide  
  f := ![![![-15, 4, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -37, 41]], ![![0, -1, 1], ![5, 4, -4], ![-20, -11, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 40], [0, 1]]
 g := ![![[30, 9], [37], [10], [29, 2], [1]], ![[0, 32], [37], [10], [36, 39], [1]]]
 h' := ![![[24, 40], [10, 3], [28, 23], [15, 16], [9, 24], [0, 1]], ![[0, 1], [0, 38], [6, 18], [30, 25], [11, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [33, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [32, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1676, 1239, 49]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, -14, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![4, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![4, 1, 0]] 
 ![![41, 0, 0], ![4, 1, 0], ![25, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![4, 1, 0], ![0, 4, 1], ![141, 0, 4]]]
  hmulB := by decide  
  f := ![![![101, 25, 0], ![-1025, 0, 0]], ![![4, 1, 0], ![-40, 0, 0]], ![![61, 15, 0], ![-619, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 41, 0], ![-25, 0, 41]], ![![0, 1, 0], ![-1, 4, 1], ![1, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![16, -4, 1]] ![![41, 0, 0], ![4, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![164, 41, 0]], ![![656, -164, 41], ![205, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![4, 1, 0]]], ![![![16, -4, 1]], ![![5, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [1, 26, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6, 42], [17, 36, 1], [0, 1]]
 g := ![![[37, 38, 25], [19, 4, 16], [27, 25], [30, 23, 1], []], ![[21, 3, 6, 30], [26, 6, 38, 27], [35, 36], [2, 2, 27, 37], [11, 1]], ![[24, 3, 42, 10], [39, 16], [42, 1], [41, 30, 17, 36], [9, 1]]]
 h' := ![![[6, 6, 42], [24, 15, 38], [13, 24, 39], [13, 14, 5], [0, 0, 1], [0, 1]], ![[17, 36, 1], [32, 4, 20], [14, 15, 4], [7, 41, 37], [25, 0, 36], [6, 6, 42]], ![[0, 1], [40, 24, 28], [32, 4], [17, 31, 1], [22, 0, 6], [17, 36, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 13], []]
 b := ![[], [4, 1, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [1, 26, 20, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-153123, -14921, -9503]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3561, -347, -221]
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


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7802, 1499, 288]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![7802, 1499, 288]] 
 ![![47, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7802, 1499, 288], ![40608, 7802, 1499], ![211359, 40608, 7802]]]
  hmulB := by decide  
  f := ![![![-188, -94, 25]], ![![75, -4, -2]], ![![-282, 75, -4]]]
  g := ![![![166, 1499, 288], ![864, 7802, 1499], ![4497, 40608, 7802]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![7802, 1499, 288]] ![![7802, 1499, 288]]
  ![![182613988, 35085500, 6740953]] where
 M := ![![![182613988, 35085500, 6740953]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![182613988, 35085500, 6740953]] ![![7802, 1499, 288]]
  ![![47, 0, 0]] where
 M := ![![![4274267403503, 821212058436, 157778908350]]]
 hmul := by decide  
 g := ![![![![90941859649, 17472596988, 3356998050]]]]
 hle2 := by decide  

def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N0, I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N0
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![11, 8, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![11, 8, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![11, 8, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![11, 8, 1], ![141, 11, 8], ![1128, 141, 11]]]
  hmulB := by decide  
  f := ![![![-10, -8, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -8, 53]], ![![0, 0, 1], ![1, -1, 8], ![19, 1, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [12, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 52], [0, 1]]
 g := ![![[11, 4], [15], [32, 9], [42], [27, 1]], ![[13, 49], [15], [10, 44], [42], [1, 52]]]
 h' := ![![[27, 52], [42, 2], [40, 42], [9, 3], [47, 28], [0, 1]], ![[0, 1], [43, 51], [8, 11], [37, 50], [8, 25], [27, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [43, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [12, 26, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-807, 1297, -83]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 37, -83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-8, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-8, 1, 0]] 
 ![![53, 0, 0], ![45, 1, 0], ![42, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-8, 1, 0], ![0, -8, 1], ![141, 0, -8]]]
  hmulB := by decide  
  f := ![![![193, -24, 0], ![1272, 0, 0]], ![![169, -21, 0], ![1114, 0, 0]], ![![162, -20, 0], ![1068, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 53, 0], ![-42, 0, 53]], ![![-1, 1, 0], ![6, -8, 1], ![9, 0, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![11, 8, 1]] ![![53, 0, 0], ![-8, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-424, 53, 0]], ![![583, 424, 53], ![53, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-8, 1, 0]]], ![![![11, 8, 1]], ![![1, -1, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![21, -27, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![21, -27, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![21, 32, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![21, -27, 1], ![141, 21, -27], ![-3807, 141, 21]]]
  hmulB := by decide  
  f := ![![![-20, 27, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -32, 59]], ![![0, -1, 1], ![12, 15, -27], ![-72, -9, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [26, 6, 1] where
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
 g := ![![[32, 25], [17, 28], [5], [42, 41], [53, 1]], ![[0, 34], [26, 31], [5], [32, 18], [47, 58]]]
 h' := ![![[53, 58], [30, 5], [3, 21], [29, 8], [38, 10], [0, 1]], ![[0, 1], [0, 54], [54, 38], [40, 51], [37, 49], [53, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [40, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [26, 6, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![308, 135, -5]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 5, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, 1, 0]] 
 ![![59, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, 1, 0], ![0, 27, 1], ![141, 0, 27]]]
  hmulB := by decide  
  f := ![![![514, 19, 0], ![-1121, 0, 0]], ![![216, 8, 0], ![-471, 0, 0]], ![![310, 11, 0], ![-676, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 59, 0], ![-38, 0, 59]], ![![0, 1, 0], ![-13, 27, 1], ![-15, 0, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![21, -27, 1]] ![![59, 0, 0], ![27, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1593, 59, 0]], ![![1239, -1593, 59], ![708, -708, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![27, 1, 0]]], ![![![21, -27, 1]], ![![12, -12, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [25, 18, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 30, 35], [22, 30, 26], [0, 1]]
 g := ![![[52, 25, 14], [50, 27], [52, 13, 27], [13, 41, 9], [1]], ![[38, 23, 21, 54], [32, 47], [17, 16, 27, 53], [1, 8, 3, 29], [22, 50, 60, 53]], ![[19, 42, 51, 31], [15, 60], [56, 43, 27, 43], [1, 20, 47, 23], [54, 11, 47, 8]]]
 h' := ![![[42, 30, 35], [26, 33, 21], [42, 54, 24], [41, 37, 37], [36, 43, 3], [0, 1]], ![[22, 30, 26], [34, 41, 16], [38, 30, 48], [24, 16, 26], [33, 39, 9], [42, 30, 35]], ![[0, 1], [38, 48, 24], [48, 38, 50], [24, 8, 59], [26, 40, 49], [22, 30, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 48], []]
 b := ![[], [15, 40, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [25, 18, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1313940, 163907, 30195]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21540, 2687, 495]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [58, 66, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 45, 19], [45, 21, 48], [0, 1]]
 g := ![![[17, 21, 33], [42, 8, 1], [31, 4], [21, 33], [64, 1], []], ![[36, 22, 10, 21], [29, 11, 58, 16], [48, 25], [56, 54], [62, 39], [24, 26]], ![[21, 15, 33, 48], [38, 28, 35, 20], [56, 9], [17, 1], [50, 15], [62, 26]]]
 h' := ![![[19, 45, 19], [43, 61, 57], [9, 39, 1], [47, 61, 2], [40, 6, 10], [0, 0, 1], [0, 1]], ![[45, 21, 48], [55, 16, 11], [54, 38, 25], [15, 48, 62], [28, 51, 56], [41, 25, 21], [19, 45, 19]], ![[0, 1], [6, 57, 66], [59, 57, 41], [52, 25, 3], [10, 10, 1], [37, 42, 45], [45, 21, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 12], []]
 b := ![[], [46, 3, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [58, 66, 3, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16080, -3618, 1206]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-240, -54, 18]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![1, -1, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![1, -1, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![1, 70, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![1, -1, 1], ![141, 1, -1], ![-141, 141, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 1], ![-70, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -70, 71]], ![![0, -1, 1], ![2, 1, -1], ![-2, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [7, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 70], [0, 1]]
 g := ![![[61, 3], [52, 19], [], [27], [1], [1]], ![[58, 68], [33, 52], [], [27], [1], [1]]]
 h' := ![![[70, 70], [62, 28], [0, 27], [13], [42, 13], [64, 70], [0, 1]], ![[0, 1], [34, 43], [44, 44], [13], [29, 58], [65, 1], [70, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [50, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [7, 1, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![571, 565, 3]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 5, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![1, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![1, 1, 0]] 
 ![![71, 0, 0], ![1, 1, 0], ![70, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![1, 1, 0], ![0, 1, 1], ![141, 0, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![71, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![70, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 71, 0], ![-70, 0, 71]], ![![0, 1, 0], ![-1, 1, 1], ![1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![1, -1, 1]] ![![71, 0, 0], ![1, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![71, 71, 0]], ![![71, -71, 71], ![142, 0, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![1, 1, 0]]], ![![![1, -1, 1]], ![![2, 0, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [64, 4, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 1, 62], [25, 71, 11], [0, 1]]
 g := ![![[6, 43, 3], [15, 70], [21, 54], [29, 1, 2], [6, 1], []], ![[55, 13, 28, 44], [8, 8], [57, 9], [7, 36, 62, 63], [3, 4], [47, 48]], ![[65, 33, 32, 44], [68, 19], [0, 41], [53, 56, 37, 34], [32, 1], [25, 48]]]
 h' := ![![[54, 1, 62], [21, 51, 21], [55, 57, 56], [42, 35, 28], [54, 58, 32], [0, 0, 1], [0, 1]], ![[25, 71, 11], [40, 70, 54], [25, 59, 64], [13, 36, 70], [23, 7, 28], [54, 60, 71], [54, 1, 62]], ![[0, 1], [20, 25, 71], [24, 30, 26], [43, 2, 48], [15, 8, 13], [47, 13, 1], [25, 71, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 34], []]
 b := ![[], [5, 38, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [64, 4, 67, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-393324, 122932, -9052]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5388, 1684, -124]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-32, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-32, 1, 0]] 
 ![![79, 0, 0], ![47, 1, 0], ![3, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-32, 1, 0], ![0, -32, 1], ![141, 0, -32]]]
  hmulB := by decide  
  f := ![![![1793, -56, 0], ![4424, 0, 0]], ![![1121, -35, 0], ![2766, 0, 0]], ![![77, -2, 0], ![190, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 79, 0], ![-3, 0, 79]], ![![-1, 1, 0], ![19, -32, 1], ![3, 0, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 52, 10]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![271, 52, 10]] 
 ![![79, 0, 0], ![54, 1, 0], ![7, 0, 1]] where
  M :=![![![271, 52, 10], ![1410, 271, 52], ![7332, 1410, 271]]]
  hmulB := by decide  
  f := ![![![121, 8, -6]], ![![72, 7, -4]], ![![25, -10, 1]]]
  g := ![![![-33, 52, 10], ![-172, 271, 52], ![-895, 1410, 271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-22, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-22, 1, 0]] 
 ![![79, 0, 0], ![57, 1, 0], ![69, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-22, 1, 0], ![0, -22, 1], ![141, 0, -22]]]
  hmulB := by decide  
  f := ![![![573, -26, 0], ![2054, 0, 0]], ![![419, -19, 0], ![1502, 0, 0]], ![![491, -22, 0], ![1760, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 79, 0], ![-69, 0, 79]], ![![-1, 1, 0], ![15, -22, 1], ![21, 0, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-32, 1, 0]] ![![271, 52, 10]]
  ![![79, 0, 0], ![10, 22, 1]] where
 M := ![![![21409, 4108, 790]], ![![-7262, -1393, -268]]]
 hmul := by decide  
 g := ![![![![261, 30, 9], ![79, 0, 0]]], ![![![-98, -31, -4], ![48, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![10, 22, 1]] ![![79, 0, 0], ![-22, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1738, 79, 0]], ![![790, 1738, 79], ![-79, -474, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-22, 1, 0]]], ![![![10, 22, 1]], ![![-1, -6, 0]]]]
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


lemma PB208I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB208I1 : PrimesBelowBoundCertificateInterval O 31 79 208 where
  m := 11
  g := ![1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB208I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N0, I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N0
      exact NI47N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
      exact NI79N2
  β := ![I41N1, I47N0, I53N1, I59N1, I71N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [], [I47N0, I47N0, I47N0], [I53N1], [I59N1], [], [], [I71N1], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
