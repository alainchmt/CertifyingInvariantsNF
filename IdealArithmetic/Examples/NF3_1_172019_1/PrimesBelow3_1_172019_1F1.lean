
import IdealArithmetic.Examples.NF3_1_172019_1.RI3_1_172019_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-28, -21, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-28, -21, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![9, 16, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-28, -21, 1], ![116, 13, -20], ![-2320, -704, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -16, 37]], ![![-1, -1, 1], ![8, 9, -20], ![-61, -16, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [20, 0, 1] where
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
 h' := ![![[0, 36], [6], [0, 12], [30], [17], [0, 1]], ![[0, 1], [6], [0, 25], [30], [17], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [0, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [20, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![368, 239, 45]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -13, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![7, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![0, -17, 1], ![116, 41, -16]]]
  hmulB := by decide  
  f := ![![![545, -32, 0], ![1184, 0, 0]], ![![290, -17, 0], ![630, 0, 0]], ![![127, -7, 0], ![276, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-7, 0, 37]], ![![-1, 1, 0], ![9, -17, 1], ![-16, 41, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-28, -21, 1]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![-1036, -777, 37], ![592, 370, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-17, 1, 0]]], ![![![-28, -21, 1]], ![![16, 10, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-36, 14, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-36, 14, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 14, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-36, 14, 1], ![116, 5, 15], ![1740, 731, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -14, 41]], ![![-1, 0, 1], ![1, -5, 15], ![40, 11, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [39, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 40], [0, 1]]
 g := ![![[5, 20], [9], [20], [15, 18], [1]], ![[0, 21], [9], [20], [31, 23], [1]]]
 h' := ![![[10, 40], [27, 26], [38, 38], [30, 26], [2, 10], [0, 1]], ![[0, 1], [0, 15], [8, 3], [3, 15], [20, 31], [10, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [39, 31, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-339, 863, 457]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -135, 457]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-15, 1, 0]] 
 ![![41, 0, 0], ![26, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-15, 1, 0], ![0, -15, 1], ![116, 41, -14]]]
  hmulB := by decide  
  f := ![![![256, -17, 0], ![697, 0, 0]], ![![166, -11, 0], ![452, 0, 0]], ![![126, -8, 0], ![343, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 41, 0], ![-21, 0, 41]], ![![-1, 1, 0], ![9, -15, 1], ![-16, 41, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-36, 14, 1]] ![![41, 0, 0], ![-15, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-615, 41, 0]], ![![-1476, 574, 41], ![656, -205, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-15, 1, 0]]], ![![![-36, 14, 1]], ![![16, -5, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [21, 28, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 36], [41, 6], [0, 1]]
 g := ![![[15, 33, 6], [34, 35, 41], [36, 16], [13, 27, 1], []], ![[41, 42, 36], [12, 8, 31], [27, 17], [3, 7, 6], []], ![[16, 11, 1], [42, 0, 14], [4, 10], [6, 9, 36], []]]
 h' := ![![[29, 36], [17, 0, 7], [28, 12, 27], [28, 15, 4], [0, 0, 1], [0, 1]], ![[41, 6], [13, 39, 42], [35, 5, 33], [0, 34, 24], [24, 24, 6], [29, 36]], ![[0, 1], [2, 4, 37], [26, 26, 26], [14, 37, 15], [4, 19, 36], [41, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34], []]
 b := ![[], [11, 31, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [21, 28, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-186663, -10879, -19049]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4341, -253, -443]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [25, 44, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 31, 36], [34, 15, 11], [0, 1]]
 g := ![![[45, 15, 18], [4, 3, 36], [18, 21, 16], [9, 37, 1], []], ![[29, 43, 27, 1], [2, 16, 4, 12], [39, 35, 6, 7], [45, 39, 8, 16], [35, 27]], ![[28, 37, 42, 26], [45, 28, 12, 19], [34, 45, 24, 45], [28, 8, 30, 43], [13, 27]]]
 h' := ![![[3, 31, 36], [41, 8, 21], [20, 5, 41], [10, 42, 43], [0, 0, 1], [0, 1]], ![[34, 15, 11], [21, 33, 39], [14, 15, 43], [28, 18, 42], [27, 39, 15], [3, 31, 36]], ![[0, 1], [45, 6, 34], [45, 27, 10], [41, 34, 9], [32, 8, 31], [34, 15, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 37], []]
 b := ![[], [6, 12, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [25, 44, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-488048, -288345, -45355]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10384, -6135, -965]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-3, -22, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-3, -22, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![50, 31, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-3, -22, 1], ![116, 38, -21], ![-2436, -745, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -31, 53]], ![![-1, -1, 1], ![22, 13, -21], ![-62, -24, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [46, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 52], [0, 1]]
 g := ![![[48, 15], [44], [10, 15], [10], [18, 1]], ![[0, 38], [44], [15, 38], [10], [36, 52]]]
 h' := ![![[18, 52], [14, 11], [17, 16], [46, 11], [20, 13], [0, 1]], ![[0, 1], [0, 42], [40, 37], [32, 42], [42, 40], [18, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [46, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![394, 204, 10]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -2, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![36, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![0, 21, 1], ![116, 41, 22]]]
  hmulB := by decide  
  f := ![![![379, 18, 0], ![-954, 0, 0]], ![![147, 7, 0], ![-370, 0, 0]], ![![240, 11, 0], ![-604, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-36, 0, 53]], ![![0, 1, 0], ![-9, 21, 1], ![-29, 41, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-3, -22, 1]] ![![53, 0, 0], ![21, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1113, 53, 0]], ![![-159, -1166, 53], ![53, -424, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![21, 1, 0]]], ![![![-3, -22, 1]], ![![1, -8, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![44, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![0, -29, 1], ![116, 41, -28]]]
  hmulB := by decide  
  f := ![![![1712, -59, 0], ![3481, 0, 0]], ![![900, -31, 0], ![1830, 0, 0]], ![![1320, -45, 0], ![2684, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-44, 0, 59]], ![![-1, 1, 0], ![14, -29, 1], ![2, 41, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-16, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-16, 1, 0]] 
 ![![59, 0, 0], ![43, 1, 0], ![39, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-16, 1, 0], ![0, -16, 1], ![116, 41, -15]]]
  hmulB := by decide  
  f := ![![![865, -54, 0], ![3186, 0, 0]], ![![625, -39, 0], ![2302, 0, 0]], ![![581, -36, 0], ![2140, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 59, 0], ![-39, 0, 59]], ![![-1, 1, 0], ![11, -16, 1], ![-18, 41, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![11, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![0, -15, 1], ![116, 41, -14]]]
  hmulB := by decide  
  f := ![![![91, -6, 0], ![354, 0, 0]], ![![76, -5, 0], ![296, 0, 0]], ![![19, -1, 0], ![74, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-11, 0, 59]], ![![-1, 1, 0], ![11, -15, 1], ![-26, 41, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-29, 1, 0]] ![![59, 0, 0], ![-16, 1, 0]]
  ![![59, 0, 0], ![-8, 14, 1]] where
 M := ![![![3481, 0, 0], ![-944, 59, 0]], ![![-1711, 59, 0], ![464, -45, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![-8, -13, -1], ![59, 0, 0]]], ![![![-21, -13, -1], ![59, 0, 0]], ![![8, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-8, 14, 1]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![-472, 826, 59], ![236, -177, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-15, 1, 0]]], ![![![-8, 14, 1]], ![![4, -3, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![61, 0, 0], ![5, 1, 0], ![36, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 1], ![116, 41, 6]]]
  hmulB := by decide  
  f := ![![![-11, -6, 1]], ![![1, 0, 0]], ![![-16, -5, 1]]]
  g := ![![![0, 1, 0], ![-1, 5, 1], ![-5, 41, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, 59, -10]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![165, 59, -10]] 
 ![![61, 0, 0], ![6, 1, 0], ![25, 0, 1]] where
  M :=![![![165, 59, -10], ![-1160, -245, 49], ![5684, 849, -196]]]
  hmulB := by decide  
  f := ![![![-6419, -3074, -441]], ![![-1470, -704, -101]], ![![-9315, -4461, -640]]]
  g := ![![![1, 59, -10], ![-15, -245, 49], ![90, 849, -196]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-495, -237, -34]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-495, -237, -34]] 
 ![![61, 0, 0], ![49, 1, 0], ![39, 0, 1]] where
  M :=![![![-495, -237, -34], ![-3944, -1889, -271], ![-31436, -15055, -2160]]]
  hmulB := by decide  
  f := ![![![-335, 50, -1]], ![![-271, 34, 0]], ![![-121, 63, -6]]]
  g := ![![![204, -237, -34], ![1626, -1889, -271], ![12959, -15055, -2160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![5, 1, 0]] ![![165, 59, -10]]
  ![![-335, 50, -1]] where
 M := ![![![-335, 50, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-335, 50, -1]] ![![-495, -237, -34]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [43, 33, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 28, 60], [1, 38, 7], [0, 1]]
 g := ![![[49, 27, 14], [24, 64, 64], [46, 29], [14, 16], [38, 1], []], ![[45, 43, 28, 62], [8, 10], [10, 21], [52, 24], [1, 37], [63, 49]], ![[2, 16, 36, 2], [63, 37, 60, 46], [18, 65], [51, 54], [39, 47], [49, 49]]]
 h' := ![![[37, 28, 60], [40, 2, 58], [14, 14, 59], [7, 31, 37], [41, 43, 4], [0, 0, 1], [0, 1]], ![[1, 38, 7], [47, 54, 46], [63, 18], [15, 35, 50], [24, 51, 52], [0, 30, 38], [37, 28, 60]], ![[0, 1], [35, 11, 30], [59, 35, 8], [37, 1, 47], [35, 40, 11], [38, 37, 28], [1, 38, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 45], []]
 b := ![[], [19, 25, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [43, 33, 29, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1366934, 625713, 79931]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20402, 9339, 1193]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-32, 22, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-32, 22, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![39, 22, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-32, 22, 1], ![116, 9, 23], ![2668, 1059, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -22, 71]], ![![-1, 0, 1], ![-11, -7, 23], ![20, 5, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 70], [0, 1]]
 g := ![![[45, 32], [41, 30], [66, 19], [60], [32], [1]], ![[0, 39], [21, 41], [6, 52], [60], [32], [1]]]
 h' := ![![[23, 70], [32, 48], [29, 39], [26, 27], [44, 29], [51, 23], [0, 1]], ![[0, 1], [0, 23], [3, 32], [8, 44], [1, 42], [12, 48], [23, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [1, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [20, 48, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-607, 49, -1]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, 1, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-23, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-23, 1, 0]] 
 ![![71, 0, 0], ![48, 1, 0], ![39, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-23, 1, 0], ![0, -23, 1], ![116, 41, -22]]]
  hmulB := by decide  
  f := ![![![1059, -46, 0], ![3266, 0, 0]], ![![714, -31, 0], ![2202, 0, 0]], ![![583, -25, 0], ![1798, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 71, 0], ![-39, 0, 71]], ![![-1, 1, 0], ![15, -23, 1], ![-14, 41, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-32, 22, 1]] ![![71, 0, 0], ![-23, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1633, 71, 0]], ![![-2272, 1562, 71], ![852, -497, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-23, 1, 0]]], ![![![-32, 22, 1]], ![![12, -7, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-50, -15, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-50, -15, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![23, 58, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-50, -15, 1], ![116, -9, -14], ![-1624, -458, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -58, 73]], ![![-1, -1, 1], ![6, 11, -14], ![-15, 12, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [55, 65, 1] where
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
 g := ![![[41, 4], [57], [49], [49, 9], [64], [1]], ![[0, 69], [57], [49], [48, 64], [64], [1]]]
 h' := ![![[8, 72], [16, 71], [42, 38], [6, 7], [16, 70], [18, 8], [0, 1]], ![[0, 1], [0, 2], [54, 35], [62, 66], [65, 3], [9, 65], [8, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [43, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [55, 65, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![983, 857, 303]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82, -229, 303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![14, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![14, 1, 0]] 
 ![![73, 0, 0], ![14, 1, 0], ![23, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![14, 1, 0], ![0, 14, 1], ![116, 41, 15]]]
  hmulB := by decide  
  f := ![![![491, 35, 0], ![-2555, 0, 0]], ![![70, 5, 0], ![-364, 0, 0]], ![![157, 11, 0], ![-817, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 73, 0], ![-23, 0, 73]], ![![0, 1, 0], ![-3, 14, 1], ![-11, 41, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-50, -15, 1]] ![![73, 0, 0], ![14, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1022, 73, 0]], ![![-3650, -1095, 73], ![-584, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![14, 1, 0]]], ![![![-50, -15, 1]], ![![-8, -3, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-56, -20, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-56, -20, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![23, 59, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-56, -20, 1], ![116, -15, -19], ![-2204, -663, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -59, 79]], ![![-1, -1, 1], ![7, 14, -19], ![-18, 17, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [28, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 78], [0, 1]]
 g := ![![[72, 62], [38, 23], [33, 73], [2, 73], [22], [1]], ![[58, 17], [43, 56], [42, 6], [11, 6], [22], [1]]]
 h' := ![![[38, 78], [42, 33], [24, 55], [23, 28], [10, 51], [51, 38], [0, 1]], ![[0, 1], [32, 46], [60, 24], [60, 51], [52, 28], [73, 41], [38, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [54, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [28, 41, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4062, -1462, 318]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144, -256, 318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![19, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![19, 1, 0]] 
 ![![79, 0, 0], ![19, 1, 0], ![34, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![19, 1, 0], ![0, 19, 1], ![116, 41, 20]]]
  hmulB := by decide  
  f := ![![![400, 21, 0], ![-1659, 0, 0]], ![![76, 4, 0], ![-315, 0, 0]], ![![138, 7, 0], ![-572, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 79, 0], ![-34, 0, 79]], ![![0, 1, 0], ![-5, 19, 1], ![-17, 41, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-56, -20, 1]] ![![79, 0, 0], ![19, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1501, 79, 0]], ![![-4424, -1580, 79], ![-948, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![19, 1, 0]]], ![![![-56, -20, 1]], ![![-12, -5, 0]]]]
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


lemma PB118I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB118I1 : PrimesBelowBoundCertificateInterval O 31 79 118 where
  m := 11
  g := ![2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB118I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
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
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
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
      exact NI61N1
      exact NI61N2
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I53N1, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [], [], [I53N1], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
