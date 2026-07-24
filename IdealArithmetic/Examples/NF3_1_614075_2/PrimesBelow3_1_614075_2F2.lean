
import IdealArithmetic.Examples.NF3_1_614075_2.RI3_1_614075_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![32, 37, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![32, 37, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![32, 37, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![32, 37, 1], ![-112, -5, 38], ![-4256, -1518, 33]]]
  hmulB := by decide  
  f := ![![![-31, -37, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -37, 83]], ![![0, 0, 1], ![-16, -17, 38], ![-64, -33, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [38, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 82], [0, 1]]
 g := ![![[29, 59], [20, 1], [29], [10], [39, 31], [1]], ![[0, 24], [80, 82], [29], [10], [73, 52], [1]]]
 h' := ![![[60, 82], [70, 68], [63, 1], [13, 64], [12, 33], [45, 60], [0, 1]], ![[0, 1], [0, 15], [40, 82], [35, 19], [0, 50], [76, 23], [60, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [29, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [38, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-298, -246, -56]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 22, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-38, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-38, 1, 0]] 
 ![![83, 0, 0], ![45, 1, 0], ![50, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-38, 1, 0], ![0, -38, 1], ![-112, -37, -37]]]
  hmulB := by decide  
  f := ![![![2775, -73, 0], ![6059, 0, 0]], ![![1521, -40, 0], ![3321, 0, 0]], ![![1690, -44, 0], ![3690, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 83, 0], ![-50, 0, 83]], ![![-1, 1, 0], ![20, -38, 1], ![41, -37, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![32, 37, 1]] ![![83, 0, 0], ![-38, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3154, 83, 0]], ![![2656, 3071, 83], ![-1328, -1411, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-38, 1, 0]]], ![![![32, 37, 1]], ![![-16, -17, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [48, 54, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 68, 27], [59, 20, 62], [0, 1]]
 g := ![![[30, 46, 55], [71, 49], [52, 73], [66, 34, 88], [15, 43, 1], []], ![[5, 35, 10, 43], [81, 47], [79, 79], [65, 68, 62, 13], [80, 82, 34, 31], [42, 17]], ![[78, 3, 20, 33], [19, 39], [45, 1], [22, 13, 14, 52], [36, 55, 85, 19], [7, 17]]]
 h' := ![![[73, 68, 27], [43, 48, 12], [46, 31, 82], [36, 30, 42], [81, 63, 55], [0, 0, 1], [0, 1]], ![[59, 20, 62], [49, 41, 23], [33, 35, 74], [40, 60, 48], [84, 51, 42], [20, 80, 20], [73, 68, 27]], ![[0, 1], [31, 0, 54], [63, 23, 22], [40, 88, 88], [19, 64, 81], [30, 9, 68], [59, 20, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 78], []]
 b := ![[], [53, 31, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [48, 54, 46, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![353063, 184230, 22250]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3967, 2070, 250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![10, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![10, 1, 0]] 
 ![![97, 0, 0], ![10, 1, 0], ![94, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![10, 1, 0], ![0, 10, 1], ![-112, -37, 11]]]
  hmulB := by decide  
  f := ![![![581, 58, 0], ![-5626, 0, 0]], ![![50, 5, 0], ![-484, 0, 0]], ![![562, 56, 0], ![-5442, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 97, 0], ![-94, 0, 97]], ![![0, 1, 0], ![-2, 10, 1], ![-8, -37, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![22, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![22, 1, 0]] 
 ![![97, 0, 0], ![22, 1, 0], ![1, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![22, 1, 0], ![0, 22, 1], ![-112, -37, 23]]]
  hmulB := by decide  
  f := ![![![1079, 49, 0], ![-4753, 0, 0]], ![![242, 11, 0], ![-1066, 0, 0]], ![![-17, -1, 0], ![75, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 97, 0], ![-1, 0, 97]], ![![0, 1, 0], ![-5, 22, 1], ![7, -37, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-33, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-33, 1, 0]] 
 ![![97, 0, 0], ![64, 1, 0], ![75, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-33, 1, 0], ![0, -33, 1], ![-112, -37, -32]]]
  hmulB := by decide  
  f := ![![![2179, -66, 0], ![6402, 0, 0]], ![![1420, -43, 0], ![4172, 0, 0]], ![![1695, -51, 0], ![4980, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 97, 0], ![-75, 0, 97]], ![![-1, 1, 0], ![21, -33, 1], ![48, -37, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![10, 1, 0]] ![![97, 0, 0], ![22, 1, 0]]
  ![![97, 0, 0], ![26, 32, 1]] where
 M := ![![![9409, 0, 0], ![2134, 97, 0]], ![![970, 97, 0], ![220, 32, 1]]]
 hmul := by decide  
 g := ![![![![71, -32, -1], ![97, 0, 0]], ![![-4, -31, -1], ![97, 0, 0]]], ![![![-16, -31, -1], ![97, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![26, 32, 1]] ![![97, 0, 0], ![-33, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3201, 97, 0]], ![![2522, 3104, 97], ![-970, -1067, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-33, 1, 0]]], ![![![26, 32, 1]], ![![-10, -11, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [20, 33, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 56, 19], [40, 44, 82], [0, 1]]
 g := ![![[18, 37, 17], [42, 37], [10, 87, 6], [94, 21], [47, 87], [1]], ![[1, 8, 68, 31], [55, 47], [56, 61, 44, 97], [46, 36], [51, 6], [58, 74, 100, 92]], ![[72, 73, 59, 87], [57, 30], [8, 73, 51, 5], [40, 71], [79, 80], [20, 50, 29, 9]]]
 h' := ![![[44, 56, 19], [73, 6, 44], [2, 28, 21], [52, 17, 62], [66, 49, 18], [81, 68, 84], [0, 1]], ![[40, 44, 82], [65, 17, 30], [85, 27, 42], [77, 48, 21], [54, 38, 6], [93, 68, 39], [44, 56, 19]], ![[0, 1], [95, 78, 27], [86, 46, 38], [30, 36, 18], [27, 14, 77], [71, 66, 79], [40, 44, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 21], []]
 b := ![[], [27, 78, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [20, 33, 17, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-222604, 16463, -5151]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2204, 163, -51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![70, 18, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![70, 18, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![70, 18, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![70, 18, 1], ![-112, 33, 19], ![-2128, -815, 52]]]
  hmulB := by decide  
  f := ![![![-69, -18, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -18, 103]], ![![0, 0, 1], ![-14, -3, 19], ![-56, -17, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [1, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 102], [0, 1]]
 g := ![![[53, 1], [53, 1], [50, 16], [23], [8], [50, 1]], ![[0, 102], [0, 102], [26, 87], [23], [8], [100, 102]]]
 h' := ![![[50, 102], [50, 102], [53, 1], [68, 99], [20, 69], [53, 27], [0, 1]], ![[0, 1], [0, 1], [0, 102], [74, 4], [71, 34], [64, 76], [50, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [45, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [1, 53, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-281, -1064, -494]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![333, 76, -494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-19, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-19, 1, 0]] 
 ![![103, 0, 0], ![84, 1, 0], ![51, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-19, 1, 0], ![0, -19, 1], ![-112, -37, -18]]]
  hmulB := by decide  
  f := ![![![913, -48, 0], ![4944, 0, 0]], ![![742, -39, 0], ![4018, 0, 0]], ![![441, -23, 0], ![2388, 1, 0]]]
  g := ![![![1, 0, 0], ![-84, 103, 0], ![-51, 0, 103]], ![![-1, 1, 0], ![15, -19, 1], ![38, -37, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![70, 18, 1]] ![![103, 0, 0], ![-19, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1957, 103, 0]], ![![7210, 1854, 103], ![-1442, -309, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-19, 1, 0]]], ![![![70, 18, 1]], ![![-14, -3, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![19, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![19, 1, 0]] 
 ![![107, 0, 0], ![19, 1, 0], ![67, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![19, 1, 0], ![0, 19, 1], ![-112, -37, 20]]]
  hmulB := by decide  
  f := ![![![913, 48, 0], ![-5136, 0, 0]], ![![133, 7, 0], ![-748, 0, 0]], ![![555, 29, 0], ![-3122, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 107, 0], ![-67, 0, 107]], ![![0, 1, 0], ![-4, 19, 1], ![-7, -37, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95, -14, 10]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-95, -14, 10]] 
 ![![107, 0, 0], ![95, 1, 0], ![70, 0, 1]] where
  M :=![![![-95, -14, 10], ![-1120, -465, -4], ![448, -972, -469]]]
  hmulB := by decide  
  f := ![![![-214197, 16286, -4706]], ![![-185249, 14085, -4070]], ![![-152250, 11576, -3345]]]
  g := ![![![5, -14, 10], ![405, -465, -4], ![1174, -972, -469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-8, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-8, 1, 0]] 
 ![![107, 0, 0], ![99, 1, 0], ![43, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-8, 1, 0], ![0, -8, 1], ![-112, -37, -7]]]
  hmulB := by decide  
  f := ![![![569, -71, 0], ![7597, 0, 0]], ![![529, -66, 0], ![7063, 0, 0]], ![![233, -29, 0], ![3111, 1, 0]]]
  g := ![![![1, 0, 0], ![-99, 107, 0], ![-43, 0, 107]], ![![-1, 1, 0], ![7, -8, 1], ![36, -37, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![19, 1, 0]] ![![-95, -14, 10]]
  ![![107, 0, 0], ![-14, 7, 1]] where
 M := ![![![-10165, -1498, 1070]], ![![-2925, -731, 186]]]
 hmul := by decide  
 g := ![![![![-81, -21, 9], ![107, 0, 0]]], ![![![-17, -12, 1], ![79, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-14, 7, 1]] ![![107, 0, 0], ![-8, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-856, 107, 0]], ![![-1498, 749, 107], ![0, -107, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-8, 1, 0]]], ![![![-14, 7, 1]], ![![0, -1, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [1, 41, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 78, 64], [55, 30, 45], [0, 1]]
 g := ![![[92, 65, 81], [98, 106], [76, 18, 22], [32, 40, 83], [14, 61], [1]], ![[65, 107, 21, 4], [99, 38], [100, 66, 70, 83], [55, 31, 28, 108], [107, 21], [84, 98, 64, 108]], ![[79, 78, 37, 5], [106, 4], [11, 25, 24, 43], [20, 67, 4, 15], [29, 83], [71, 60, 74, 1]]]
 h' := ![![[17, 78, 64], [10, 60, 100], [33, 70, 91], [77, 16, 26], [96, 101, 44], [108, 68, 72], [0, 1]], ![[55, 30, 45], [53, 3, 82], [32, 30, 16], [71, 8, 60], [1, 78, 45], [33, 101, 81], [17, 78, 64]], ![[0, 1], [7, 46, 36], [2, 9, 2], [35, 85, 23], [108, 39, 20], [79, 49, 65], [55, 30, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 81], []]
 b := ![[], [11, 67, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [1, 41, 37, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44799, -22345, -1635]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-411, -205, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![9, -26, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![9, -26, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![9, 87, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![9, -26, 1], ![-112, -28, -25], ![2800, 813, -53]]]
  hmulB := by decide  
  f := ![![![-8, 26, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -87, 113]], ![![0, -1, 1], ![1, 19, -25], ![29, 48, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [2, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 112], [0, 1]]
 g := ![![[101, 57], [15], [36], [88], [63, 81], [24, 1]], ![[0, 56], [15], [36], [88], [86, 32], [48, 112]]]
 h' := ![![[24, 112], [47, 31], [90, 44], [106, 107], [100, 38], [65, 9], [0, 1]], ![[0, 1], [0, 82], [16, 69], [75, 6], [108, 75], [55, 104], [24, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [8, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [2, 89, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4276, 174, 454]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74, -348, 454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![25, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![25, 1, 0]] 
 ![![113, 0, 0], ![25, 1, 0], ![53, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![25, 1, 0], ![0, 25, 1], ![-112, -37, 26]]]
  hmulB := by decide  
  f := ![![![1551, 62, 0], ![-7006, 0, 0]], ![![325, 13, 0], ![-1468, 0, 0]], ![![731, 29, 0], ![-3302, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 113, 0], ![-53, 0, 113]], ![![0, 1, 0], ![-6, 25, 1], ![-5, -37, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![9, -26, 1]] ![![113, 0, 0], ![25, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2825, 113, 0]], ![![1017, -2938, 113], ![113, -678, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![25, 1, 0]]], ![![![9, -26, 1]], ![![1, -6, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![69, -56, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![69, -56, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![69, 71, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![69, -56, 1], ![-112, 32, -55], ![6160, 1923, -23]]]
  hmulB := by decide  
  f := ![![![-68, 56, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -71, 127]], ![![0, -1, 1], ![29, 31, -55], ![61, 28, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [50, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 126], [0, 1]]
 g := ![![[16, 94], [51, 72], [100, 4], [47, 1], [69, 9], [89, 1]], ![[0, 33], [109, 55], [75, 123], [9, 126], [108, 118], [51, 126]]]
 h' := ![![[89, 126], [117, 100], [80, 96], [63, 2], [106, 1], [122, 124], [0, 1]], ![[0, 1], [0, 27], [115, 31], [114, 125], [68, 126], [109, 3], [89, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [21, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [50, 38, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![573, 181, -69]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, 40, -69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![55, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![55, 1, 0]] 
 ![![127, 0, 0], ![55, 1, 0], ![23, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![55, 1, 0], ![0, 55, 1], ![-112, -37, 56]]]
  hmulB := by decide  
  f := ![![![2256, 41, 0], ![-5207, 0, 0]], ![![990, 18, 0], ![-2285, 0, 0]], ![![354, 6, 0], ![-817, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 127, 0], ![-23, 0, 127]], ![![0, 1, 0], ![-24, 55, 1], ![5, -37, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![69, -56, 1]] ![![127, 0, 0], ![55, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![6985, 127, 0]], ![![8763, -7112, 127], ![3683, -3048, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![55, 1, 0]]], ![![![69, -56, 1]], ![![29, -24, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [7, 81, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 100, 127], [90, 30, 4], [0, 1]]
 g := ![![[71, 11, 49], [28], [117, 38], [102, 84], [45, 125], [117, 1], []], ![[56, 23, 125, 122], [46, 90, 61, 42], [17, 64], [80, 109], [99, 100], [55, 114], [24, 16]], ![[32, 27, 21, 27], [12, 118, 36, 89], [119, 48], [14, 121], [98, 21], [125, 44], [16, 16]]]
 h' := ![![[27, 100, 127], [66, 128, 124], [118, 91], [85, 101, 118], [119, 91, 79], [98, 79, 115], [0, 0, 1], [0, 1]], ![[90, 30, 4], [119, 3, 64], [86, 61, 29], [104, 33, 123], [128, 10, 41], [67, 115, 121], [37, 69, 30], [27, 100, 127]], ![[0, 1], [79, 0, 74], [55, 110, 102], [44, 128, 21], [81, 30, 11], [51, 68, 26], [128, 62, 100], [90, 30, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 66], []]
 b := ![[], [86, 105, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [7, 81, 14, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![200823, 90390, 4061]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1533, 690, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![41, 23, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![41, 23, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![41, 23, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![41, 23, 1], ![-112, 4, 24], ![-2688, -1000, 28]]]
  hmulB := by decide  
  f := ![![![-40, -23, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -23, 137]], ![![0, 0, 1], ![-8, -4, 24], ![-28, -12, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [15, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 136], [0, 1]]
 g := ![![[7, 64], [133], [30], [91, 65], [28], [65], [1]], ![[0, 73], [133], [30], [116, 72], [28], [65], [1]]]
 h' := ![![[32, 136], [119, 129], [123, 74], [5, 21], [106, 105], [72, 24], [122, 32], [0, 1]], ![[0, 1], [0, 8], [25, 63], [129, 116], [41, 32], [18, 113], [50, 105], [32, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [116, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [15, 105, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4261, -206, 134]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -24, 134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-24, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-24, 1, 0]] 
 ![![137, 0, 0], ![113, 1, 0], ![109, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-24, 1, 0], ![0, -24, 1], ![-112, -37, -23]]]
  hmulB := by decide  
  f := ![![![1201, -50, 0], ![6850, 0, 0]], ![![985, -41, 0], ![5618, 0, 0]], ![![965, -40, 0], ![5504, 1, 0]]]
  g := ![![![1, 0, 0], ![-113, 137, 0], ![-109, 0, 137]], ![![-1, 1, 0], ![19, -24, 1], ![48, -37, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![41, 23, 1]] ![![137, 0, 0], ![-24, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3288, 137, 0]], ![![5617, 3151, 137], ![-1096, -548, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-24, 1, 0]]], ![![![41, 23, 1]], ![![-8, -4, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB222I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB222I2 : PrimesBelowBoundCertificateInterval O 79 137 222 where
  m := 11
  g := ![2, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB222I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I97N0, I97N1, I97N2, I103N1, I107N0, I107N1, I107N2, I113N1, I127N1, I137N1]
  Il := ![[I83N1], [], [I97N0, I97N1, I97N2], [], [I103N1], [I107N0, I107N1, I107N2], [], [I113N1], [I127N1], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
