
import IdealArithmetic.Examples.NF3_1_181804_1.RI3_1_181804_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![17, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![17, 1, 0]] 
 ![![83, 0, 0], ![17, 1, 0], ![43, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![17, 1, 0], ![0, 17, 1], ![82, -4, 17]]]
  hmulB := by decide  
  f := ![![![579, 34, 0], ![-2822, 0, 0]], ![![119, 7, 0], ![-580, 0, 0]], ![![293, 17, 0], ![-1428, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 83, 0], ![-43, 0, 83]], ![![0, 1, 0], ![-4, 17, 1], ![-7, -4, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![26, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![26, 1, 0]] 
 ![![83, 0, 0], ![26, 1, 0], ![71, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![26, 1, 0], ![0, 26, 1], ![82, -4, 26]]]
  hmulB := by decide  
  f := ![![![365, 14, 0], ![-1162, 0, 0]], ![![78, 3, 0], ![-248, 0, 0]], ![![269, 10, 0], ![-856, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 83, 0], ![-71, 0, 83]], ![![0, 1, 0], ![-9, 26, 1], ![-20, -4, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![40, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![40, 1, 0]] 
 ![![83, 0, 0], ![40, 1, 0], ![60, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![40, 1, 0], ![0, 40, 1], ![82, -4, 40]]]
  hmulB := by decide  
  f := ![![![761, 19, 0], ![-1577, 0, 0]], ![![360, 9, 0], ![-746, 0, 0]], ![![580, 14, 0], ![-1202, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 83, 0], ![-60, 0, 83]], ![![0, 1, 0], ![-20, 40, 1], ![-26, -4, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![17, 1, 0]] ![![83, 0, 0], ![26, 1, 0]]
  ![![83, 0, 0], ![27, -40, 1]] where
 M := ![![![6889, 0, 0], ![2158, 83, 0]], ![![1411, 83, 0], ![442, 43, 1]]]
 hmul := by decide  
 g := ![![![![56, 40, -1], ![83, 0, 0]], ![![-1, 41, -1], ![83, 0, 0]]], ![![![-10, 41, -1], ![83, 0, 0]], ![![-22, 41, -1], ![84, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![27, -40, 1]] ![![83, 0, 0], ![40, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3320, 83, 0]], ![![2241, -3320, 83], ![1162, -1577, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![40, 1, 0]]], ![![![27, -40, 1]], ![![14, -19, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![9, 19, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![9, 19, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![9, 19, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![9, 19, 1], ![82, 5, 19], ![1558, 6, 5]]]
  hmulB := by decide  
  f := ![![![-8, -19, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -19, 89]], ![![0, 0, 1], ![-1, -4, 19], ![17, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [8, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 88], [0, 1]]
 g := ![![[85, 78], [5], [10], [58, 10], [38, 45], [1]], ![[0, 11], [5], [10], [22, 79], [54, 44], [1]]]
 h' := ![![[32, 88], [67, 73], [14, 70], [70, 30], [52, 30], [81, 32], [0, 1]], ![[0, 1], [0, 16], [29, 19], [51, 59], [33, 59], [37, 57], [32, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [23, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [8, 57, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172, 17, -60]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 13, -60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-19, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-19, 1, 0]] 
 ![![89, 0, 0], ![70, 1, 0], ![84, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-19, 1, 0], ![0, -19, 1], ![82, -4, -19]]]
  hmulB := by decide  
  f := ![![![1540, -81, 0], ![7209, 0, 0]], ![![1198, -63, 0], ![5608, 0, 0]], ![![1468, -77, 0], ![6872, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 89, 0], ![-84, 0, 89]], ![![-1, 1, 0], ![14, -19, 1], ![22, -4, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![9, 19, 1]] ![![89, 0, 0], ![-19, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1691, 89, 0]], ![![801, 1691, 89], ![-89, -356, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-19, 1, 0]]], ![![![9, 19, 1]], ![![-1, -4, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![26, 33, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![26, 33, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![26, 33, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![26, 33, 1], ![82, 22, 33], ![2706, -50, 22]]]
  hmulB := by decide  
  f := ![![![-25, -33, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -33, 97]], ![![0, 0, 1], ![-8, -11, 33], ![22, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [12, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 96], [0, 1]]
 g := ![![[83, 89], [53], [94], [70], [31], [71, 1]], ![[0, 8], [53], [94], [70], [31], [45, 96]]]
 h' := ![![[71, 96], [11, 34], [68, 76], [41, 26], [69, 19], [21, 82], [0, 1]], ![[0, 1], [0, 63], [32, 21], [44, 71], [60, 78], [23, 15], [71, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [88, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [12, 26, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-997, 738, 40]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -6, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-33, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-33, 1, 0]] 
 ![![97, 0, 0], ![64, 1, 0], ![75, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-33, 1, 0], ![0, -33, 1], ![82, -4, -33]]]
  hmulB := by decide  
  f := ![![![2179, -66, 0], ![6402, 0, 0]], ![![1420, -43, 0], ![4172, 0, 0]], ![![1695, -51, 0], ![4980, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 97, 0], ![-75, 0, 97]], ![![-1, 1, 0], ![21, -33, 1], ![29, -4, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![26, 33, 1]] ![![97, 0, 0], ![-33, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3201, 97, 0]], ![![2522, 3201, 97], ![-776, -1067, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-33, 1, 0]]], ![![![26, 33, 1]], ![![-8, -11, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![16, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![16, 1, 0]] 
 ![![101, 0, 0], ![16, 1, 0], ![47, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![16, 1, 0], ![0, 16, 1], ![82, -4, 16]]]
  hmulB := by decide  
  f := ![![![273, 17, 0], ![-1717, 0, 0]], ![![16, 1, 0], ![-100, 0, 0]], ![![115, 7, 0], ![-723, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 101, 0], ![-47, 0, 101]], ![![0, 1, 0], ![-3, 16, 1], ![-6, -4, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![31, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![31, 1, 0]] 
 ![![101, 0, 0], ![31, 1, 0], ![49, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![31, 1, 0], ![0, 31, 1], ![82, -4, 31]]]
  hmulB := by decide  
  f := ![![![1365, 44, 0], ![-4444, 0, 0]], ![![403, 13, 0], ![-1312, 0, 0]], ![![661, 21, 0], ![-2152, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 101, 0], ![-49, 0, 101]], ![![0, 1, 0], ![-10, 31, 1], ![-13, -4, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-47, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-47, 1, 0]] 
 ![![101, 0, 0], ![54, 1, 0], ![13, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-47, 1, 0], ![0, -47, 1], ![82, -4, -47]]]
  hmulB := by decide  
  f := ![![![2962, -63, 0], ![6363, 0, 0]], ![![1646, -35, 0], ![3536, 0, 0]], ![![398, -8, 0], ![855, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 101, 0], ![-13, 0, 101]], ![![-1, 1, 0], ![25, -47, 1], ![9, -4, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![16, 1, 0]] ![![101, 0, 0], ![31, 1, 0]]
  ![![101, 0, 0], ![-9, 47, 1]] where
 M := ![![![10201, 0, 0], ![3131, 101, 0]], ![![1616, 101, 0], ![496, 47, 1]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![31, 1, 0], ![0, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-9, 47, 1]] ![![101, 0, 0], ![-47, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4747, 101, 0]], ![![-909, 4747, 101], ![505, -2222, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-47, 1, 0]]], ![![![-9, 47, 1]], ![![5, -22, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-43, 46, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-43, 46, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![60, 46, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-43, 46, 1], ![82, -47, 46], ![3772, -102, -47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -46, 103]], ![![-1, 0, 1], ![-26, -21, 46], ![64, 20, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [94, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 102], [0, 1]]
 g := ![![[45, 34], [100, 34], [39, 76], [82], [68], [96, 1]], ![[13, 69], [68, 69], [22, 27], [82], [68], [89, 102]]]
 h' := ![![[96, 102], [76, 31], [42, 31], [49, 30], [49, 44], [40, 58], [0, 1]], ![[0, 1], [65, 72], [31, 72], [45, 73], [50, 59], [46, 45], [96, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [29, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [94, 7, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3578, -31, 118]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -53, 118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-46, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-46, 1, 0]] 
 ![![103, 0, 0], ![57, 1, 0], ![47, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-46, 1, 0], ![0, -46, 1], ![82, -4, -46]]]
  hmulB := by decide  
  f := ![![![3497, -76, 0], ![7828, 0, 0]], ![![1979, -43, 0], ![4430, 0, 0]], ![![1585, -34, 0], ![3548, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 103, 0], ![-47, 0, 103]], ![![-1, 1, 0], ![25, -46, 1], ![24, -4, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-43, 46, 1]] ![![103, 0, 0], ![-46, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4738, 103, 0]], ![![-4429, 4738, 103], ![2060, -2163, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-46, 1, 0]]], ![![![-43, 46, 1]], ![![20, -21, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![38, -26, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![38, -26, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![38, 81, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![38, -26, 1], ![82, 34, -26], ![-2132, 186, 34]]]
  hmulB := by decide  
  f := ![![![-37, 26, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -81, 107]], ![![0, -1, 1], ![10, 20, -26], ![-32, -24, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [58, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 106], [0, 1]]
 g := ![![[49, 1], [83, 89], [83], [49, 12], [14], [47, 1]], ![[96, 106], [93, 18], [83], [78, 95], [14], [94, 106]]]
 h' := ![![[47, 106], [1, 1], [70, 93], [47, 46], [77, 71], [56, 11], [0, 1]], ![[0, 1], [48, 106], [54, 14], [69, 61], [97, 36], [38, 96], [47, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [24, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [58, 60, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-373, 824, -221]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![75, 175, -221]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![26, 1, 0]] 
 ![![107, 0, 0], ![26, 1, 0], ![73, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![26, 1, 0], ![0, 26, 1], ![82, -4, 26]]]
  hmulB := by decide  
  f := ![![![1249, 48, 0], ![-5136, 0, 0]], ![![286, 11, 0], ![-1176, 0, 0]], ![![839, 32, 0], ![-3450, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 107, 0], ![-73, 0, 107]], ![![0, 1, 0], ![-7, 26, 1], ![-16, -4, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![38, -26, 1]] ![![107, 0, 0], ![26, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2782, 107, 0]], ![![4066, -2782, 107], ![1070, -642, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![26, 1, 0]]], ![![![38, -26, 1]], ![![10, -6, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![24, -42, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![24, -42, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![24, 67, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![24, -42, 1], ![82, 20, -42], ![-3444, 250, 20]]]
  hmulB := by decide  
  f := ![![![-23, 42, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -67, 109]], ![![0, -1, 1], ![10, 26, -42], ![-36, -10, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [82, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 108], [0, 1]]
 g := ![![[56, 4], [84], [28, 15], [90, 35], [25], [95, 1]], ![[0, 105], [84], [36, 94], [36, 74], [25], [81, 108]]]
 h' := ![![[95, 108], [28, 2], [102, 56], [32, 48], [6, 12], [58, 5], [0, 1]], ![[0, 1], [0, 107], [81, 53], [14, 61], [56, 97], [97, 104], [95, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [48, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [82, 14, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246, 60, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 11, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![42, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![42, 1, 0]] 
 ![![109, 0, 0], ![42, 1, 0], ![89, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![42, 1, 0], ![0, 42, 1], ![82, -4, 42]]]
  hmulB := by decide  
  f := ![![![463, 11, 0], ![-1199, 0, 0]], ![![126, 3, 0], ![-326, 0, 0]], ![![395, 9, 0], ![-1023, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 109, 0], ![-89, 0, 109]], ![![0, 1, 0], ![-17, 42, 1], ![-32, -4, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![24, -42, 1]] ![![109, 0, 0], ![42, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![4578, 109, 0]], ![![2616, -4578, 109], ![1090, -1744, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![42, 1, 0]]], ![![![24, -42, 1]], ![![10, -16, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [59, 50, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 89, 40], [16, 23, 73], [0, 1]]
 g := ![![[31, 26, 97], [98, 69], [55, 52], [64, 60], [78, 36, 25], [1]], ![[85, 44, 110, 84], [102, 77], [98, 106], [89, 109], [38, 23, 111, 54], [6, 79, 76, 42]], ![[10, 67, 77, 6], [96, 22], [48, 8], [29, 87], [29, 51, 2, 107], [53, 24, 96, 71]]]
 h' := ![![[92, 89, 40], [3, 73, 60], [19, 12, 42], [10, 9, 74], [31, 56, 88], [54, 63, 108], [0, 1]], ![[16, 23, 73], [86, 74, 6], [62, 41, 90], [104, 100, 28], [65, 61, 83], [103, 12, 32], [92, 89, 40]], ![[0, 1], [27, 79, 47], [43, 60, 94], [84, 4, 11], [10, 109, 55], [65, 38, 86], [16, 23, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 30], []]
 b := ![[], [95, 48, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [59, 50, 5, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![575509, 62263, 3277]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5093, 551, 29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀



lemma PB121I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 120 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 120 (by omega)

def PB121I2 : PrimesBelowBoundCertificateInterval O 79 120 121 where
  m := 8
  g := ![3, 2, 2, 3, 2, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB121I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
