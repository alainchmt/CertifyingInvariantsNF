
import IdealArithmetic.Examples.NF3_1_905324_3.RI3_1_905324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-36, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-36, 1, 0]] 
 ![![83, 0, 0], ![47, 1, 0], ![32, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-36, 1, 0], ![0, -36, 1], ![182, -14, -36]]]
  hmulB := by decide  
  f := ![![![1585, -44, 0], ![3652, 0, 0]], ![![901, -25, 0], ![2076, 0, 0]], ![![664, -18, 0], ![1530, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 83, 0], ![-32, 0, 83]], ![![-1, 1, 0], ![20, -36, 1], ![24, -14, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-32, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-32, 1, 0]] 
 ![![83, 0, 0], ![51, 1, 0], ![55, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-32, 1, 0], ![0, -32, 1], ![182, -14, -32]]]
  hmulB := by decide  
  f := ![![![673, -21, 0], ![1743, 0, 0]], ![![449, -14, 0], ![1163, 0, 0]], ![![493, -15, 0], ![1277, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 83, 0], ![-55, 0, 83]], ![![-1, 1, 0], ![19, -32, 1], ![32, -14, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-15, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-15, 1, 0]] 
 ![![83, 0, 0], ![68, 1, 0], ![24, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-15, 1, 0], ![0, -15, 1], ![182, -14, -15]]]
  hmulB := by decide  
  f := ![![![1141, -76, 0], ![6308, 0, 0]], ![![946, -63, 0], ![5230, 0, 0]], ![![348, -23, 0], ![1924, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 83, 0], ![-24, 0, 83]], ![![-1, 1, 0], ![12, -15, 1], ![18, -14, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-36, 1, 0]] ![![83, 0, 0], ![-32, 1, 0]]
  ![![83, 0, 0], ![-10, 15, 1]] where
 M := ![![![6889, 0, 0], ![-2656, 83, 0]], ![![-2988, 83, 0], ![1152, -68, 1]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![-22, -14, -1], ![83, 0, 0]]], ![![![-26, -14, -1], ![83, 0, 0]], ![![14, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-10, 15, 1]] ![![83, 0, 0], ![-15, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1245, 83, 0]], ![![-830, 1245, 83], ![332, -249, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-15, 1, 0]]], ![![![-10, 15, 1]], ![![4, -3, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![7, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![7, 1, 0]] 
 ![![89, 0, 0], ![7, 1, 0], ![40, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![7, 1, 0], ![0, 7, 1], ![182, -14, 7]]]
  hmulB := by decide  
  f := ![![![316, 45, 0], ![-4005, 0, 0]], ![![14, 2, 0], ![-177, 0, 0]], ![![134, 19, 0], ![-1698, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 89, 0], ![-40, 0, 89]], ![![0, 1, 0], ![-1, 7, 1], ![0, -14, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![37, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![37, 1, 0]] 
 ![![89, 0, 0], ![37, 1, 0], ![55, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![37, 1, 0], ![0, 37, 1], ![182, -14, 37]]]
  hmulB := by decide  
  f := ![![![1074, 29, 0], ![-2581, 0, 0]], ![![444, 12, 0], ![-1067, 0, 0]], ![![608, 16, 0], ![-1461, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 89, 0], ![-55, 0, 89]], ![![0, 1, 0], ![-16, 37, 1], ![-15, -14, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-44, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-44, 1, 0]] 
 ![![89, 0, 0], ![45, 1, 0], ![22, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-44, 1, 0], ![0, -44, 1], ![182, -14, -44]]]
  hmulB := by decide  
  f := ![![![3917, -89, 0], ![7921, 0, 0]], ![![2025, -46, 0], ![4095, 0, 0]], ![![990, -22, 0], ![2002, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 89, 0], ![-22, 0, 89]], ![![-1, 1, 0], ![22, -44, 1], ![20, -14, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![7, 1, 0]] ![![89, 0, 0], ![37, 1, 0]]
  ![![89, 0, 0], ![-8, 44, 1]] where
 M := ![![![7921, 0, 0], ![3293, 89, 0]], ![![623, 89, 0], ![259, 44, 1]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![37, 1, 0], ![0, 0, 0]]], ![![![7, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-8, 44, 1]] ![![89, 0, 0], ![-44, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3916, 89, 0]], ![![-712, 3916, 89], ![534, -1958, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-44, 1, 0]]], ![![![-8, 44, 1]], ![![6, -22, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-8, -47, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-8, -47, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![89, 50, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-8, -47, 1], ![182, -22, -47], ![-8554, 840, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-89, -50, 97]], ![![-1, -1, 1], ![45, 24, -47], ![-68, 20, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [68, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 96], [0, 1]]
 g := ![![[22, 31], [62], [54], [44], [35], [56, 1]], ![[12, 66], [62], [54], [44], [35], [15, 96]]]
 h' := ![![[56, 96], [83, 82], [15, 81], [96, 65], [88, 74], [72, 61], [0, 1]], ![[0, 1], [19, 15], [89, 16], [50, 32], [61, 23], [93, 36], [56, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [3, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [68, 41, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![432, 113, -54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 29, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![47, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![47, 1, 0]] 
 ![![97, 0, 0], ![47, 1, 0], ![22, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![47, 1, 0], ![0, 47, 1], ![182, -14, 47]]]
  hmulB := by decide  
  f := ![![![1411, 30, 0], ![-2910, 0, 0]], ![![611, 13, 0], ![-1260, 0, 0]], ![![258, 5, 0], ![-532, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 97, 0], ![-22, 0, 97]], ![![0, 1, 0], ![-23, 47, 1], ![-2, -14, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-8, -47, 1]] ![![97, 0, 0], ![47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4559, 97, 0]], ![![-776, -4559, 97], ![-194, -2231, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![47, 1, 0]]], ![![![-8, -47, 1]], ![![-2, -23, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-16, -24, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-16, -24, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![85, 77, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-16, -24, 1], ![182, -30, -24], ![-4368, 518, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -77, 101]], ![![-1, -1, 1], ![22, 18, -24], ![-18, 28, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [42, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 100], [0, 1]]
 g := ![![[78, 97], [68], [86, 43], [68], [19], [57, 1]], ![[52, 4], [68], [12, 58], [68], [19], [13, 100]]]
 h' := ![![[57, 100], [43, 20], [24, 88], [74, 12], [1, 88], [30, 76], [0, 1]], ![[0, 1], [72, 81], [91, 13], [51, 89], [68, 13], [19, 25], [57, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [13, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [42, 44, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2185, 1722, 4]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, 14, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![24, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![24, 1, 0]] 
 ![![101, 0, 0], ![24, 1, 0], ![30, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![24, 1, 0], ![0, 24, 1], ![182, -14, 24]]]
  hmulB := by decide  
  f := ![![![1201, 50, 0], ![-5050, 0, 0]], ![![264, 11, 0], ![-1110, 0, 0]], ![![342, 14, 0], ![-1438, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 101, 0], ![-30, 0, 101]], ![![0, 1, 0], ![-6, 24, 1], ![-2, -14, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-16, -24, 1]] ![![101, 0, 0], ![24, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2424, 101, 0]], ![![-1616, -2424, 101], ![-202, -606, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![24, 1, 0]]], ![![![-16, -24, 1]], ![![-2, -6, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![48, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![48, 1, 0]] 
 ![![103, 0, 0], ![48, 1, 0], ![65, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![48, 1, 0], ![0, 48, 1], ![182, -14, 48]]]
  hmulB := by decide  
  f := ![![![1441, 30, 0], ![-3090, 0, 0]], ![![624, 13, 0], ![-1338, 0, 0]], ![![887, 18, 0], ![-1902, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 103, 0], ![-65, 0, 103]], ![![0, 1, 0], ![-23, 48, 1], ![-22, -14, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-27, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-27, 1, 0]] 
 ![![103, 0, 0], ![76, 1, 0], ![95, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-27, 1, 0], ![0, -27, 1], ![182, -14, -27]]]
  hmulB := by decide  
  f := ![![![1513, -56, 0], ![5768, 0, 0]], ![![1108, -41, 0], ![4224, 0, 0]], ![![1385, -51, 0], ![5280, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 103, 0], ![-95, 0, 103]], ![![-1, 1, 0], ![19, -27, 1], ![37, -14, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-21, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-21, 1, 0]] 
 ![![103, 0, 0], ![82, 1, 0], ![74, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-21, 1, 0], ![0, -21, 1], ![182, -14, -21]]]
  hmulB := by decide  
  f := ![![![1387, -66, 0], ![6798, 0, 0]], ![![1072, -51, 0], ![5254, 0, 0]], ![![992, -47, 0], ![4862, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 103, 0], ![-74, 0, 103]], ![![-1, 1, 0], ![16, -21, 1], ![28, -14, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![48, 1, 0]] ![![103, 0, 0], ![-27, 1, 0]]
  ![![103, 0, 0], ![43, 21, 1]] where
 M := ![![![10609, 0, 0], ![-2781, 103, 0]], ![![4944, 103, 0], ![-1296, 21, 1]]]
 hmul := by decide  
 g := ![![![![60, -21, -1], ![103, 0, 0]], ![![-27, 1, 0], ![0, 0, 0]]], ![![![5, -20, -1], ![103, 0, 0]], ![![-13, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![43, 21, 1]] ![![103, 0, 0], ![-21, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2163, 103, 0]], ![![4429, 2163, 103], ![-721, -412, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-21, 1, 0]]], ![![![43, 21, 1]], ![![-7, -4, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![21, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![21, 1, 0]] 
 ![![107, 0, 0], ![21, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![21, 1, 0], ![0, 21, 1], ![182, -14, 21]]]
  hmulB := by decide  
  f := ![![![862, 41, 0], ![-4387, 0, 0]], ![![168, 8, 0], ![-855, 0, 0]], ![![740, 35, 0], ![-3766, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 107, 0], ![-94, 0, 107]], ![![0, 1, 0], ![-5, 21, 1], ![-14, -14, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![25, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![25, 1, 0]] 
 ![![107, 0, 0], ![25, 1, 0], ![17, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![25, 1, 0], ![0, 25, 1], ![182, -14, 25]]]
  hmulB := by decide  
  f := ![![![651, 26, 0], ![-2782, 0, 0]], ![![125, 5, 0], ![-534, 0, 0]], ![![81, 3, 0], ![-346, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 107, 0], ![-17, 0, 107]], ![![0, 1, 0], ![-6, 25, 1], ![1, -14, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-46, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-46, 1, 0]] 
 ![![107, 0, 0], ![61, 1, 0], ![24, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-46, 1, 0], ![0, -46, 1], ![182, -14, -46]]]
  hmulB := by decide  
  f := ![![![599, -13, 0], ![1391, 0, 0]], ![![369, -8, 0], ![857, 0, 0]], ![![204, -4, 0], ![474, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 107, 0], ![-24, 0, 107]], ![![-1, 1, 0], ![26, -46, 1], ![20, -14, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![21, 1, 0]] ![![107, 0, 0], ![25, 1, 0]]
  ![![107, 0, 0], ![-10, 46, 1]] where
 M := ![![![11449, 0, 0], ![2675, 107, 0]], ![![2247, 107, 0], ![525, 46, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-10, 46, 1]] ![![107, 0, 0], ![-46, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4922, 107, 0]], ![![-1070, 4922, 107], ![642, -2140, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-46, 1, 0]]], ![![![-10, 46, 1]], ![![6, -20, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![18, -2, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![18, -2, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![18, 107, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![18, -2, 1], ![182, 4, -2], ![-364, 210, 4]]]
  hmulB := by decide  
  f := ![![![-17, 2, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -107, 109]], ![![0, -1, 1], ![2, 2, -2], ![-4, -2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [46, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 108], [0, 1]]
 g := ![![[21, 64], [104], [68, 12], [88, 64], [104], [15, 1]], ![[0, 45], [104], [30, 97], [67, 45], [104], [30, 108]]]
 h' := ![![[15, 108], [11, 101], [33, 39], [94, 11], [0, 8], [73, 70], [0, 1]], ![[0, 1], [0, 8], [73, 70], [41, 98], [11, 101], [33, 39], [15, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [11, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [46, 94, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2238, 176, 21]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -19, 21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![2, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![2, 1, 0]] 
 ![![109, 0, 0], ![2, 1, 0], ![105, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![2, 1, 0], ![0, 2, 1], ![182, -14, 2]]]
  hmulB := by decide  
  f := ![![![107, 53, 0], ![-5777, 0, 0]], ![![-2, -1, 0], ![110, 0, 0]], ![![103, 51, 0], ![-5561, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 109, 0], ![-105, 0, 109]], ![![0, 1, 0], ![-1, 2, 1], ![0, -14, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![18, -2, 1]] ![![109, 0, 0], ![2, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![218, 109, 0]], ![![1962, -218, 109], ![218, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![2, 1, 0]]], ![![![18, -2, 1]], ![![2, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![50, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![50, 1, 0]] 
 ![![113, 0, 0], ![50, 1, 0], ![99, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![50, 1, 0], ![0, 50, 1], ![182, -14, 50]]]
  hmulB := by decide  
  f := ![![![1701, 34, 0], ![-3842, 0, 0]], ![![750, 15, 0], ![-1694, 0, 0]], ![![1423, 28, 0], ![-3214, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 113, 0], ![-99, 0, 113]], ![![0, 1, 0], ![-23, 50, 1], ![-36, -14, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-47, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-47, 1, 0]] 
 ![![113, 0, 0], ![66, 1, 0], ![51, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-47, 1, 0], ![0, -47, 1], ![182, -14, -47]]]
  hmulB := by decide  
  f := ![![![5124, -109, 0], ![12317, 0, 0]], ![![3056, -65, 0], ![7346, 0, 0]], ![![2370, -50, 0], ![5697, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 113, 0], ![-51, 0, 113]], ![![-1, 1, 0], ![27, -47, 1], ![31, -14, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![113, 0, 0], ![110, 1, 0], ![104, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![182, -14, -3]]]
  hmulB := by decide  
  f := ![![![23, 3, 1]], ![![24, 3, 1]], ![![26, 4, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![18, -14, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![50, 1, 0]] ![![113, 0, 0], ![-47, 1, 0]]
  ![![23, 3, 1]] where
 M := ![![![12769, 0, 0], ![-5311, 113, 0]], ![![5650, 113, 0], ![-2350, 3, 1]]]
 hmul := by decide  
 g := ![![![![-339, 113, 0]], ![![141, -50, 1]]], ![![![-150, 47, 1]], ![![64, -21, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![23, 3, 1]] ![![-3, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 3, -2]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![31, 3, -2]] 
 ![![127, 0, 0], ![0, 127, 0], ![48, 62, 1]] where
  M :=![![![31, 3, -2], ![-364, 59, 3], ![546, -406, 59]]]
  hmulB := by decide  
  f := ![![![-37, -5, -1]], ![![-182, -23, -5]], ![![-110, -14, -3]]]
  g := ![![![1, 1, -2], ![-4, -1, 3], ![-18, -32, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [119, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 126], [0, 1]]
 g := ![![[111, 38], [45, 21], [34, 26], [29, 18], [29, 81], [126, 1]], ![[73, 89], [24, 106], [8, 101], [11, 109], [75, 46], [125, 126]]]
 h' := ![![[126, 126], [106, 66], [18, 23], [105, 91], [105, 48], [119, 9], [0, 1]], ![[0, 1], [40, 61], [122, 104], [14, 36], [57, 79], [110, 118], [126, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [50, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [119, 1, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-971, 1725, -134]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 79, -134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -5, -1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-37, -5, -1]] 
 ![![127, 0, 0], ![65, 1, 0], ![93, 0, 1]] where
  M :=![![![-37, -5, -1], ![-182, -23, -5], ![-910, -112, -23]]]
  hmulB := by decide  
  f := ![![![31, 3, -2]], ![![13, 2, -1]], ![![27, -1, -1]]]
  g := ![![![3, -5, -1], ![14, -23, -5], ![67, -112, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![31, 3, -2]] ![![-37, -5, -1]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-18, 19, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-18, 19, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![113, 19, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-18, 19, 1], ![182, -32, 19], ![3458, -84, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -19, 131]], ![![-1, 0, 1], ![-15, -3, 19], ![54, 4, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [124, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 130], [0, 1]]
 g := ![![[77, 41], [4, 129], [102], [100], [77], [94], [1]], ![[37, 90], [105, 2], [102], [100], [77], [94], [1]]]
 h' := ![![[15, 130], [28, 98], [107, 103], [21, 44], [99, 121], [52, 48], [7, 15], [0, 1]], ![[0, 1], [57, 33], [80, 28], [26, 87], [80, 10], [117, 83], [101, 116], [15, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [42, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [124, 116, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![488, 38, -129]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![115, 19, -129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-19, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-19, 1, 0]] 
 ![![131, 0, 0], ![112, 1, 0], ![32, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-19, 1, 0], ![0, -19, 1], ![182, -14, -19]]]
  hmulB := by decide  
  f := ![![![1502, -79, 0], ![10349, 0, 0]], ![![1274, -67, 0], ![8778, 0, 0]], ![![364, -19, 0], ![2508, 1, 0]]]
  g := ![![![1, 0, 0], ![-112, 131, 0], ![-32, 0, 131]], ![![-1, 1, 0], ![16, -19, 1], ![18, -14, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-18, 19, 1]] ![![131, 0, 0], ![-19, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-2489, 131, 0]], ![![-2358, 2489, 131], ![524, -393, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-19, 1, 0]]], ![![![-18, 19, 1]], ![![4, -3, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [67, 29, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 92, 25], [60, 44, 112], [0, 1]]
 g := ![![[126, 42, 77], [130, 30], [114, 78], [114, 47, 74], [88, 112], [112, 1], []], ![[39, 116, 94, 133], [79, 49], [130, 7], [47, 0, 83, 123], [88, 105], [79, 18], [72, 77]], ![[54, 55, 106, 129], [20, 59], [120, 50], [30, 51, 26, 11], [63, 73], [30, 107], [122, 77]]]
 h' := ![![[52, 92, 25], [126, 64, 25], [94, 34, 21], [34, 130, 107], [134, 52, 38], [31, 110, 48], [0, 0, 1], [0, 1]], ![[60, 44, 112], [48, 71, 97], [86, 83, 130], [113, 7, 12], [94, 96, 95], [28, 9, 67], [72, 129, 44], [52, 92, 25]], ![[0, 1], [38, 2, 15], [62, 20, 123], [108, 0, 18], [7, 126, 4], [114, 18, 22], [84, 8, 92], [60, 44, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 47], []]
 b := ![[], [51, 80, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [67, 29, 25, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1329996, 98914, 5206]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9708, 722, 38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB270I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB270I2 : PrimesBelowBoundCertificateInterval O 79 137 270 where
  m := 11
  g := ![3, 3, 2, 2, 3, 3, 2, 3, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB270I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![83, 83, 83]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![2571353]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N0, I83N1, I83N2, I89N0, I89N1, I89N2, I97N1, I101N1, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I109N1, I113N0, I113N1, I113N2, I127N1, I131N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N0, I89N1, I89N2], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [I109N1], [I113N0, I113N1, I113N2], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
