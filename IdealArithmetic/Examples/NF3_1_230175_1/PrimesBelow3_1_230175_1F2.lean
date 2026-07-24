
import IdealArithmetic.Examples.NF3_1_230175_1.RI3_1_230175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, 8, 3]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![34, 8, 3]] 
 ![![83, 0, 0], ![0, 83, 0], ![39, 58, 1]] where
  M :=![![![34, 8, 3], ![315, 79, 40], ![840, 183, 79]]]
  hmulB := by decide  
  f := ![![![-13, -1, 1]], ![![105, 2, -5]], ![![66, 1, -3]]]
  g := ![![![-1, -2, 3], ![-15, -27, 40], ![-27, -53, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [34, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 82], [0, 1]]
 g := ![![[64, 75], [71, 78], [75], [27], [40, 75], [1]], ![[42, 8], [78, 5], [75], [27], [18, 8], [1]]]
 h' := ![![[65, 82], [76, 65], [54, 59], [23, 18], [51, 44], [49, 65], [0, 1]], ![[0, 1], [68, 18], [71, 24], [31, 65], [6, 39], [41, 18], [65, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [52, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [34, 18, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![244, 33, 2]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -1, 2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -1, 1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-13, -1, 1]] 
 ![![83, 0, 0], ![42, 1, 0], ![29, 0, 1]] where
  M :=![![![-13, -1, 1], ![105, 2, -5], ![-105, 6, 2]]]
  hmulB := by decide  
  f := ![![![34, 8, 3]], ![![21, 5, 2]], ![![22, 5, 2]]]
  g := ![![![0, -1, 1], ![2, 2, -5], ![-5, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![34, 8, 3]] ![![-13, -1, 1]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![22, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![22, 1, 0]] 
 ![![89, 0, 0], ![22, 1, 0], ![10, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![22, 1, 0], ![0, 22, 5], ![105, 15, 22]]]
  hmulB := by decide  
  f := ![![![1035, 47, 0], ![-4183, 0, 0]], ![![242, 11, 0], ![-978, 0, 0]], ![![98, 0, -1], ![-396, 18, 0]]]
  g := ![![![1, 0, 0], ![-22, 89, 0], ![-10, 0, 89]], ![![0, 1, 0], ![-6, 22, 5], ![-5, 15, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![24, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![24, 1, 0]] 
 ![![89, 0, 0], ![24, 1, 0], ![45, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![24, 1, 0], ![0, 24, 5], ![105, 15, 24]]]
  hmulB := by decide  
  f := ![![![529, 22, 0], ![-1958, 0, 0]], ![![120, 5, 0], ![-444, 0, 0]], ![![261, 6, -1], ![-966, 18, 0]]]
  g := ![![![1, 0, 0], ![-24, 89, 0], ![-45, 0, 89]], ![![0, 1, 0], ![-9, 24, 5], ![-15, 15, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![43, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![43, 1, 0]] 
 ![![89, 0, 0], ![43, 1, 0], ![4, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![43, 1, 0], ![0, 43, 5], ![105, 15, 43]]]
  hmulB := by decide  
  f := ![![![904, 21, 0], ![-1869, 0, 0]], ![![430, 10, 0], ![-889, 0, 0]], ![![30, -8, -1], ![-62, 18, 0]]]
  g := ![![![1, 0, 0], ![-43, 89, 0], ![-4, 0, 89]], ![![0, 1, 0], ![-21, 43, 5], ![-8, 15, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![22, 1, 0]] ![![89, 0, 0], ![24, 1, 0]]
  ![![89, 0, 0], ![-19, 27, 1]] where
 M := ![![![7921, 0, 0], ![2136, 89, 0]], ![![1958, 89, 0], ![528, 46, 5]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![24, 1, 0], ![0, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![7, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-19, 27, 1]] ![![89, 0, 0], ![43, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3827, 89, 0]], ![![-1691, 2403, 89], ![-712, 1157, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![43, 1, 0]]], ![![![-19, 27, 1]], ![![-8, 13, 2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![6, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![6, 1, 0]] 
 ![![97, 0, 0], ![6, 1, 0], ![51, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![6, 1, 0], ![0, 6, 5], ![105, 15, 6]]]
  hmulB := by decide  
  f := ![![![427, 71, 0], ![-6887, 0, 0]], ![![18, 3, 0], ![-290, 0, 0]], ![![225, 35, -2], ![-3629, 39, 0]]]
  g := ![![![1, 0, 0], ![-6, 97, 0], ![-51, 0, 97]], ![![0, 1, 0], ![-3, 6, 5], ![-3, 15, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![37, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![37, 1, 0]] 
 ![![97, 0, 0], ![37, 1, 0], ![56, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![37, 1, 0], ![0, 37, 5], ![105, 15, 37]]]
  hmulB := by decide  
  f := ![![![630, 17, 0], ![-1649, 0, 0]], ![![222, 6, 0], ![-581, 0, 0]], ![![366, -5, -2], ![-958, 39, 0]]]
  g := ![![![1, 0, 0], ![-37, 97, 0], ![-56, 0, 97]], ![![0, 1, 0], ![-17, 37, 5], ![-26, 15, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-43, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-43, 1, 0]] 
 ![![97, 0, 0], ![54, 1, 0], ![57, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-43, 1, 0], ![0, -43, 5], ![105, 15, -43]]]
  hmulB := by decide  
  f := ![![![4129, -96, 0], ![9312, 0, 0]], ![![2280, -53, 0], ![5142, 0, 0]], ![![2421, -39, -2], ![5460, 39, 0]]]
  g := ![![![1, 0, 0], ![-54, 97, 0], ![-57, 0, 97]], ![![-1, 1, 0], ![21, -43, 5], ![18, 15, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![6, 1, 0]] ![![97, 0, 0], ![37, 1, 0]]
  ![![97, 0, 0], ![25, 28, 1]] where
 M := ![![![9409, 0, 0], ![3589, 97, 0]], ![![582, 97, 0], ![222, 43, 5]]]
 hmul := by decide  
 g := ![![![![72, -28, -1], ![97, 0, 0]], ![![12, -27, -1], ![97, 0, 0]]], ![![![-19, -27, -1], ![97, 0, 0]], ![![1, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![25, 28, 1]] ![![97, 0, 0], ![-43, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4171, 97, 0]], ![![2425, 2716, 97], ![-970, -1164, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-43, 1, 0]]], ![![![25, 28, 1]], ![![-10, -12, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![19, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![19, 1, 0]] 
 ![![101, 0, 0], ![19, 1, 0], ![49, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![19, 1, 0], ![0, 19, 5], ![105, 15, 19]]]
  hmulB := by decide  
  f := ![![![267, 14, 0], ![-1414, 0, 0]], ![![19, 1, 0], ![-100, 0, 0]], ![![119, -9, -4], ![-630, 81, 0]]]
  g := ![![![1, 0, 0], ![-19, 101, 0], ![-49, 0, 101]], ![![0, 1, 0], ![-6, 19, 5], ![-11, 15, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-12, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-12, 1, 0]] 
 ![![101, 0, 0], ![89, 1, 0], ![52, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-12, 1, 0], ![0, -12, 5], ![105, 15, -12]]]
  hmulB := by decide  
  f := ![![![781, -65, 0], ![6565, 0, 0]], ![![697, -58, 0], ![5859, 0, 0]], ![![404, -24, -4], ![3396, 81, 0]]]
  g := ![![![1, 0, 0], ![-89, 101, 0], ![-52, 0, 101]], ![![-1, 1, 0], ![8, -12, 5], ![-6, 15, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -14, 8]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-41, -14, 8]] 
 ![![101, 0, 0], ![94, 1, 0], ![71, 0, 1]] where
  M :=![![![-41, -14, 8], ![840, 79, -70], ![-1470, -42, 79]]]
  hmulB := by decide  
  f := ![![![-3301, -770, -348]], ![![-3434, -801, -362]], ![![-3121, -728, -329]]]
  g := ![![![7, -14, 8], ![-16, 79, -70], ![-31, -42, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![19, 1, 0]] ![![101, 0, 0], ![-12, 1, 0]]
  ![![3301, 770, 348]] where
 M := ![![![10201, 0, 0], ![-1212, 101, 0]], ![![1919, 101, 0], ![-228, 7, 5]]]
 hmul := by decide  
 g := ![![![![4141, 1414, -808]], ![![-1332, -247, 166]]], ![![![-61, 187, -82]], ![![-78, -35, 19]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![3301, 770, 348]] ![![-41, -14, 8]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [78, 39, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 0, 97], [11, 102, 6], [0, 1]]
 g := ![![[36, 44, 16], [23, 77, 64], [74, 70, 1], [17, 32], [36, 50], [1]], ![[29, 67, 86, 19], [8, 38, 30, 7], [45, 61, 13, 38], [87, 81], [67, 82], [5, 64, 57, 93]], ![[61, 62, 56, 3], [3, 13, 47, 40], [27, 71, 0, 53], [77, 68], [92, 63], [20, 57, 41, 10]]]
 h' := ![![[76, 0, 97], [60, 14, 99], [99, 101, 8], [1, 43, 1], [83, 59, 49], [25, 64, 87], [0, 1]], ![[11, 102, 6], [85, 68, 23], [68, 70, 4], [1, 86, 50], [68, 94, 9], [12, 66, 44], [76, 0, 97]], ![[0, 1], [26, 21, 84], [41, 35, 91], [6, 77, 52], [48, 53, 45], [80, 76, 75], [11, 102, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 89], []]
 b := ![[], [20, 89, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [78, 39, 16, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46041, 8137, 5150]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-447, 79, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![22, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![22, 1, 0]] 
 ![![107, 0, 0], ![22, 1, 0], ![53, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![22, 1, 0], ![0, 22, 5], ![105, 15, 22]]]
  hmulB := by decide  
  f := ![![![1167, 53, 0], ![-5671, 0, 0]], ![![198, 9, 0], ![-962, 0, 0]], ![![569, 17, -2], ![-2765, 43, 0]]]
  g := ![![![1, 0, 0], ![-22, 107, 0], ![-53, 0, 107]], ![![0, 1, 0], ![-7, 22, 5], ![-13, 15, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 1, -2]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![38, 1, -2]] 
 ![![107, 0, 0], ![40, 1, 0], ![1, 0, 1]] where
  M :=![![![38, 1, -2], ![-210, 8, 5], ![105, -27, 8]]]
  hmulB := by decide  
  f := ![![![199, 46, 21]], ![![95, 22, 10]], ![![47, 11, 5]]]
  g := ![![![0, 1, -2], ![-5, 8, 5], ![11, -27, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![45, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![45, 1, 0]] 
 ![![107, 0, 0], ![45, 1, 0], ![23, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![45, 1, 0], ![0, 45, 5], ![105, 15, 45]]]
  hmulB := by decide  
  f := ![![![1621, 36, 0], ![-3852, 0, 0]], ![![675, 15, 0], ![-1604, 0, 0]], ![![319, -11, -2], ![-758, 43, 0]]]
  g := ![![![1, 0, 0], ![-45, 107, 0], ![-23, 0, 107]], ![![0, 1, 0], ![-20, 45, 5], ![-15, 15, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![22, 1, 0]] ![![38, 1, -2]]
  ![![107, 0, 0], ![-38, -9, 1]] where
 M := ![![![4066, 107, -214]], ![![626, 30, -39]]]
 hmul := by decide  
 g := ![![![![38, 1, -2], ![0, 0, 0]]], ![![![30, 6, -1], ![68, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-38, -9, 1]] ![![107, 0, 0], ![45, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4815, 107, 0]], ![![-4066, -963, 107], ![-1605, -428, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![45, 1, 0]]], ![![![-38, -9, 1]], ![![-15, -4, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-35, 43, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-35, 43, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![74, 43, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-35, 43, 1], ![105, -20, 215], ![4515, 666, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -43, 109]], ![![-1, 0, 1], ![-145, -85, 215], ![55, 14, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [84, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 108], [0, 1]]
 g := ![![[102, 61], [20], [61, 12], [91, 5], [5], [43, 1]], ![[0, 48], [20], [32, 97], [88, 104], [5], [86, 108]]]
 h' := ![![[43, 108], [65, 72], [108, 67], [95, 98], [23, 21], [94, 21], [0, 1]], ![[0, 1], [0, 37], [46, 42], [58, 11], [54, 88], [16, 88], [43, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [47, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [84, 66, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-254, -71, 82]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-58, -33, 82]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![3, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![3, 1, 0]] 
 ![![109, 0, 0], ![3, 1, 0], ![20, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![3, 1, 0], ![0, 3, 5], ![105, 15, 3]]]
  hmulB := by decide  
  f := ![![![208, 69, 0], ![-7521, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![38, 12, -1], ![-1374, 22, 0]]]
  g := ![![![1, 0, 0], ![-3, 109, 0], ![-20, 0, 109]], ![![0, 1, 0], ![-1, 3, 5], ![0, 15, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-35, 43, 1]] ![![109, 0, 0], ![3, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![327, 109, 0]], ![![-3815, 4687, 109], ![0, 109, 218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![3, 1, 0]]], ![![![-35, 43, 1]], ![![0, 1, 2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-42, -57, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-42, -57, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![71, 56, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-42, -57, 1], ![105, -27, -285], ![-5985, -834, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -56, 113]], ![![-1, -1, 1], ![180, 141, -285], ![-36, 6, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [50, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 112], [0, 1]]
 g := ![![[70, 52], [26], [22], [50], [54, 99], [3, 1]], ![[0, 61], [26], [22], [50], [12, 14], [6, 112]]]
 h' := ![![[3, 112], [4, 74], [93, 34], [17, 19], [12, 84], [76, 72], [0, 1]], ![[0, 1], [0, 39], [82, 79], [74, 94], [38, 29], [66, 41], [3, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [13, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [50, 110, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-469, 211, -196]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![119, 99, -196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-54, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-54, 1, 0]] 
 ![![113, 0, 0], ![59, 1, 0], ![27, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-54, 1, 0], ![0, -54, 5], ![105, 15, -54]]]
  hmulB := by decide  
  f := ![![![5725, -106, 0], ![11978, 0, 0]], ![![2971, -55, 0], ![6216, 0, 0]], ![![1431, 6, -3], ![2994, 68, 0]]]
  g := ![![![1, 0, 0], ![-59, 113, 0], ![-27, 0, 113]], ![![-1, 1, 0], ![27, -54, 5], ![6, 15, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-42, -57, 1]] ![![113, 0, 0], ![-54, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-6102, 113, 0]], ![![-4746, -6441, 113], ![2373, 3051, -339]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-54, 1, 0]]], ![![![-42, -57, 1]], ![![21, 27, -3]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [12, 89, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 31, 110], [66, 95, 17], [0, 1]]
 g := ![![[8, 24, 4], [112, 97, 100], [18, 122, 18], [104, 75, 107], [110, 57, 11], [1]], ![[14, 83, 93, 125], [43, 65, 47, 48], [28, 83, 25, 102], [93, 62, 3, 89], [67, 61, 33, 14], [37, 32, 23, 40]], ![[42, 45, 11, 76], [77, 120, 53, 103], [111, 49, 60, 122], [24, 68, 115, 82], [85, 60, 43, 60], [101, 6, 126, 87]]]
 h' := ![![[31, 31, 110], [53, 91, 125], [38, 85, 10], [22, 91, 79], [77, 84, 108], [115, 38, 97], [0, 1]], ![[66, 95, 17], [113, 82, 41], [95, 74, 13], [79, 77, 116], [10, 15, 69], [10, 98, 60], [31, 31, 110]], ![[0, 1], [10, 81, 88], [79, 95, 104], [44, 86, 59], [35, 28, 77], [26, 118, 97], [66, 95, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 17], []]
 b := ![[], [60, 93, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [12, 89, 30, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1143, -254, -254]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -2, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [86, 109, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 3, 102], [63, 127, 29], [0, 1]]
 g := ![![[43, 122, 39], [27, 74, 15], [111, 11], [10, 109], [52, 39], [33, 1], []], ![[39, 41, 88, 91], [114, 96, 105, 61], [33, 20], [55, 80], [85, 84], [23, 16], [69, 55]], ![[18, 28, 5, 130], [35, 114, 127, 6], [43, 46], [11, 112], [91, 125], [82, 9], [11, 55]]]
 h' := ![![[101, 3, 102], [36, 102, 63], [97, 21, 43], [39, 13, 81], [84, 7, 90], [44, 116, 63], [0, 0, 1], [0, 1]], ![[63, 127, 29], [129, 9, 65], [72, 10, 5], [91, 125, 85], [74, 102, 92], [110, 51, 52], [75, 14, 127], [101, 3, 102]], ![[0, 1], [18, 20, 3], [16, 100, 83], [96, 124, 96], [115, 22, 80], [122, 95, 16], [10, 117, 3], [63, 127, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 59], []]
 b := ![[], [113, 92, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [86, 109, 98, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4096239, 707138, 271563]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31269, 5398, 2073]
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



lemma PB136I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 135 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 135 (by omega)

def PB136I2 : PrimesBelowBoundCertificateInterval O 79 135 136 where
  m := 10
  g := ![2, 3, 3, 3, 1, 3, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB136I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![2248091]
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
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
  β := ![I83N1, I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I107N0, I107N1, I107N2, I109N1, I113N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
